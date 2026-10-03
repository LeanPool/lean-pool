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

@[expose]
noncomputable def nb090_alpha_dummy_750 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_751 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_709 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_752 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_753 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_700 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_754 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_700 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_755 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_756 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_757 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_753 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_758 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_759 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_760 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_761 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_762 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_763 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_764 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_765 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
          (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_766 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
          (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
          (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_767 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_768 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_769 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_770 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_771 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_760 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_772 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_773 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_761 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_774 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_775 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
            (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A)
          (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
              (Class.cv (nb090_alpha_dummy_042 A)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_776 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
            (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h)
          (syn_wrex (nb090_alpha_dummy_702 v u h)
            (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_777 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_778 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_779 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
          (Class.cv (nb090_alpha_dummy_777 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_780 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
          (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_781 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A))
              (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_782 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A))
              (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_783 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_778 v u h)
            (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
              (Class.cv (nb090_alpha_dummy_778 v u h))))
          (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_784 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_778 v u h)
            (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
              (Class.cv (nb090_alpha_dummy_778 v u h))))
          (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_785 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_777 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_786 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_777 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_787 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_788 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_789 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_790 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h)
            (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_791 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_785 A)
          (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_785 A)
          (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_792 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_787 v u h)
          (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_787 v u h)
          (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_793 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_786 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_794 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_786 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_795 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_796 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_797 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_793 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_798 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_799 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_800 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_801 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_802 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_803 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_804 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_805 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
          (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_806 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
          (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
          (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_807 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_808 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_809 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_810 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_811 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_800 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_812 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_813 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_801 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_814 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_815 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_785 A)
          (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A)
          (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_816 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_787 v u h)
          (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h)
          (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_817 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_818 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_819 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_820 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_821 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_779 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_822 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_823 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_824 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_825 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_826 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_827 (A : Class) : Var :=
  (freshVar (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_828 (v : Var) : Var :=
  (freshVar (((syn_c1st)).fv ∪ ((Class.cv v)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_829 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
          (Class.cv (nb090_alpha_dummy_827 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_830 (v : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪
      ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_831 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_827 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
              (Class.cv (nb090_alpha_dummy_827 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_832 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_827 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
              (Class.cv (nb090_alpha_dummy_827 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_833 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_828 v)
            (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
          (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_834 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_828 v)
            (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
          (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_835 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_827 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_836 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_827 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_837 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_838 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_839 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_840 (v : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_841 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_835 A)
          (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_835 A)
          (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_842 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_837 v)
          (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
              (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
              (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_843 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_836 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_844 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_836 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_845 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_838 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_846 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_838 v))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_847 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_843 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_848 (v : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_845 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_849 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_850 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_851 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_852 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_853 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_854 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_855 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
          (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_856 (v : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
          (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_857 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_858 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_859 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_860 (v : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_861 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_850 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_862 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_853 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_863 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_851 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_864 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_854 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_865 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_835 A)
          (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A)
          (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_866 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_837 v)
          (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v)
          (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_867 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_868 (v : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_869 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_870 (v : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_871 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_829 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_872 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_830 v))).fv) 0)

theorem nb090_fresh_000 (A : Class) :
    (nb090_alpha_dummy_011 A) ∉
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv)
      0

theorem nb090_fresh_001 (A : Class) :
    (nb090_alpha_dummy_035 A) ∉
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_002 (v : Var) (u : Var) :
    (nb090_alpha_dummy_012 v u) ∉
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv)
      0

theorem nb090_fresh_003 (v : Var) (u : Var) :
    (nb090_alpha_dummy_036 v u) ∉
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_004 (A : Class) :
    (nb090_alpha_dummy_063 A) ∉
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_063] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv)
      0

theorem nb090_fresh_005 (A : Class) :
    (nb090_alpha_dummy_087 A) ∉
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_006 (h : Var) :
    (nb090_alpha_dummy_064 h) ∉
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv)
      0

theorem nb090_fresh_007 (h : Var) :
    (nb090_alpha_dummy_088 h) ∉
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_008 (A : Class) :
    (nb090_alpha_dummy_099 A) ∉
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_099] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv)
      0

theorem nb090_fresh_009 (A : Class) :
    (nb090_alpha_dummy_123 A) ∉
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_123] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_010 (h : Var) :
    (nb090_alpha_dummy_100 h) ∉
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv)
      0

theorem nb090_fresh_011 (h : Var) :
    (nb090_alpha_dummy_124 h) ∉
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_124] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_012 (A : Class) :
    (nb090_alpha_dummy_141 A) ∉
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_141] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv)
      0

theorem nb090_fresh_013 (A : Class) :
    (nb090_alpha_dummy_165 A) ∉
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_165] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_014 (h : Var) :
    (nb090_alpha_dummy_142 h) ∉
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_142] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv)
      0

theorem nb090_fresh_015 (h : Var) :
    (nb090_alpha_dummy_166 h) ∉
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_166] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_016 (A : Class) :
    (nb090_alpha_dummy_201 A) ∉
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_201] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_017 (A : Class) :
    (nb090_alpha_dummy_177 A) ∉
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_177] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv)
      0

theorem nb090_fresh_018 (h : Var) :
    (nb090_alpha_dummy_202 h) ∉
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_202] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_019 (h : Var) :
    (nb090_alpha_dummy_178 h) ∉
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_178] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv)
      0

theorem nb090_fresh_020 (A : Class) :
    (nb090_alpha_dummy_237 A) ∉
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_237] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_021 (A : Class) :
    (nb090_alpha_dummy_213 A) ∉
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_213] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv)
      0

theorem nb090_fresh_022 (h : Var) :
    (nb090_alpha_dummy_238 h) ∉
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_238] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_023 (h : Var) :
    (nb090_alpha_dummy_214 h) ∉
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_214] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv)
      0

theorem nb090_fresh_024 (A : Class) :
    (nb090_alpha_dummy_277 A) ∉
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_277] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_025 (A : Class) :
    (nb090_alpha_dummy_253 A) ∉
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_253] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv)
      0

theorem nb090_fresh_026 (h : Var) :
    (nb090_alpha_dummy_278 h) ∉
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_278] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv)
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
    (nb090_alpha_dummy_254 h) ∉
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_254] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv)
      0

theorem nb090_fresh_028 (A : Class) :
    (nb090_alpha_dummy_287 A) ∉
      (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_287] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv)
      0

theorem nb090_fresh_029 (A : Class) :
    (nb090_alpha_dummy_288 A) ∉
      (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_288] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv)
      1

theorem nb090_distinct_030 (A : Class) :
    (nb090_alpha_dummy_287 A) ≠ (nb090_alpha_dummy_288 A) := by
  simpa only [nb090_alpha_dummy_287, nb090_alpha_dummy_288] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_031 (u : Var) :
    (nb090_alpha_dummy_289 u) ∉
      (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_289] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv)
      0

theorem nb090_fresh_032 (u : Var) :
    (nb090_alpha_dummy_290 u) ∉
      (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_290] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv)
      1

theorem nb090_distinct_033 (u : Var) :
    (nb090_alpha_dummy_289 u) ≠ (nb090_alpha_dummy_290 u) := by
  simpa only [nb090_alpha_dummy_289, nb090_alpha_dummy_290] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_034 (A : Class) :
    (nb090_alpha_dummy_297 A) ∉
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_297] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv)
      0

theorem nb090_fresh_035 (A : Class) :
    (nb090_alpha_dummy_321 A) ∉
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_321] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_036 (u : Var) :
    (nb090_alpha_dummy_322 u) ∉
      (((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_322] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_037 (u : Var) :
    (nb090_alpha_dummy_298 u) ∉
      (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_298] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv)
      0

theorem nb090_fresh_038 (A : Class) :
    (nb090_alpha_dummy_367 A) ∉
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_367] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_039 (A : Class) :
    (nb090_alpha_dummy_343 A) ∉
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_343] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv)
      0

theorem nb090_fresh_040 (h : Var) :
    (nb090_alpha_dummy_368 h) ∉
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_368] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_041 (h : Var) :
    (nb090_alpha_dummy_344 h) ∉
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_344] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv)
      0

theorem nb090_fresh_042 (A : Class) :
    (nb090_alpha_dummy_377 A) ∉
      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_377] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv)
      0

theorem nb090_fresh_043 (A : Class) :
    (nb090_alpha_dummy_378 A) ∉
      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_378] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv)
      1

theorem nb090_distinct_044 (A : Class) :
    (nb090_alpha_dummy_377 A) ≠ (nb090_alpha_dummy_378 A) := by
  simpa only [nb090_alpha_dummy_377, nb090_alpha_dummy_378] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_045 (v : Var) :
    (nb090_alpha_dummy_379 v) ∉
      (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_379] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv)
      0

theorem nb090_fresh_046 (v : Var) :
    (nb090_alpha_dummy_380 v) ∉
      (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_380] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv)
      1

theorem nb090_distinct_047 (v : Var) :
    (nb090_alpha_dummy_379 v) ≠ (nb090_alpha_dummy_380 v) := by
  simpa only [nb090_alpha_dummy_379, nb090_alpha_dummy_380] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_048 (A : Class) :
    (nb090_alpha_dummy_387 A) ∉
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_387] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv)
      0

theorem nb090_fresh_049 (A : Class) :
    (nb090_alpha_dummy_411 A) ∉
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_411] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_050 (v : Var) :
    (nb090_alpha_dummy_412 v) ∉
      (((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_412] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_051 (v : Var) :
    (nb090_alpha_dummy_388 v) ∉
      (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_388] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv)
      0

theorem nb090_fresh_052 (A : Class) :
    (nb090_alpha_dummy_437 A) ∉
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_437] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv)
      0

theorem nb090_fresh_053 (A : Class) :
    (nb090_alpha_dummy_461 A) ∉
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_461] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_054 (h : Var) :
    (nb090_alpha_dummy_438 h) ∉
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_438] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv)
      0

theorem nb090_fresh_055 (h : Var) :
    (nb090_alpha_dummy_462 h) ∉
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_462] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_056 (A : Class) :
    (nb090_alpha_dummy_473 A) ∉
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_473] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv)
      0

theorem nb090_fresh_057 (A : Class) :
    (nb090_alpha_dummy_497 A) ∉
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_497] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_058 (h : Var) :
    (nb090_alpha_dummy_474 h) ∉
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_474] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv)
      0

theorem nb090_fresh_059 (h : Var) :
    (nb090_alpha_dummy_498 h) ∉
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_498] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_060 (A : Class) :
    (nb090_alpha_dummy_515 A) ∉
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_515] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv)
      0

theorem nb090_fresh_061 (A : Class) :
    (nb090_alpha_dummy_539 A) ∉
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_539] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_062 (h : Var) :
    (nb090_alpha_dummy_516 h) ∉
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_516] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv)
      0

theorem nb090_fresh_063 (h : Var) :
    (nb090_alpha_dummy_540 h) ∉
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_540] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_064 (A : Class) :
    (nb090_alpha_dummy_575 A) ∉
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_575] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_065 (A : Class) :
    (nb090_alpha_dummy_551 A) ∉
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_551] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv)
      0

theorem nb090_fresh_066 (h : Var) :
    (nb090_alpha_dummy_576 h) ∉
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_576] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_067 (h : Var) :
    (nb090_alpha_dummy_552 h) ∉
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_552] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv)
      0

theorem nb090_fresh_068 (A : Class) :
    (nb090_alpha_dummy_611 A) ∉
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_611] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_069 (A : Class) :
    (nb090_alpha_dummy_587 A) ∉
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_587] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv)
      0

theorem nb090_fresh_070 (h : Var) :
    (nb090_alpha_dummy_612 h) ∉
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_612] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_071 (h : Var) :
    (nb090_alpha_dummy_588 h) ∉
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_588] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv)
      0

theorem nb090_fresh_072 (A : Class) :
    (nb090_alpha_dummy_623 A) ∉
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_623] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv)
      0

theorem nb090_fresh_073 (A : Class) :
    (nb090_alpha_dummy_647 A) ∉
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_647] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_074 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_624 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_624] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv)
      0

theorem nb090_fresh_075 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_648 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h)
            (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_648] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h)
            (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_076 (A : Class) :
    (nb090_alpha_dummy_657 A) ∉
      (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_657] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv)
      0

theorem nb090_fresh_077 (A : Class) :
    (nb090_alpha_dummy_658 A) ∉
      (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_658] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv)
      1

theorem nb090_distinct_078 (A : Class) :
    (nb090_alpha_dummy_657 A) ≠ (nb090_alpha_dummy_658 A) := by
  simpa only [nb090_alpha_dummy_657, nb090_alpha_dummy_658] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_079 (u : Var) :
    (nb090_alpha_dummy_659 u) ∉
      (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_659] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv)
      0

theorem nb090_fresh_080 (u : Var) :
    (nb090_alpha_dummy_660 u) ∉
      (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_660] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv)
      1

theorem nb090_distinct_081 (u : Var) :
    (nb090_alpha_dummy_659 u) ≠ (nb090_alpha_dummy_660 u) := by
  simpa only [nb090_alpha_dummy_659, nb090_alpha_dummy_660] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_082 (A : Class) :
    (nb090_alpha_dummy_667 A) ∉
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_667] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv)
      0

theorem nb090_fresh_083 (A : Class) :
    (nb090_alpha_dummy_691 A) ∉
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_691] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_084 (u : Var) :
    (nb090_alpha_dummy_692 u) ∉
      (((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_692] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_085 (u : Var) :
    (nb090_alpha_dummy_668 u) ∉
      (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_668] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv)
      0

theorem nb090_fresh_086 (A : Class) :
    (nb090_alpha_dummy_705 A) ∉
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_705] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv)
      0

theorem nb090_fresh_087 (A : Class) :
    (nb090_alpha_dummy_775 A) ∉
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A)
            (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_775] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A)
            (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_088 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_706 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_706] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv)
      0

theorem nb090_fresh_089 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_776 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h)
            (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_776] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h)
            (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_090 (A : Class) :
    (nb090_alpha_dummy_711 A) ∉
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_711] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv)
      0

theorem nb090_fresh_091 (A : Class) :
    (nb090_alpha_dummy_712 A) ∉
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_712] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv)
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
    (nb090_alpha_dummy_711 A) ≠ (nb090_alpha_dummy_712 A) := by
  simpa only [nb090_alpha_dummy_711, nb090_alpha_dummy_712] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
                (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_093 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_713 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_713] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv)
      0

theorem nb090_fresh_094 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_714 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_714] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv)
      1

theorem nb090_distinct_095 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_713 v u h) ≠ (nb090_alpha_dummy_714 v u h) := by
  simpa only [nb090_alpha_dummy_713, nb090_alpha_dummy_714] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_096 (A : Class) :
    (nb090_alpha_dummy_721 A) ∉
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_721] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv)
      0

theorem nb090_fresh_097 (A : Class) :
    (nb090_alpha_dummy_745 A) ∉
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_745] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_098 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_722 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_722] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv)
      0

theorem nb090_fresh_099 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_746 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h)
            (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_746] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h)
            (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_100 (A : Class) :
    (nb090_alpha_dummy_781 A) ∉
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_781] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv)
      0

theorem nb090_fresh_101 (A : Class) :
    (nb090_alpha_dummy_782 A) ∉
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_782] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv)
      1

theorem nb090_distinct_102 (A : Class) :
    (nb090_alpha_dummy_781 A) ≠ (nb090_alpha_dummy_782 A) := by
  simpa only [nb090_alpha_dummy_781, nb090_alpha_dummy_782] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A))
                (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_103 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_783 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_783] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv)
      0

theorem nb090_fresh_104 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_784 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_784] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv)
      1

theorem nb090_distinct_105 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_783 v u h) ≠ (nb090_alpha_dummy_784 v u h) := by
  simpa only [nb090_alpha_dummy_783, nb090_alpha_dummy_784] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_106 (A : Class) :
    (nb090_alpha_dummy_791 A) ∉
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_791] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv)
      0

theorem nb090_fresh_107 (A : Class) :
    (nb090_alpha_dummy_815 A) ∉
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_815] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_108 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_792 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_792] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv)
      0

theorem nb090_fresh_109 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_816 v u h) ∉
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h)
            (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_816] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h)
            (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_110 (A : Class) :
    (nb090_alpha_dummy_831 A) ∉
      (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_831] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv)
      0

theorem nb090_fresh_111 (A : Class) :
    (nb090_alpha_dummy_832 A) ∉
      (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_832] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv)
      1

theorem nb090_distinct_112 (A : Class) :
    (nb090_alpha_dummy_831 A) ≠ (nb090_alpha_dummy_832 A) := by
  simpa only [nb090_alpha_dummy_831, nb090_alpha_dummy_832] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_113 (v : Var) :
    (nb090_alpha_dummy_833 v) ∉
      (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_833] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv)
      0

theorem nb090_fresh_114 (v : Var) :
    (nb090_alpha_dummy_834 v) ∉
      (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_834] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv)
      1

theorem nb090_distinct_115 (v : Var) :
    (nb090_alpha_dummy_833 v) ≠ (nb090_alpha_dummy_834 v) := by
  simpa only [nb090_alpha_dummy_833, nb090_alpha_dummy_834] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_116 (A : Class) :
    (nb090_alpha_dummy_841 A) ∉
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_841] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv)
      0

theorem nb090_fresh_117 (A : Class) :
    (nb090_alpha_dummy_865 A) ∉
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_865] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_118 (v : Var) :
    (nb090_alpha_dummy_866 v) ∉
      (((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_866] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb090_fresh_119 (v : Var) :
    (nb090_alpha_dummy_842 v) ∉
      (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) :=
  by
  simpa only [nb090_alpha_dummy_842] using
    freshVar_not_mem
      (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv)
      0

theorem nb090_fresh_120 (A : Class) :
    (nb090_alpha_dummy_129 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv) := by
  simpa only [nb090_alpha_dummy_129] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv) 0

theorem nb090_fresh_121 (A : Class) :
    (nb090_alpha_dummy_130 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv) := by
  simpa only [nb090_alpha_dummy_130] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv) 1

theorem nb090_distinct_122 (A : Class) :
    (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_130 A) := by
  simpa only [nb090_alpha_dummy_129, nb090_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_123 (A : Class) :
    (nb090_alpha_dummy_707 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_707] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv)
      0

theorem nb090_fresh_124 (A : Class) :
    (nb090_alpha_dummy_777 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_777] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv)
      0

theorem nb090_fresh_125 (A : Class) :
    (nb090_alpha_dummy_049 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
      0

theorem nb090_fresh_126 (A : Class) :
    (nb090_alpha_dummy_050 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
      1

theorem nb090_fresh_127 (A : Class) :
    (nb090_alpha_dummy_051 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
      2

theorem nb090_distinct_128 (A : Class) :
    (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_050 A) := by
  simpa only [nb090_alpha_dummy_049, nb090_alpha_dummy_050] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_129 (A : Class) :
    (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_051 A) := by
  simpa only [nb090_alpha_dummy_049, nb090_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_130 (A : Class) :
    (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_051 A) := by
  simpa only [nb090_alpha_dummy_050, nb090_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
        ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_131 (A : Class) :
    (nb090_alpha_dummy_041 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
      0

theorem nb090_fresh_132 (A : Class) :
    (nb090_alpha_dummy_042 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  simpa only [nb090_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
      1

theorem nb090_distinct_133 (A : Class) :
    (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_042 A) := by
  simpa only [nb090_alpha_dummy_041, nb090_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_134 (A : Class) :
    (nb090_alpha_dummy_333 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb090_alpha_dummy_333] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_135 (A : Class) :
    (nb090_alpha_dummy_334 A) ∉
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb090_alpha_dummy_334] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_136 (A : Class) :
    (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_334 A) := by
  simpa only [nb090_alpha_dummy_333, nb090_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_fresh_137 (A : Class) :
    (nb090_alpha_dummy_005 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv)
      0

theorem nb090_fresh_138 (A : Class) :
    (nb090_alpha_dummy_006 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv)
      1

theorem nb090_distinct_139 (A : Class) :
    (nb090_alpha_dummy_005 A) ≠ (nb090_alpha_dummy_006 A) := by
  simpa only [nb090_alpha_dummy_005, nb090_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_002 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_140 (A : Class) :
    (nb090_alpha_dummy_291 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_291] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv)
      0

theorem nb090_fresh_141 (A : Class) :
    (nb090_alpha_dummy_292 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_292] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv)
      1

theorem nb090_distinct_142 (A : Class) :
    (nb090_alpha_dummy_291 A) ≠ (nb090_alpha_dummy_292 A) := by
  simpa only [nb090_alpha_dummy_291, nb090_alpha_dummy_292] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_283 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_143 (A : Class) :
    (nb090_alpha_dummy_661 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_661] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv)
      0

theorem nb090_fresh_144 (A : Class) :
    (nb090_alpha_dummy_662 A) ∉
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_662] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv)
      1

theorem nb090_distinct_145 (A : Class) :
    (nb090_alpha_dummy_661 A) ≠ (nb090_alpha_dummy_662 A) := by
  simpa only [nb090_alpha_dummy_661, nb090_alpha_dummy_662] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_146 (A : Class) :
    (nb090_alpha_dummy_381 A) ∉
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_381] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv)
      0

theorem nb090_fresh_147 (A : Class) :
    (nb090_alpha_dummy_382 A) ∉
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_382] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv)
      1

theorem nb090_distinct_148 (A : Class) :
    (nb090_alpha_dummy_381 A) ≠ (nb090_alpha_dummy_382 A) := by
  simpa only [nb090_alpha_dummy_381, nb090_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_373 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_149 (A : Class) :
    (nb090_alpha_dummy_835 A) ∉
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_835] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv)
      0

theorem nb090_fresh_150 (A : Class) :
    (nb090_alpha_dummy_836 A) ∉
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_836] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv)
      1

theorem nb090_distinct_151 (A : Class) :
    (nb090_alpha_dummy_835 A) ≠ (nb090_alpha_dummy_836 A) := by
  simpa only [nb090_alpha_dummy_835, nb090_alpha_dummy_836] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_827 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_152 (A : Class) :
    (nb090_alpha_dummy_013 A) ∉ (((Class.cv (nb090_alpha_dummy_006 A))).fv) := by
  simpa only [nb090_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_006 A))).fv) 0

theorem nb090_fresh_153 (A : Class) :
    (nb090_alpha_dummy_014 A) ∉ (((Class.cv (nb090_alpha_dummy_006 A))).fv) := by
  simpa only [nb090_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_006 A))).fv) 1

theorem nb090_distinct_154 (A : Class) :
    (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_014 A) := by
  simpa only [nb090_alpha_dummy_013, nb090_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_155 (v : Var) (u : Var) :
    (nb090_alpha_dummy_015 v u) ∉ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) := by
  simpa only [nb090_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 0

theorem nb090_fresh_156 (v : Var) (u : Var) :
    (nb090_alpha_dummy_016 v u) ∉ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) := by
  simpa only [nb090_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 1

theorem nb090_distinct_157 (v : Var) (u : Var) :
    (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_016 v u) := by
  simpa only [nb090_alpha_dummy_015, nb090_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_158 (A : Class) :
    (nb090_alpha_dummy_019 A) ∉
      (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_159 (A : Class) :
    (nb090_alpha_dummy_020 A) ∉
      (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_160 (A : Class) :
    (nb090_alpha_dummy_021 A) ∉
      (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_161 (A : Class) :
    (nb090_alpha_dummy_019 A) ≠ (nb090_alpha_dummy_020 A) := by
  simpa only [nb090_alpha_dummy_019, nb090_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_162 (A : Class) :
    (nb090_alpha_dummy_019 A) ≠ (nb090_alpha_dummy_021 A) := by
  simpa only [nb090_alpha_dummy_019, nb090_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_163 (A : Class) :
    (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_021 A) := by
  simpa only [nb090_alpha_dummy_020, nb090_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_164 (v : Var) (u : Var) :
    (nb090_alpha_dummy_022 v u) ∉
      (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_165 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ∉
      (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_166 (v : Var) (u : Var) :
    (nb090_alpha_dummy_024 v u) ∉
      (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_167 (v : Var) (u : Var) :
    (nb090_alpha_dummy_022 v u) ≠ (nb090_alpha_dummy_023 v u) := by
  simpa only [nb090_alpha_dummy_022, nb090_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_168 (v : Var) (u : Var) :
    (nb090_alpha_dummy_022 v u) ≠ (nb090_alpha_dummy_024 v u) := by
  simpa only [nb090_alpha_dummy_022, nb090_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_169 (v : Var) (u : Var) :
    (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_024 v u) := by
  simpa only [nb090_alpha_dummy_023, nb090_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_170 (A : Class) :
    (nb090_alpha_dummy_031 A) ∉
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv)
      0

theorem nb090_fresh_171 (A : Class) :
    (nb090_alpha_dummy_027 A) ∉
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv)
      0

theorem nb090_fresh_172 (A : Class) :
    (nb090_alpha_dummy_033 A) ∉
      (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv)
      0

theorem nb090_fresh_173 (v : Var) (u : Var) :
    (nb090_alpha_dummy_032 v u) ∉
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_023 v u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_023 v u))).fv)
      0

theorem nb090_fresh_174 (v : Var) (u : Var) :
    (nb090_alpha_dummy_028 v u) ∉
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv)
      0

theorem nb090_fresh_175 (v : Var) (u : Var) :
    (nb090_alpha_dummy_034 v u) ∉
      (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv) :=
  by
  simpa only [nb090_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪
        ((Class.cv (nb090_alpha_dummy_024 v u))).fv)
      0

theorem nb090_fresh_176 (A : Class) :
    (nb090_alpha_dummy_617 A) ∉
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_617] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv)
      0

theorem nb090_fresh_177 (A : Class) :
    (nb090_alpha_dummy_618 A) ∉
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_618] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv)
      1

theorem nb090_distinct_178 (A : Class) :
    (nb090_alpha_dummy_617 A) ≠ (nb090_alpha_dummy_618 A) := by
  simpa only [nb090_alpha_dummy_617, nb090_alpha_dummy_618] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_042 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_179 (A : Class) :
    (nb090_alpha_dummy_715 A) ∉
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_715] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv)
      0

theorem nb090_fresh_180 (A : Class) :
    (nb090_alpha_dummy_716 A) ∉
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_716] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv)
      1

theorem nb090_distinct_181 (A : Class) :
    (nb090_alpha_dummy_715 A) ≠ (nb090_alpha_dummy_716 A) := by
  simpa only [nb090_alpha_dummy_715, nb090_alpha_dummy_716] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_707 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_182 (A : Class) :
    (nb090_alpha_dummy_785 A) ∉
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_785] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv)
      0

theorem nb090_fresh_183 (A : Class) :
    (nb090_alpha_dummy_786 A) ∉
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_786] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv)
      1

theorem nb090_distinct_184 (A : Class) :
    (nb090_alpha_dummy_785 A) ≠ (nb090_alpha_dummy_786 A) := by
  simpa only [nb090_alpha_dummy_785, nb090_alpha_dummy_786] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_777 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_185 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_619 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_619] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv)
      0

theorem nb090_fresh_186 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_620 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_620] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv)
      1

theorem nb090_distinct_187 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_619 v u h) ≠ (nb090_alpha_dummy_620 v u h) := by
  simpa only [nb090_alpha_dummy_619, nb090_alpha_dummy_620] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_188 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_717 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_717] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv)
      0

theorem nb090_fresh_189 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_718 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_718] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv)
      1

theorem nb090_distinct_190 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_717 v u h) ≠ (nb090_alpha_dummy_718 v u h) := by
  simpa only [nb090_alpha_dummy_717, nb090_alpha_dummy_718] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_191 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_787 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_787] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
      0

theorem nb090_fresh_192 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_788 v u h) ∉
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_788] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv)
      1

theorem nb090_distinct_193 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_787 v u h) ≠ (nb090_alpha_dummy_788 v u h) := by
  simpa only [nb090_alpha_dummy_787, nb090_alpha_dummy_788] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_194 (A : Class) :
    (nb090_alpha_dummy_057 A) ∉
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_057] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
      0

theorem nb090_fresh_195 (A : Class) :
    (nb090_alpha_dummy_058 A) ∉
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_058] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
      1

theorem nb090_distinct_196 (A : Class) :
    (nb090_alpha_dummy_057 A) ≠ (nb090_alpha_dummy_058 A) := by
  simpa only [nb090_alpha_dummy_057, nb090_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_197 (A : Class) :
    (nb090_alpha_dummy_093 A) ∉
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv)
      0

theorem nb090_fresh_198 (A : Class) :
    (nb090_alpha_dummy_094 A) ∉
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv)
      1

theorem nb090_distinct_199 (A : Class) :
    (nb090_alpha_dummy_093 A) ≠ (nb090_alpha_dummy_094 A) := by
  simpa only [nb090_alpha_dummy_093, nb090_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_051 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_200 (A : Class) :
    (nb090_alpha_dummy_207 A) ∉
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_207] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
      0

theorem nb090_fresh_201 (A : Class) :
    (nb090_alpha_dummy_208 A) ∉
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_208] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv)
      1

theorem nb090_distinct_202 (A : Class) :
    (nb090_alpha_dummy_207 A) ≠ (nb090_alpha_dummy_208 A) := by
  simpa only [nb090_alpha_dummy_207, nb090_alpha_dummy_208] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_203 (h : Var) :
    (nb090_alpha_dummy_059 h) ∉
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_059] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv)
      0

theorem nb090_fresh_204 (h : Var) :
    (nb090_alpha_dummy_060 h) ∉
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_060] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv)
      1

theorem nb090_distinct_205 (h : Var) :
    (nb090_alpha_dummy_059 h) ≠ (nb090_alpha_dummy_060 h) := by
  simpa only [nb090_alpha_dummy_059, nb090_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_206 (h : Var) :
    (nb090_alpha_dummy_095 h) ∉
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv)
      0

theorem nb090_fresh_207 (h : Var) :
    (nb090_alpha_dummy_096 h) ∉
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv)
      1

theorem nb090_distinct_208 (h : Var) :
    (nb090_alpha_dummy_095 h) ≠ (nb090_alpha_dummy_096 h) := by
  simpa only [nb090_alpha_dummy_095, nb090_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_209 (h : Var) :
    (nb090_alpha_dummy_209 h) ∉
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv)
      0

theorem nb090_fresh_210 (h : Var) :
    (nb090_alpha_dummy_210 h) ∉
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_210] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv)
      1

theorem nb090_distinct_211 (h : Var) :
    (nb090_alpha_dummy_209 h) ≠ (nb090_alpha_dummy_210 h) := by
  simpa only [nb090_alpha_dummy_209, nb090_alpha_dummy_210] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_212 (A : Class) :
    (nb090_alpha_dummy_065 A) ∉ (((Class.cv (nb090_alpha_dummy_058 A))).fv) := by
  simpa only [nb090_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_058 A))).fv) 0

theorem nb090_fresh_213 (A : Class) :
    (nb090_alpha_dummy_066 A) ∉ (((Class.cv (nb090_alpha_dummy_058 A))).fv) := by
  simpa only [nb090_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_058 A))).fv) 1

theorem nb090_distinct_214 (A : Class) :
    (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_066 A) := by
  simpa only [nb090_alpha_dummy_065, nb090_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_215 (h : Var) :
    (nb090_alpha_dummy_067 h) ∉ (((Class.cv (nb090_alpha_dummy_060 h))).fv) := by
  simpa only [nb090_alpha_dummy_067] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_060 h))).fv) 0

theorem nb090_fresh_216 (h : Var) :
    (nb090_alpha_dummy_068 h) ∉ (((Class.cv (nb090_alpha_dummy_060 h))).fv) := by
  simpa only [nb090_alpha_dummy_068] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_060 h))).fv) 1

theorem nb090_distinct_217 (h : Var) :
    (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_068 h) := by
  simpa only [nb090_alpha_dummy_067, nb090_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_218 (A : Class) :
    (nb090_alpha_dummy_071 A) ∉
      (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_071] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_219 (A : Class) :
    (nb090_alpha_dummy_072 A) ∉
      (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_220 (A : Class) :
    (nb090_alpha_dummy_073 A) ∉
      (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_073] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_221 (A : Class) :
    (nb090_alpha_dummy_071 A) ≠ (nb090_alpha_dummy_072 A) := by
  simpa only [nb090_alpha_dummy_071, nb090_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_222 (A : Class) :
    (nb090_alpha_dummy_071 A) ≠ (nb090_alpha_dummy_073 A) := by
  simpa only [nb090_alpha_dummy_071, nb090_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_223 (A : Class) :
    (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_073 A) := by
  simpa only [nb090_alpha_dummy_072, nb090_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_224 (h : Var) :
    (nb090_alpha_dummy_074 h) ∉
      (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_074] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_225 (h : Var) :
    (nb090_alpha_dummy_075 h) ∉
      (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_075] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_226 (h : Var) :
    (nb090_alpha_dummy_076 h) ∉
      (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_076] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_227 (h : Var) :
    (nb090_alpha_dummy_074 h) ≠ (nb090_alpha_dummy_075 h) := by
  simpa only [nb090_alpha_dummy_074, nb090_alpha_dummy_075] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_228 (h : Var) :
    (nb090_alpha_dummy_074 h) ≠ (nb090_alpha_dummy_076 h) := by
  simpa only [nb090_alpha_dummy_074, nb090_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_229 (h : Var) :
    (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_076 h) := by
  simpa only [nb090_alpha_dummy_075, nb090_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_230 (A : Class) :
    (nb090_alpha_dummy_083 A) ∉
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv)
      0

theorem nb090_fresh_231 (A : Class) :
    (nb090_alpha_dummy_079 A) ∉
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv)
      0

theorem nb090_fresh_232 (A : Class) :
    (nb090_alpha_dummy_085 A) ∉
      (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_085] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv)
      0

theorem nb090_fresh_233 (h : Var) :
    (nb090_alpha_dummy_084 h) ∉
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv)
      0

theorem nb090_fresh_234 (h : Var) :
    (nb090_alpha_dummy_080 h) ∉
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv)
      0

theorem nb090_fresh_235 (h : Var) :
    (nb090_alpha_dummy_086 h) ∉
      (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_086] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv)
      0

theorem nb090_fresh_236 (A : Class) :
    (nb090_alpha_dummy_101 A) ∉ (((Class.cv (nb090_alpha_dummy_094 A))).fv) := by
  simpa only [nb090_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_094 A))).fv) 0

theorem nb090_fresh_237 (A : Class) :
    (nb090_alpha_dummy_102 A) ∉ (((Class.cv (nb090_alpha_dummy_094 A))).fv) := by
  simpa only [nb090_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_094 A))).fv) 1

theorem nb090_distinct_238 (A : Class) :
    (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_102 A) := by
  simpa only [nb090_alpha_dummy_101, nb090_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_239 (h : Var) :
    (nb090_alpha_dummy_103 h) ∉ (((Class.cv (nb090_alpha_dummy_096 h))).fv) := by
  simpa only [nb090_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_096 h))).fv) 0

theorem nb090_fresh_240 (h : Var) :
    (nb090_alpha_dummy_104 h) ∉ (((Class.cv (nb090_alpha_dummy_096 h))).fv) := by
  simpa only [nb090_alpha_dummy_104] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_096 h))).fv) 1

theorem nb090_distinct_241 (h : Var) :
    (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_104 h) := by
  simpa only [nb090_alpha_dummy_103, nb090_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv) (i := 0) (j := 1)
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
    (nb090_alpha_dummy_107 A) ∉
      (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_243 (A : Class) :
    (nb090_alpha_dummy_108 A) ∉
      (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_244 (A : Class) :
    (nb090_alpha_dummy_109 A) ∉
      (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_245 (A : Class) :
    (nb090_alpha_dummy_107 A) ≠ (nb090_alpha_dummy_108 A) := by
  simpa only [nb090_alpha_dummy_107, nb090_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_246 (A : Class) :
    (nb090_alpha_dummy_107 A) ≠ (nb090_alpha_dummy_109 A) := by
  simpa only [nb090_alpha_dummy_107, nb090_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_247 (A : Class) :
    (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_109 A) := by
  simpa only [nb090_alpha_dummy_108, nb090_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_248 (h : Var) :
    (nb090_alpha_dummy_110 h) ∉
      (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_249 (h : Var) :
    (nb090_alpha_dummy_111 h) ∉
      (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_111] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_250 (h : Var) :
    (nb090_alpha_dummy_112 h) ∉
      (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_112] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_251 (h : Var) :
    (nb090_alpha_dummy_110 h) ≠ (nb090_alpha_dummy_111 h) := by
  simpa only [nb090_alpha_dummy_110, nb090_alpha_dummy_111] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_252 (h : Var) :
    (nb090_alpha_dummy_110 h) ≠ (nb090_alpha_dummy_112 h) := by
  simpa only [nb090_alpha_dummy_110, nb090_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_253 (h : Var) :
    (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_112 h) := by
  simpa only [nb090_alpha_dummy_111, nb090_alpha_dummy_112] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_254 (A : Class) :
    (nb090_alpha_dummy_119 A) ∉
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_108 A))).fv)
      0

theorem nb090_fresh_255 (A : Class) :
    (nb090_alpha_dummy_115 A) ∉
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv)
      0

theorem nb090_fresh_256 (A : Class) :
    (nb090_alpha_dummy_121 A) ∉
      (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_109 A))).fv)
      0

theorem nb090_fresh_257 (h : Var) :
    (nb090_alpha_dummy_120 h) ∉
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_111 h))).fv)
      0

theorem nb090_fresh_258 (h : Var) :
    (nb090_alpha_dummy_116 h) ∉
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_116] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv)
      0

theorem nb090_fresh_259 (h : Var) :
    (nb090_alpha_dummy_122 h) ∉
      (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_112 h))).fv)
      0

theorem nb090_fresh_260 (A : Class) :
    (nb090_alpha_dummy_135 A) ∉
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_135] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv)
      0

theorem nb090_fresh_261 (A : Class) :
    (nb090_alpha_dummy_136 A) ∉
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_136] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv)
      1

theorem nb090_distinct_262 (A : Class) :
    (nb090_alpha_dummy_135 A) ≠ (nb090_alpha_dummy_136 A) := by
  simpa only [nb090_alpha_dummy_135, nb090_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_263 (A : Class) :
    (nb090_alpha_dummy_171 A) ∉
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_171] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv)
      0

theorem nb090_fresh_264 (A : Class) :
    (nb090_alpha_dummy_172 A) ∉
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_172] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv)
      1

theorem nb090_distinct_265 (A : Class) :
    (nb090_alpha_dummy_171 A) ≠ (nb090_alpha_dummy_172 A) := by
  simpa only [nb090_alpha_dummy_171, nb090_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_129 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_266 (h : Var) :
    (nb090_alpha_dummy_137 h) ∉
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_137] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv)
      0

theorem nb090_fresh_267 (h : Var) :
    (nb090_alpha_dummy_138 h) ∉
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_138] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv)
      1

theorem nb090_distinct_268 (h : Var) :
    (nb090_alpha_dummy_137 h) ≠ (nb090_alpha_dummy_138 h) := by
  simpa only [nb090_alpha_dummy_137, nb090_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_269 (h : Var) :
    (nb090_alpha_dummy_173 h) ∉
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv)
      0

theorem nb090_fresh_270 (h : Var) :
    (nb090_alpha_dummy_174 h) ∉
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_174] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv)
      1

theorem nb090_distinct_271 (h : Var) :
    (nb090_alpha_dummy_173 h) ≠ (nb090_alpha_dummy_174 h) := by
  simpa only [nb090_alpha_dummy_173, nb090_alpha_dummy_174] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_272 (A : Class) :
    (nb090_alpha_dummy_143 A) ∉ (((Class.cv (nb090_alpha_dummy_136 A))).fv) := by
  simpa only [nb090_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_136 A))).fv) 0

theorem nb090_fresh_273 (A : Class) :
    (nb090_alpha_dummy_144 A) ∉ (((Class.cv (nb090_alpha_dummy_136 A))).fv) := by
  simpa only [nb090_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_136 A))).fv) 1

theorem nb090_distinct_274 (A : Class) :
    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_144 A) := by
  simpa only [nb090_alpha_dummy_143, nb090_alpha_dummy_144] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_275 (h : Var) :
    (nb090_alpha_dummy_145 h) ∉ (((Class.cv (nb090_alpha_dummy_138 h))).fv) := by
  simpa only [nb090_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_138 h))).fv) 0

theorem nb090_fresh_276 (h : Var) :
    (nb090_alpha_dummy_146 h) ∉ (((Class.cv (nb090_alpha_dummy_138 h))).fv) := by
  simpa only [nb090_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_138 h))).fv) 1

theorem nb090_distinct_277 (h : Var) :
    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_146 h) := by
  simpa only [nb090_alpha_dummy_145, nb090_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_278 (A : Class) :
    (nb090_alpha_dummy_149 A) ∉
      (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_149] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_279 (A : Class) :
    (nb090_alpha_dummy_150 A) ∉
      (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_150] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_280 (A : Class) :
    (nb090_alpha_dummy_151 A) ∉
      (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_151] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_281 (A : Class) :
    (nb090_alpha_dummy_149 A) ≠ (nb090_alpha_dummy_150 A) := by
  simpa only [nb090_alpha_dummy_149, nb090_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_282 (A : Class) :
    (nb090_alpha_dummy_149 A) ≠ (nb090_alpha_dummy_151 A) := by
  simpa only [nb090_alpha_dummy_149, nb090_alpha_dummy_151] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_283 (A : Class) :
    (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_151 A) := by
  simpa only [nb090_alpha_dummy_150, nb090_alpha_dummy_151] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_284 (h : Var) :
    (nb090_alpha_dummy_152 h) ∉
      (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_152] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_285 (h : Var) :
    (nb090_alpha_dummy_153 h) ∉
      (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_153] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_286 (h : Var) :
    (nb090_alpha_dummy_154 h) ∉
      (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_154] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_287 (h : Var) :
    (nb090_alpha_dummy_152 h) ≠ (nb090_alpha_dummy_153 h) := by
  simpa only [nb090_alpha_dummy_152, nb090_alpha_dummy_153] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_288 (h : Var) :
    (nb090_alpha_dummy_152 h) ≠ (nb090_alpha_dummy_154 h) := by
  simpa only [nb090_alpha_dummy_152, nb090_alpha_dummy_154] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_289 (h : Var) :
    (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_154 h) := by
  simpa only [nb090_alpha_dummy_153, nb090_alpha_dummy_154] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_290 (A : Class) :
    (nb090_alpha_dummy_161 A) ∉
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_150 A))).fv)
      0

theorem nb090_fresh_291 (A : Class) :
    (nb090_alpha_dummy_157 A) ∉
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv)
      0

theorem nb090_fresh_292 (A : Class) :
    (nb090_alpha_dummy_163 A) ∉
      (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_163] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_151 A))).fv)
      0

theorem nb090_fresh_293 (h : Var) :
    (nb090_alpha_dummy_162 h) ∉
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_162] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_153 h))).fv)
      0

theorem nb090_fresh_294 (h : Var) :
    (nb090_alpha_dummy_158 h) ∉
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv)
      0

theorem nb090_fresh_295 (h : Var) :
    (nb090_alpha_dummy_164 h) ∉
      (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_164] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_154 h))).fv)
      0

theorem nb090_fresh_296 (A : Class) :
    (nb090_alpha_dummy_179 A) ∉ (((Class.cv (nb090_alpha_dummy_172 A))).fv) := by
  simpa only [nb090_alpha_dummy_179] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_172 A))).fv) 0

theorem nb090_fresh_297 (A : Class) :
    (nb090_alpha_dummy_180 A) ∉ (((Class.cv (nb090_alpha_dummy_172 A))).fv) := by
  simpa only [nb090_alpha_dummy_180] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_172 A))).fv) 1

theorem nb090_distinct_298 (A : Class) :
    (nb090_alpha_dummy_179 A) ≠ (nb090_alpha_dummy_180 A) := by
  simpa only [nb090_alpha_dummy_179, nb090_alpha_dummy_180] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_172 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_299 (h : Var) :
    (nb090_alpha_dummy_181 h) ∉ (((Class.cv (nb090_alpha_dummy_174 h))).fv) := by
  simpa only [nb090_alpha_dummy_181] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_174 h))).fv) 0

theorem nb090_fresh_300 (h : Var) :
    (nb090_alpha_dummy_182 h) ∉ (((Class.cv (nb090_alpha_dummy_174 h))).fv) := by
  simpa only [nb090_alpha_dummy_182] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_174 h))).fv) 1

theorem nb090_distinct_301 (h : Var) :
    (nb090_alpha_dummy_181 h) ≠ (nb090_alpha_dummy_182 h) := by
  simpa only [nb090_alpha_dummy_181, nb090_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_174 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_302 (A : Class) :
    (nb090_alpha_dummy_185 A) ∉
      (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_185] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_303 (A : Class) :
    (nb090_alpha_dummy_186 A) ∉
      (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_186] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_304 (A : Class) :
    (nb090_alpha_dummy_187 A) ∉
      (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_187] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_305 (A : Class) :
    (nb090_alpha_dummy_185 A) ≠ (nb090_alpha_dummy_186 A) := by
  simpa only [nb090_alpha_dummy_185, nb090_alpha_dummy_186] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_306 (A : Class) :
    (nb090_alpha_dummy_185 A) ≠ (nb090_alpha_dummy_187 A) := by
  simpa only [nb090_alpha_dummy_185, nb090_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_307 (A : Class) :
    (nb090_alpha_dummy_186 A) ≠ (nb090_alpha_dummy_187 A) := by
  simpa only [nb090_alpha_dummy_186, nb090_alpha_dummy_187] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_308 (h : Var) :
    (nb090_alpha_dummy_188 h) ∉
      (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_188] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_309 (h : Var) :
    (nb090_alpha_dummy_189 h) ∉
      (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_189] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_310 (h : Var) :
    (nb090_alpha_dummy_190 h) ∉
      (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_190] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_311 (h : Var) :
    (nb090_alpha_dummy_188 h) ≠ (nb090_alpha_dummy_189 h) := by
  simpa only [nb090_alpha_dummy_188, nb090_alpha_dummy_189] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_312 (h : Var) :
    (nb090_alpha_dummy_188 h) ≠ (nb090_alpha_dummy_190 h) := by
  simpa only [nb090_alpha_dummy_188, nb090_alpha_dummy_190] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_313 (h : Var) :
    (nb090_alpha_dummy_189 h) ≠ (nb090_alpha_dummy_190 h) := by
  simpa only [nb090_alpha_dummy_189, nb090_alpha_dummy_190] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_314 (A : Class) :
    (nb090_alpha_dummy_197 A) ∉
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_186 A))).fv)
      0

theorem nb090_fresh_315 (A : Class) :
    (nb090_alpha_dummy_193 A) ∉
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_193] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv)
      0

theorem nb090_fresh_316 (A : Class) :
    (nb090_alpha_dummy_199 A) ∉
      (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_199] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_187 A))).fv)
      0

theorem nb090_fresh_317 (h : Var) :
    (nb090_alpha_dummy_198 h) ∉
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_198] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_189 h))).fv)
      0

theorem nb090_fresh_318 (h : Var) :
    (nb090_alpha_dummy_194 h) ∉
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_194] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv)
      0

theorem nb090_fresh_319 (h : Var) :
    (nb090_alpha_dummy_200 h) ∉
      (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_200] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_190 h))).fv)
      0

theorem nb090_fresh_320 (A : Class) :
    (nb090_alpha_dummy_215 A) ∉ (((Class.cv (nb090_alpha_dummy_208 A))).fv) := by
  simpa only [nb090_alpha_dummy_215] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_208 A))).fv) 0

theorem nb090_fresh_321 (A : Class) :
    (nb090_alpha_dummy_216 A) ∉ (((Class.cv (nb090_alpha_dummy_208 A))).fv) := by
  simpa only [nb090_alpha_dummy_216] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_208 A))).fv) 1

theorem nb090_distinct_322 (A : Class) :
    (nb090_alpha_dummy_215 A) ≠ (nb090_alpha_dummy_216 A) := by
  simpa only [nb090_alpha_dummy_215, nb090_alpha_dummy_216] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_208 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_323 (h : Var) :
    (nb090_alpha_dummy_217 h) ∉ (((Class.cv (nb090_alpha_dummy_210 h))).fv) := by
  simpa only [nb090_alpha_dummy_217] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_210 h))).fv) 0

theorem nb090_fresh_324 (h : Var) :
    (nb090_alpha_dummy_218 h) ∉ (((Class.cv (nb090_alpha_dummy_210 h))).fv) := by
  simpa only [nb090_alpha_dummy_218] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_210 h))).fv) 1

theorem nb090_distinct_325 (h : Var) :
    (nb090_alpha_dummy_217 h) ≠ (nb090_alpha_dummy_218 h) := by
  simpa only [nb090_alpha_dummy_217, nb090_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_210 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_326 (A : Class) :
    (nb090_alpha_dummy_221 A) ∉
      (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_221] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_327 (A : Class) :
    (nb090_alpha_dummy_222 A) ∉
      (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_222] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_328 (A : Class) :
    (nb090_alpha_dummy_223 A) ∉
      (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_223] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_329 (A : Class) :
    (nb090_alpha_dummy_221 A) ≠ (nb090_alpha_dummy_222 A) := by
  simpa only [nb090_alpha_dummy_221, nb090_alpha_dummy_222] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_330 (A : Class) :
    (nb090_alpha_dummy_221 A) ≠ (nb090_alpha_dummy_223 A) := by
  simpa only [nb090_alpha_dummy_221, nb090_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_331 (A : Class) :
    (nb090_alpha_dummy_222 A) ≠ (nb090_alpha_dummy_223 A) := by
  simpa only [nb090_alpha_dummy_222, nb090_alpha_dummy_223] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_332 (h : Var) :
    (nb090_alpha_dummy_224 h) ∉
      (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_224] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_333 (h : Var) :
    (nb090_alpha_dummy_225 h) ∉
      (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_225] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_334 (h : Var) :
    (nb090_alpha_dummy_226 h) ∉
      (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_226] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_335 (h : Var) :
    (nb090_alpha_dummy_224 h) ≠ (nb090_alpha_dummy_225 h) := by
  simpa only [nb090_alpha_dummy_224, nb090_alpha_dummy_225] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_336 (h : Var) :
    (nb090_alpha_dummy_224 h) ≠ (nb090_alpha_dummy_226 h) := by
  simpa only [nb090_alpha_dummy_224, nb090_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_337 (h : Var) :
    (nb090_alpha_dummy_225 h) ≠ (nb090_alpha_dummy_226 h) := by
  simpa only [nb090_alpha_dummy_225, nb090_alpha_dummy_226] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_338 (A : Class) :
    (nb090_alpha_dummy_233 A) ∉
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_233] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv)
      0

theorem nb090_fresh_339 (A : Class) :
    (nb090_alpha_dummy_229 A) ∉
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_229] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv)
      0

theorem nb090_fresh_340 (A : Class) :
    (nb090_alpha_dummy_235 A) ∉
      (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_235] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv)
      0

theorem nb090_fresh_341 (h : Var) :
    (nb090_alpha_dummy_234 h) ∉
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_234] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv)
      0

theorem nb090_fresh_342 (h : Var) :
    (nb090_alpha_dummy_230 h) ∉
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_230] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv)
      0

theorem nb090_fresh_343 (h : Var) :
    (nb090_alpha_dummy_236 h) ∉
      (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_236] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv)
      0

theorem nb090_fresh_344 (A : Class) :
    (nb090_alpha_dummy_247 A) ∉
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_247] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv)
      0

theorem nb090_fresh_345 (A : Class) :
    (nb090_alpha_dummy_248 A) ∉
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_248] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv)
      1

theorem nb090_distinct_346 (A : Class) :
    (nb090_alpha_dummy_247 A) ≠ (nb090_alpha_dummy_248 A) := by
  simpa only [nb090_alpha_dummy_247, nb090_alpha_dummy_248] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
        ((Class.cv (nb090_alpha_dummy_243 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_347 (h : Var) :
    (nb090_alpha_dummy_249 h) ∉
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_249] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv)
      0

theorem nb090_fresh_348 (h : Var) :
    (nb090_alpha_dummy_250 h) ∉
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_250] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv)
      1

theorem nb090_distinct_349 (h : Var) :
    (nb090_alpha_dummy_249 h) ≠ (nb090_alpha_dummy_250 h) := by
  simpa only [nb090_alpha_dummy_249, nb090_alpha_dummy_250] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_245 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_350 (A : Class) :
    (nb090_alpha_dummy_255 A) ∉ (((Class.cv (nb090_alpha_dummy_248 A))).fv) := by
  simpa only [nb090_alpha_dummy_255] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_248 A))).fv) 0

theorem nb090_fresh_351 (A : Class) :
    (nb090_alpha_dummy_256 A) ∉ (((Class.cv (nb090_alpha_dummy_248 A))).fv) := by
  simpa only [nb090_alpha_dummy_256] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_248 A))).fv) 1

theorem nb090_distinct_352 (A : Class) :
    (nb090_alpha_dummy_255 A) ≠ (nb090_alpha_dummy_256 A) := by
  simpa only [nb090_alpha_dummy_255, nb090_alpha_dummy_256] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_248 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_353 (h : Var) :
    (nb090_alpha_dummy_257 h) ∉ (((Class.cv (nb090_alpha_dummy_250 h))).fv) := by
  simpa only [nb090_alpha_dummy_257] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_250 h))).fv) 0

theorem nb090_fresh_354 (h : Var) :
    (nb090_alpha_dummy_258 h) ∉ (((Class.cv (nb090_alpha_dummy_250 h))).fv) := by
  simpa only [nb090_alpha_dummy_258] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_250 h))).fv) 1

theorem nb090_distinct_355 (h : Var) :
    (nb090_alpha_dummy_257 h) ≠ (nb090_alpha_dummy_258 h) := by
  simpa only [nb090_alpha_dummy_257, nb090_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_250 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_356 (A : Class) :
    (nb090_alpha_dummy_261 A) ∉
      (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_261] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_357 (A : Class) :
    (nb090_alpha_dummy_262 A) ∉
      (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_262] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_358 (A : Class) :
    (nb090_alpha_dummy_263 A) ∉
      (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_263] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_359 (A : Class) :
    (nb090_alpha_dummy_261 A) ≠ (nb090_alpha_dummy_262 A) := by
  simpa only [nb090_alpha_dummy_261, nb090_alpha_dummy_262] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_360 (A : Class) :
    (nb090_alpha_dummy_261 A) ≠ (nb090_alpha_dummy_263 A) := by
  simpa only [nb090_alpha_dummy_261, nb090_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_361 (A : Class) :
    (nb090_alpha_dummy_262 A) ≠ (nb090_alpha_dummy_263 A) := by
  simpa only [nb090_alpha_dummy_262, nb090_alpha_dummy_263] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_362 (h : Var) :
    (nb090_alpha_dummy_264 h) ∉
      (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_264] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_363 (h : Var) :
    (nb090_alpha_dummy_265 h) ∉
      (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_265] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_364 (h : Var) :
    (nb090_alpha_dummy_266 h) ∉
      (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_266] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_365 (h : Var) :
    (nb090_alpha_dummy_264 h) ≠ (nb090_alpha_dummy_265 h) := by
  simpa only [nb090_alpha_dummy_264, nb090_alpha_dummy_265] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_366 (h : Var) :
    (nb090_alpha_dummy_264 h) ≠ (nb090_alpha_dummy_266 h) := by
  simpa only [nb090_alpha_dummy_264, nb090_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_367 (h : Var) :
    (nb090_alpha_dummy_265 h) ≠ (nb090_alpha_dummy_266 h) := by
  simpa only [nb090_alpha_dummy_265, nb090_alpha_dummy_266] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_368 (A : Class) :
    (nb090_alpha_dummy_273 A) ∉
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_273] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv)
      0

theorem nb090_fresh_369 (A : Class) :
    (nb090_alpha_dummy_269 A) ∉
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv)
      0

theorem nb090_fresh_370 (A : Class) :
    (nb090_alpha_dummy_275 A) ∉
      (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) :=
  by
  simpa only [nb090_alpha_dummy_275] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv)
      0

theorem nb090_fresh_371 (h : Var) :
    (nb090_alpha_dummy_274 h) ∉
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_274] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv)
      0

theorem nb090_fresh_372 (h : Var) :
    (nb090_alpha_dummy_270 h) ∉
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv)
      0

theorem nb090_fresh_373 (h : Var) :
    (nb090_alpha_dummy_276 h) ∉
      (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) :=
  by
  simpa only [nb090_alpha_dummy_276] using
    freshVar_not_mem
      (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv)
      0

theorem nb090_fresh_374 (A : Class) :
    (nb090_alpha_dummy_327 A) ∉ (((Class.cv (nb090_alpha_dummy_285 A))).fv) := by
  simpa only [nb090_alpha_dummy_327] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_285 A))).fv) 0

theorem nb090_fresh_375 (u : Var) :
    (nb090_alpha_dummy_328 u) ∉ (((Class.cv (nb090_alpha_dummy_286 u))).fv) := by
  simpa only [nb090_alpha_dummy_328] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_286 u))).fv) 0

theorem nb090_fresh_376 (A : Class) :
    (nb090_alpha_dummy_299 A) ∉ (((Class.cv (nb090_alpha_dummy_292 A))).fv) := by
  simpa only [nb090_alpha_dummy_299] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_292 A))).fv) 0

theorem nb090_fresh_377 (A : Class) :
    (nb090_alpha_dummy_300 A) ∉ (((Class.cv (nb090_alpha_dummy_292 A))).fv) := by
  simpa only [nb090_alpha_dummy_300] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_292 A))).fv) 1

theorem nb090_distinct_378 (A : Class) :
    (nb090_alpha_dummy_299 A) ≠ (nb090_alpha_dummy_300 A) := by
  simpa only [nb090_alpha_dummy_299, nb090_alpha_dummy_300] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_379 (u : Var) :
    (nb090_alpha_dummy_301 u) ∉ (((Class.cv (nb090_alpha_dummy_294 u))).fv) := by
  simpa only [nb090_alpha_dummy_301] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_294 u))).fv) 0

theorem nb090_fresh_380 (u : Var) :
    (nb090_alpha_dummy_302 u) ∉ (((Class.cv (nb090_alpha_dummy_294 u))).fv) := by
  simpa only [nb090_alpha_dummy_302] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_294 u))).fv) 1

theorem nb090_distinct_381 (u : Var) :
    (nb090_alpha_dummy_301 u) ≠ (nb090_alpha_dummy_302 u) := by
  simpa only [nb090_alpha_dummy_301, nb090_alpha_dummy_302] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_382 (A : Class) :
    (nb090_alpha_dummy_305 A) ∉
      (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_305] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_383 (A : Class) :
    (nb090_alpha_dummy_306 A) ∉
      (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_306] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_384 (A : Class) :
    (nb090_alpha_dummy_307 A) ∉
      (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_307] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_385 (A : Class) :
    (nb090_alpha_dummy_305 A) ≠ (nb090_alpha_dummy_306 A) := by
  simpa only [nb090_alpha_dummy_305, nb090_alpha_dummy_306] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_386 (A : Class) :
    (nb090_alpha_dummy_305 A) ≠ (nb090_alpha_dummy_307 A) := by
  simpa only [nb090_alpha_dummy_305, nb090_alpha_dummy_307] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_387 (A : Class) :
    (nb090_alpha_dummy_306 A) ≠ (nb090_alpha_dummy_307 A) := by
  simpa only [nb090_alpha_dummy_306, nb090_alpha_dummy_307] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_388 (u : Var) :
    (nb090_alpha_dummy_308 u) ∉
      (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_308] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_389 (u : Var) :
    (nb090_alpha_dummy_309 u) ∉
      (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_309] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_390 (u : Var) :
    (nb090_alpha_dummy_310 u) ∉
      (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb090_alpha_dummy_310] using
    freshVar_not_mem (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_391 (u : Var) :
    (nb090_alpha_dummy_308 u) ≠ (nb090_alpha_dummy_309 u) := by
  simpa only [nb090_alpha_dummy_308, nb090_alpha_dummy_309] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
