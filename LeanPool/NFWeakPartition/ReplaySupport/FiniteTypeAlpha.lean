/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! Freshness and support lemmas for finite-type alpha renaming. -/


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

/-! Shared freshness facts and the four alpha-certificate subtrees for finite types. -/


namespace FiniteTypeAlpha

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_000`. -/
@[expose]
def alphaDummy000 (M : Class) : Var :=
  (freshVar ((M).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_001`. -/
@[expose]
def alphaDummy001 (M : Class) : Var :=
  (freshVar ((M).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_002`. -/
@[expose]
def alphaDummy002 (M : Class) : Var :=
  (freshVar (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio (alphaDummy001 M)
          (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
            (synWrex (alphaDummy000 M) M
              (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                (Class.cv (alphaDummy001 M))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_003`. -/
@[expose]
def alphaDummy003 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio n
          (synWa (Wff.classMem (Class.cv n) (synCnnc))
            (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 : Var :=
  (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
      ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_005`. -/
@[expose]
def alphaDummy005 : Var :=
  (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_006`. -/
@[expose]
def alphaDummy006 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_007`. -/
@[expose]
def alphaDummy007 : Var :=
  (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_008`. -/
@[expose]
def alphaDummy008 (M : Class) : Var :=
  (freshVar (({(alphaDummy001 M)} : Finset Var) ∪
      ((synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
          (synWrex (alphaDummy000 M) M
            (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
              (Class.cv (alphaDummy001 M)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_009`. -/
@[expose]
def alphaDummy009 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (({ n } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv n) (synCnnc))
          (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_010`. -/
@[expose]
def alphaDummy010 (M : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
            (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
              (synWrex (alphaDummy000 M) M
                (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                  (Class.cv (alphaDummy001 M))))))
          (synCsn (Class.cv (alphaDummy008 M)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_011`. -/
@[expose]
def alphaDummy011 (M : Class) : Var :=
  (freshVar (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
            (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
              (synWrex (alphaDummy000 M) M
                (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                  (Class.cv (alphaDummy001 M))))))
          (synCsn (Class.cv (alphaDummy008 M)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_012`. -/
@[expose]
def alphaDummy012 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
            (synWa (Wff.classMem (Class.cv n) (synCnnc))
              (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
          (synCsn (Class.cv (alphaDummy009 n M a)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_013`. -/
@[expose]
def alphaDummy013 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
            (synWa (Wff.classMem (Class.cv n) (synCnnc))
              (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
          (synCsn (Class.cv (alphaDummy009 n M a)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_014`. -/
@[expose]
def alphaDummy014 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_015`. -/
@[expose]
def alphaDummy015 : Var :=
  (freshVar (((Class.cab alphaDummy006
        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy006))
          (synWral alphaDummy014 (Class.cv alphaDummy006)
            (Wff.classMem (synCplc (Class.cv alphaDummy014) (synC1c))
              (Class.cv alphaDummy006)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_016`. -/
@[expose]
def alphaDummy016 : Var :=
  (freshVar (((Class.cab alphaDummy006
        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy006))
          (synWral alphaDummy014 (Class.cv alphaDummy006)
            (Wff.classMem (synCplc (Class.cv alphaDummy014) (synC1c))
              (Class.cv alphaDummy006)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_017`. -/
@[expose]
def alphaDummy017 : Var :=
  (freshVar (((synC0)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_018`. -/
@[expose]
def alphaDummy018 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_019`. -/
@[expose]
def alphaDummy019 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_020`. -/
@[expose]
def alphaDummy020 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_021`. -/
@[expose]
def alphaDummy021 : Var :=
  (freshVar (((Class.cv alphaDummy014)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_022`. -/
@[expose]
def alphaDummy022 : Var :=
  (freshVar (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
      ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_023`. -/
@[expose]
def alphaDummy023 : Var :=
  (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_024`. -/
@[expose]
def alphaDummy024 : Var :=
  (freshVar (((synCcompl (Class.cv alphaDummy019))).fv ∪
      ((synCcompl (Class.cv alphaDummy020))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_025`. -/
@[expose]
def alphaDummy025 : Var :=
  (freshVar (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_026`. -/
@[expose]
def alphaDummy026 : Var :=
  (freshVar (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_027`. -/
@[expose]
def alphaDummy027 (M : Class) : Var :=
  (freshVar (((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_028`. -/
@[expose]
def alphaDummy028 (a : Var) : Var :=
  (freshVar (((synCnin (synCpw (Class.cv a)) (synC1c))).fv ∪
      ((synCnin (synCpw (Class.cv a)) (synC1c))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_029`. -/
@[expose]
def alphaDummy029 (M : Class) : Var :=
  (freshVar (((synCpw (Class.cv (alphaDummy000 M)))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_030`. -/
@[expose]
def alphaDummy030 (a : Var) : Var :=
  (freshVar (((synCpw (Class.cv a))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_031`. -/
@[expose]
def alphaDummy031 (M : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy000 M))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_032`. -/
@[expose]
def alphaDummy032 (a : Var) : Var :=
  (freshVar (((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_033`. -/
@[expose]
def alphaDummy033 (M : Class) : Var :=
  (freshVar (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv ∪
      ((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_034`. -/
@[expose]
def alphaDummy034 (a : Var) : Var :=
  (freshVar (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv ∪
      ((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_035`. -/
@[expose]
def alphaDummy035 (M : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy031 M))).fv ∪ ((Class.cv (alphaDummy000 M))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_036`. -/
@[expose]
def alphaDummy036 (a : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy032 a))).fv ∪ ((Class.cv a)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_037`. -/
@[expose]
def alphaDummy037 (M : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy008 M))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_038`. -/
@[expose]
def alphaDummy038 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (alphaDummy009 n M a))).fv) 0)

theorem fresh_003 (M : Class) :
    (alphaDummy010 M) ∉
      (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
              (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                (synWrex (alphaDummy000 M) M
                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                    (Class.cv (alphaDummy001 M))))))
            (synCsn (Class.cv (alphaDummy008 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
              (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                (synWrex (alphaDummy000 M) M
                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                    (Class.cv (alphaDummy001 M))))))
            (synCsn (Class.cv (alphaDummy008 M)))))).fv)
      0

theorem fresh_004 (M : Class) :
    (alphaDummy011 M) ∉
      (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
              (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                (synWrex (alphaDummy000 M) M
                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                    (Class.cv (alphaDummy001 M))))))
            (synCsn (Class.cv (alphaDummy008 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alphaDummy008 M) (Wff.classEq (Class.cab (alphaDummy001 M)
              (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                (synWrex (alphaDummy000 M) M
                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                    (Class.cv (alphaDummy001 M))))))
            (synCsn (Class.cv (alphaDummy008 M)))))).fv)
      1

theorem fresh_006 (n : Var) (M : Class) (a : Var) :
    (alphaDummy012 n M a) ∉
      (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
              (synWa (Wff.classMem (Class.cv n) (synCnnc))
                (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
            (synCsn (Class.cv (alphaDummy009 n M a)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
              (synWa (Wff.classMem (Class.cv n) (synCnnc))
                (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
            (synCsn (Class.cv (alphaDummy009 n M a)))))).fv)
      0

theorem fresh_007 (n : Var) (M : Class) (a : Var) :
    (alphaDummy013 n M a) ∉
      (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
              (synWa (Wff.classMem (Class.cv n) (synCnnc))
                (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
            (synCsn (Class.cv (alphaDummy009 n M a)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alphaDummy009 n M a) (Wff.classEq (Class.cab n
              (synWa (Wff.classMem (Class.cv n) (synCnnc))
                (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
            (synCsn (Class.cv (alphaDummy009 n M a)))))).fv)
      1

theorem fresh_025 (M : Class) :
    (alphaDummy002 M) ∉
      (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio (alphaDummy001 M)
            (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
              (synWrex (alphaDummy000 M) M
                (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                  (Class.cv (alphaDummy001 M))))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio (alphaDummy001 M)
            (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
              (synWrex (alphaDummy000 M) M
                (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                  (Class.cv (alphaDummy001 M))))))).fv)
      0

theorem fresh_026 (n : Var) (M : Class) (a : Var) :
    (alphaDummy003 n M a) ∉
      (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio n
            (synWa (Wff.classMem (Class.cv n) (synCnnc))
              (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Wff.classEq M (synC0))).fv ∪ ((synC0)).fv ∪ ((synCio n
            (synWa (Wff.classMem (Class.cv n) (synCnnc))
              (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))).fv)
      0

theorem fresh_039 (M : Class) : (alphaDummy000 M) ∉ ((M).fv) := by
  exact freshVar_not_mem ((M).fv) 0

theorem fresh_040 (M : Class) : (alphaDummy001 M) ∉ ((M).fv) := by
  exact freshVar_not_mem ((M).fv) 1

theorem fresh_042 (M : Class) :
    (alphaDummy008 M) ∉
      (({(alphaDummy001 M)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
            (synWrex (alphaDummy000 M) M
              (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                (Class.cv (alphaDummy001 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (({(alphaDummy001 M)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
            (synWrex (alphaDummy000 M) M
              (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                (Class.cv (alphaDummy001 M)))))).fv)
      0

theorem fresh_043 (n : Var) (M : Class) (a : Var) :
    (alphaDummy009 n M a) ∉
      (({ n } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv n) (synCnnc))
            (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n))))).fv) :=
  by
  exact
    freshVar_not_mem
      (({ n } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv n) (synCnnc))
            (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n))))).fv)
      0

theorem support_part_0000 : alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0000 :
    alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv) := by
  exact (Finset.mem_union_left (((synC1c)).fv) support_part_0000)

theorem support_part_0001 : alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0001 : alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv) := by
  exact support_part_0001

theorem support_part_0002 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0002 :
    alphaDummy019 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
        ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) support_part_0002)

theorem support_part_0003 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0003 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alphaDummy020)).fv) support_part_0003)

theorem support_part_0004 :
    alphaDummy020 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0004 :
    alphaDummy020 ∈
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv ∪
        ((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((synCnin (Class.cv alphaDummy019) (Class.cv alphaDummy020))).fv) support_part_0004)

theorem support_part_0005 : alphaDummy020 ∈ (((Class.cv alphaDummy020)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0005 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
  by exact (Finset.mem_union_right (((Class.cv alphaDummy019)).fv) support_part_0005)

theorem support_part_0006 :
    alphaDummy019 ∈ (((synCcompl (Class.cv alphaDummy019))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]

theorem support_mem_0006 :
    alphaDummy019 ∈
      (((synCcompl (Class.cv alphaDummy019))).fv ∪
        ((synCcompl (Class.cv alphaDummy020))).fv) :=
  by
  exact
    (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy020))).fv) support_part_0006)

theorem support_part_0007 : alphaDummy019 ∈ (((Class.cv alphaDummy019)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0007 :
    alphaDummy019 ∈
      (((Class.cv alphaDummy019)).fv ∪ ((Class.cv alphaDummy019)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alphaDummy019)).fv) support_part_0007)

theorem support_part_0008 :
    alphaDummy020 ∈ (((synCcompl (Class.cv alphaDummy020))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]

theorem support_mem_0008 :
    alphaDummy020 ∈
      (((synCcompl (Class.cv alphaDummy019))).fv ∪
        ((synCcompl (Class.cv alphaDummy020))).fv) :=
  by
  exact
    (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy019))).fv) support_part_0008)

theorem support_part_0009 : alphaDummy020 ∈ (((Class.cv alphaDummy020)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0009 :
    alphaDummy020 ∈
      (((Class.cv alphaDummy020)).fv ∪ ((Class.cv alphaDummy020)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alphaDummy020)).fv) support_part_0009)

theorem support_part_0010 (M : Class) :
    (alphaDummy031 M) ∈
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0010 (M : Class) :
    (alphaDummy031 M) ∈
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv ∪
        ((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv)
      (support_part_0010 M))

theorem support_part_0011 (a : Var) :
    (alphaDummy032 a) ∈ (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0011 (a : Var) :
    (alphaDummy032 a) ∈
      (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv ∪
        ((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv) :=
  by
  exact
    (Finset.mem_union_left (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv)
      (support_part_0011 a))

theorem support_part_0012 (M : Class) :
    (alphaDummy031 M) ∈ (((Class.cv (alphaDummy031 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0012 (M : Class) :
    (alphaDummy031 M) ∈
      (((Class.cv (alphaDummy031 M))).fv ∪ ((Class.cv (alphaDummy000 M))).fv) :=
  by
  exact
    (Finset.mem_union_left (((Class.cv (alphaDummy000 M))).fv) (support_part_0012 M))

theorem support_part_0013 (a : Var) :
    (alphaDummy032 a) ∈ (((Class.cv (alphaDummy032 a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0013 (a : Var) :
    (alphaDummy032 a) ∈ (((Class.cv (alphaDummy032 a))).fv ∪ ((Class.cv a)).fv) := by
  exact (Finset.mem_union_left (((Class.cv a)).fv) (support_part_0013 a))

theorem support_part_0014 (M : Class) :
    (alphaDummy000 M) ∈
      (((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c, fv_syn_cnin,
    fv_syn_cpw, eq_self, true_or]

theorem support_mem_0014 (M : Class) :
    (alphaDummy000 M) ∈
      (((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv) :=
  by
  exact
    (Finset.mem_union_left (((synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))).fv)
      (support_part_0014 M))

theorem support_part_0015 (a : Var) :
    a ∈ (((synCnin (synCpw (Class.cv a)) (synC1c))).fv) := by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c, fv_syn_cnin,
    fv_syn_cpw, eq_self, true_or]

theorem support_mem_0015 (a : Var) :
    a ∈
      (((synCnin (synCpw (Class.cv a)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv a)) (synC1c))).fv) :=
  by
  exact
    (Finset.mem_union_left (((synCnin (synCpw (Class.cv a)) (synC1c))).fv)
      (support_part_0015 a))

theorem support_part_0016 (M : Class) :
    (alphaDummy000 M) ∈ (((synCpw (Class.cv (alphaDummy000 M)))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]

theorem support_mem_0016 (M : Class) :
    (alphaDummy000 M) ∈
      (((synCpw (Class.cv (alphaDummy000 M)))).fv ∪ ((synC1c)).fv) :=
  by exact (Finset.mem_union_left (((synC1c)).fv) (support_part_0016 M))

theorem support_part_0017 (a : Var) : a ∈ (((synCpw (Class.cv a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]

theorem support_mem_0017 (a : Var) : a ∈ (((synCpw (Class.cv a))).fv ∪ ((synC1c)).fv) :=
  by exact (Finset.mem_union_left (((synC1c)).fv) (support_part_0017 a))

theorem support_part_0018 (M : Class) :
    (alphaDummy000 M) ∈ (((Class.cv (alphaDummy000 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0018 (M : Class) :
    (alphaDummy000 M) ∈ (((Class.cv (alphaDummy000 M))).fv) := by
  exact (support_part_0018 M)

theorem support_part_0019 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0019 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  exact (support_part_0019 a)

theorem support_part_0020 (M : Class) :
    (alphaDummy000 M) ∈
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0020 (M : Class) :
    (alphaDummy000 M) ∈
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv ∪
        ((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((synCnin (Class.cv (alphaDummy031 M)) (Class.cv (alphaDummy000 M)))).fv)
      (support_part_0020 M))

theorem support_part_0021 (a : Var) :
    a ∈ (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv) := by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0021 (a : Var) :
    a ∈
      (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv ∪
        ((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv) :=
  by
  exact
    (Finset.mem_union_left (((synCnin (Class.cv (alphaDummy032 a)) (Class.cv a))).fv)
      (support_part_0021 a))

theorem support_part_0022 (M : Class) :
    (alphaDummy000 M) ∈ (((Class.cv (alphaDummy000 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0022 (M : Class) :
    (alphaDummy000 M) ∈
      (((Class.cv (alphaDummy031 M))).fv ∪ ((Class.cv (alphaDummy000 M))).fv) :=
  by
  exact
    (Finset.mem_union_right (((Class.cv (alphaDummy031 M))).fv) (support_part_0022 M))

theorem support_part_0023 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0023 (a : Var) :
    a ∈ (((Class.cv (alphaDummy032 a))).fv ∪ ((Class.cv a)).fv) := by
  exact
    (Finset.mem_union_right (((Class.cv (alphaDummy032 a))).fv) (support_part_0023 a))

theorem support_part_0024 (M : Class) :
    (alphaDummy008 M) ∈ (((Class.cv (alphaDummy008 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0024 (M : Class) :
    (alphaDummy008 M) ∈ (((Class.cv (alphaDummy008 M))).fv) := by
  exact (support_part_0024 M)

theorem support_part_0025 (n : Var) (M : Class) (a : Var) :
    (alphaDummy009 n M a) ∈ (((Class.cv (alphaDummy009 n M a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0025 (n : Var) (M : Class) (a : Var) :
    (alphaDummy009 n M a) ∈ (((Class.cv (alphaDummy009 n M a))).fv) := by
  exact (support_part_0025 n M a)

/-- Predicate whose restricted existential retains every free parameter variable. -/
@[expose]
def finitePredicate (n : Var) (M : Class) (a : Var) : Wff :=
  synWa (.classMem (.cv n) synCnnc)
    (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))

/-- The singleton-encoding class used in the finite-type alpha certificate. -/
@[expose]
def codingClass (outer n : Var) (M : Class) (a : Var) : Class :=
  .cab outer (.classEq (.cab n (finitePredicate n M a)) (synCsn (.cv outer)))

theorem parameter_subset_predicate (n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv) :
    M.fv ⊆ (finitePredicate n M a).fv :=
  by
  rw [finitePredicate, fv_syn_wa, fv_syn_wrex]
  intro u hu
  exact
    Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hu), hu⟩))

theorem parameter_subset_codingClass (outer n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv)
    (hn : n ∉ M.fv) (houter : outer ∉ ({ n } ∪ (finitePredicate n M a).fv)) :
    M.fv ⊆ (codingClass outer n M a).fv :=
  by
  have hpredicate := parameter_subset_predicate n M a ha
  have houterParameter : outer ∉ M.fv := fun hu =>
    houter (Finset.mem_union_right _ (hpredicate hu))
  rw [codingClass, fv_class_cab, fv_wff_classEq, fv_class_cab]
  exact
    subset_erase_of_subset_of_not_mem
      (fun u hu =>
        Finset.mem_union_left _ ((subset_erase_of_subset_of_not_mem hpredicate hn) hu))
      houterParameter

theorem outerVariablesFresh (n : Var) (M : Class) (a : Var) :
    TEnvFresh [(alphaDummy002 M, alphaDummy003 n M a)] M.fv :=
  by
  have hsubset :
    M.fv ⊆
      (Wff.classEq M synC0).fv ∪ synC0.fv ∪
        (synCio (alphaDummy001 M)
            (finitePredicate (alphaDummy001 M) M (alphaDummy000 M))).fv :=
    by
    rw [fv_wff_classEq]
    exact fun u hu =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hsubset' :
    M.fv ⊆
      (Wff.classEq M synC0).fv ∪ synC0.fv ∪ (synCio n (finitePredicate n M a)).fv :=
    by
    rw [fv_wff_classEq]
    exact fun u hu =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  exact
    TEnvFresh.cons (fun hu => fresh_025 M (hsubset hu))
      (fun hu => fresh_026 n M a (hsubset' hu)) (by simp [TEnvFresh])

theorem allVariablesFresh (n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv)
    (hn : n ∉ M.fv) :
    TEnvFresh
      [(alphaDummy000 M, a), (alphaDummy001 M, n),
        (alphaDummy008 M, alphaDummy009 n M a),
        (alphaDummy011 M, alphaDummy013 n M a),
        (alphaDummy010 M, alphaDummy012 n M a),
        (alphaDummy002 M, alphaDummy003 n M a)]
      M.fv :=
  by
  have hleft :=
    parameter_subset_predicate (alphaDummy001 M) M (alphaDummy000 M) (fresh_039 M)
  have hright := parameter_subset_predicate n M a ha
  have hleftCode :=
    parameter_subset_codingClass (alphaDummy008 M) (alphaDummy001 M) M
      (alphaDummy000 M) (fresh_039 M) (fresh_040 M) (fresh_042 M)
  have hrightCode :=
    parameter_subset_codingClass (alphaDummy009 n M a) n M a ha hn (fresh_043 n M a)
  exact
    TEnvFresh.cons (fresh_039 M) ha
      (TEnvFresh.cons (fresh_040 M) hn
        (TEnvFresh.cons (fun hu => fresh_042 M (Finset.mem_union_right _ (hleft hu)))
          (fun hu => fresh_043 n M a (Finset.mem_union_right _ (hright hu)))
          (TEnvFresh.cons (fun hu => fresh_004 M (hleftCode hu))
            (fun hu => fresh_007 n M a (hrightCode hu))
            (TEnvFresh.cons (fun hu => fresh_003 M (hleftCode hu))
              (fun hu => fresh_006 n M a (hrightCode hu)) (outerVariablesFresh n M a)))))

end FiniteTypeAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
