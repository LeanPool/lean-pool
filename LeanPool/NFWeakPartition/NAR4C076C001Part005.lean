/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block001

/-! NF weak partition development: NAR4C076C001Part005. -/


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

theorem nb076_support_mem_0176 :
    (nb076AlphaDummy002) ∈
      (((Class.cab (nb076AlphaDummy081) (synWrex (nb076AlphaDummy082)
              (synCxp (Class.cv (nb076AlphaDummy001)) (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy081)
            (synWrex (nb076AlphaDummy082) (synCxp (Class.cv (nb076AlphaDummy001))
                (Class.cv (nb076AlphaDummy002)))
              (Wff.classEq (Class.cv (nb076AlphaDummy081))
                (synCun (synCphi (Class.cv (nb076AlphaDummy082)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy081) from (by
          unfold nb076AlphaDummy081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076AlphaDummy002) ≠ (nb076AlphaDummy082) from (by
            unfold nb076AlphaDummy082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0177 (g : Var) (a : Var) (b : Var) :
    g ∈
      (((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb076AlphaDummy083 g a b)
            (synWrex (nb076AlphaDummy084 g a b) (synCxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076AlphaDummy083 g a b))
                (synCun (synCphi (Class.cv (nb076AlphaDummy084 g a b)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb076AlphaDummy083 g a b) from (by
          unfold nb076AlphaDummy083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show g ≠ (nb076AlphaDummy084 g a b) from (by
            unfold nb076AlphaDummy084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0178 :
    (nb076AlphaDummy002) ∈
      (({(nb076AlphaDummy113)} : Finset Var) ∪ ({(nb076AlphaDummy114)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy113))
              (Class.cv (nb076AlphaDummy001)))
            (Wff.classMem (Class.cv (nb076AlphaDummy114))
              (Class.cv (nb076AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0179 (g : Var) (b : Var) :
    g ∈
      (({(nb076AlphaDummy115 g b)} : Finset Var) ∪
          ({(nb076AlphaDummy116 g b)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv (nb076AlphaDummy115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076AlphaDummy116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0180 :
    (nb076AlphaDummy002) ∈
      (((Class.cv (nb076AlphaDummy001))).fv ∪ ((Class.cv (nb076AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0181 (g : Var) (b : Var) :
    g ∈ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0182 :
    (nb076AlphaDummy082) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy082))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0183 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy084 g a b) ∈
      (((synCcompl (synCphi (Class.cv (nb076AlphaDummy084 g a b))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0184 :
    (nb076AlphaDummy082) ∈
      (((synCphi (Class.cv (nb076AlphaDummy082)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy082)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0185 (g : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy084 g a b) ∈
      (((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv ∪
        ((synCphi (Class.cv (nb076AlphaDummy084 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_compact_fv_empty_0028 : (nb076AlphaDummy005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0030 : (nb076AlphaDummy004) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0031 (n : Var) : n ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0032 : (nb076AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0033 (m : Var) : m ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0034 : (nb076AlphaDummy007) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0035 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy008 g m n a b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
