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
    (nb076_alpha_dummy_002) ∈
      (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
              (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0177 (g : Var) (a : Var) (b : Var) :
    g ∈
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show g ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0178 :
    (nb076_alpha_dummy_002) ∈
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv) :=
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
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) :=
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
    (nb076_alpha_dummy_002) ∈
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) :=
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
    (nb076_alpha_dummy_082) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0183 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_084 g a b) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0184 :
    (nb076_alpha_dummy_082) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0185 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_084 g a b) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_compact_fv_empty_0028 : (nb076_alpha_dummy_005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0029 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0030 : (nb076_alpha_dummy_004) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0031 (n : Var) : n ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0032 : (nb076_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0033 (m : Var) : m ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0034 : (nb076_alpha_dummy_007) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0035 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_008 g m n a b) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
