/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brpprod`. -/
@[expose]
noncomputable def gBrpprod (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (B : Class) (R : Class) (S : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_w : w ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_S_w : w ∉ S.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWbr A (synCpprod R S) B) (synWex x (synWex y (synWex z (synWex w
                (synW3a (.classEq A (synCop (.cv x) (.cv y)))
                  (.classEq B (synCop (.cv z) (.cv w))) (synWa (synWbr (.cv x) R (.cv z))
                    (synWbr (.cv y) S (.cv w))))))))) :=
  by
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_w, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCcom R (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, dv_R_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((synCcom R (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, dv_R_w,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCcom S (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_S_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((synCcom S (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_S_w,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact Ne.symm dv_w_z))
  have dv_cache_0010 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((synWbr A (synCcom S (synC2nd)) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_w_x), dv_S_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0017 : y ∉ ((synWbr A (synCcom S (synC2nd)) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_w_y), dv_S_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((synWbr (.cv x) R (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_y_z, dv_R_y, or_false,
          not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Wff.classEq B (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_B_x, dv_x_z, (Ne.symm dv_w_x), or_false,
          not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Wff.classEq B (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_B_y, dv_y_z, (Ne.symm dv_w_y), or_false,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCpprod R S))
  have p0001 :=
    @gBreqi A B (synCpprod R S)
      (synCtxp (synCcom R (synC1st)) (synCcom S (synC2nd))) p0000
  have p0002 :=
    @gBrtxp z w A B (synCcom R (synC1st)) (synCcom S (synC2nd)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0003 :=
    @gBrco x A (.cv z) R (synC1st) dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0004 :=
    @gAnbi1i (synWbr A (synCcom R (synC1st)) (.cv z))
      (synWex x (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z))))
      (synWbr A (synCcom S (synC2nd)) (.cv w)) p0003
  have p0005 :=
    @gN1941v (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z)))
      (synWbr A (synCcom S (synC2nd)) (.cv w)) x dv_cache_0014
  have p0006 :=
    @gAn32 (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z))
      (synWbr A (synCcom S (synC2nd)) (.cv w))
  have p0007 := @gVex x
  have p0008 := @gBr1st y A (.cv x) dv_cache_0015 dv_cache_0016 p0007
  have p0009 :=
    @gAnbi1i (synWbr A (synC1st) (.cv x))
      (synWex y (.classEq A (synCop (.cv x) (.cv y))))
      (synWbr A (synCcom S (synC2nd)) (.cv w)) p0008
  have p0010 :=
    @gN1941v (.classEq A (synCop (.cv x) (.cv y)))
      (synWbr A (synCcom S (synC2nd)) (.cv w)) y dv_cache_0017
  have p0011 := @gBreq1 A (synCop (.cv x) (.cv y)) (.cv w) (synCcom S (synC2nd))
  have p0012 := @gVex y
  have p0013 := @gBrco2nd (.cv x) (.cv y) (.cv w) S p0007 p0012
  have p0014 :=
    @gSyl6bb (.classEq A (synCop (.cv x) (.cv y)))
      (synWbr A (synCcom S (synC2nd)) (.cv w))
      (synWbr (synCop (.cv x) (.cv y)) (synCcom S (synC2nd)) (.cv w))
      (synWbr (.cv y) S (.cv w)) p0011 p0013
  have p0015 :=
    @gPm532i (.classEq A (synCop (.cv x) (.cv y)))
      (synWbr A (synCcom S (synC2nd)) (.cv w)) (synWbr (.cv y) S (.cv w)) p0014
  have p0016 :=
    @gExbii
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w))) y p0015
  have p0017 :=
    @gN3bitr2i
      (synWa (synWbr A (synC1st) (.cv x)) (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWa (synWex y (.classEq A (synCop (.cv x) (.cv y))))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWbr A (synCcom S (synC2nd)) (.cv w))))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w))))
      p0009 p0010 p0016
  have p0018 :=
    @gAnbi1i
      (synWa (synWbr A (synC1st) (.cv x)) (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w))))
      (synWbr (.cv x) R (.cv z)) p0017
  have p0019 :=
    @gAnass (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv x) R (.cv z))
      (synWbr (.cv y) S (.cv w))
  have p0020 :=
    @gAn32 (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv x) R (.cv z))
      (synWbr (.cv y) S (.cv w))
  have p0021 :=
    @gBitr3i
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synWa (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv x) R (.cv z)))
        (synWbr (.cv y) S (.cv w)))
      (synWa (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w)))
        (synWbr (.cv x) R (.cv z)))
      p0019 p0020
  have p0022 :=
    @gExbii
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synWa (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w)))
        (synWbr (.cv x) R (.cv z)))
      y p0021
  have p0023 :=
    @gN1941v
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w)))
      (synWbr (.cv x) R (.cv z)) y dv_cache_0018
  have p0024 :=
    @gBitr2i
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))
      (synWex y (synWa
          (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w)))
          (synWbr (.cv x) R (.cv z))))
      (synWa (synWex y
          (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w))))
        (synWbr (.cv x) R (.cv z)))
      p0022 p0023
  have p0025 :=
    @gN3bitri
      (synWa (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z)))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWa (synWa (synWbr A (synC1st) (.cv x))
          (synWbr A (synCcom S (synC2nd)) (.cv w))) (synWbr (.cv x) R (.cv z)))
      (synWa (synWex y
          (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) S (.cv w))))
        (synWbr (.cv x) R (.cv z)))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))
      p0006 p0018 p0024
  have p0026 :=
    @gExbii
      (synWa (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z)))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))
      x p0025
  have p0027 :=
    @gN3bitr2i
      (synWa (synWbr A (synCcom R (synC1st)) (.cv z))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWa (synWex x (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z))))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex x (synWa (synWa (synWbr A (synC1st) (.cv x)) (synWbr (.cv x) R (.cv z)))
          (synWbr A (synCcom S (synC2nd)) (.cv w))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))
      p0004 p0005 p0026
  have p0028 :=
    @gAnbi2i
      (synWa (synWbr A (synCcom R (synC1st)) (.cv z))
        (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))
      (.classEq B (synCop (.cv z) (.cv w))) p0027
  have p0029 :=
    @gN3anass (.classEq B (synCop (.cv z) (.cv w)))
      (synWbr A (synCcom R (synC1st)) (.cv z))
      (synWbr A (synCcom S (synC2nd)) (.cv w))
  have p0030 :=
    @gN3ancoma (.classEq A (synCop (.cv x) (.cv y)))
      (.classEq B (synCop (.cv z) (.cv w)))
      (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))
  have p0031 :=
    @gN3anass (.classEq B (synCop (.cv z) (.cv w)))
      (.classEq A (synCop (.cv x) (.cv y)))
      (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))
  have p0032 :=
    @gBitri
      (synW3a (.classEq A (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synW3a (.classEq B (synCop (.cv z) (.cv w))) (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synWa (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))
      p0030 p0031
  have p0033 :=
    @gN2exbii
      (synW3a (.classEq A (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      (synWa (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))
      x y p0032
  have p0034 :=
    @gN1942vv (.classEq B (synCop (.cv z) (.cv w)))
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      x y dv_cache_0019 dv_cache_0020
  have p0035 :=
    @gBitri
      (synWex x (synWex y (synW3a (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv z) (.cv w)))
            (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))
      (synWex x (synWex y (synWa (.classEq B (synCop (.cv z) (.cv w)))
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))))
      (synWa (.classEq B (synCop (.cv z) (.cv w))) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))))
      p0033 p0034
  have p0036 :=
    @gN3bitr4i
      (synWa (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (synWbr A (synCcom R (synC1st)) (.cv z))
          (synWbr A (synCcom S (synC2nd)) (.cv w))))
      (synWa (.classEq B (synCop (.cv z) (.cv w))) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w)))))))
      (synW3a (.classEq B (synCop (.cv z) (.cv w)))
        (synWbr A (synCcom R (synC1st)) (.cv z)) (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex x (synWex y (synW3a (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv z) (.cv w)))
            (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))
      p0028 p0029 p0035
  have p0037 :=
    @gN2exbii
      (synW3a (.classEq B (synCop (.cv z) (.cv w)))
        (synWbr A (synCcom R (synC1st)) (.cv z)) (synWbr A (synCcom S (synC2nd)) (.cv w)))
      (synWex x (synWex y (synW3a (.classEq A (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv z) (.cv w)))
            (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))
      z w p0036
  have p0038 :=
    @gExrot4
      (synW3a (.classEq A (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv z) (.cv w)))
        (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))
      z w x y
  have p0039 :=
    @gBitri
      (synWex z (synWex w (synW3a (.classEq B (synCop (.cv z) (.cv w)))
            (synWbr A (synCcom R (synC1st)) (.cv z))
            (synWbr A (synCcom S (synC2nd)) (.cv w)))))
      (synWex z (synWex w (synWex x (synWex y
              (synW3a (.classEq A (synCop (.cv x) (.cv y)))
                (.classEq B (synCop (.cv z) (.cv w)))
                (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))))
      (synWex x (synWex y (synWex z (synWex w
              (synW3a (.classEq A (synCop (.cv x) (.cv y)))
                (.classEq B (synCop (.cv z) (.cv w)))
                (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))))
      p0037 p0038
  have p0040 :=
    @gN3bitri (synWbr A (synCpprod R S) B)
      (synWbr A (synCtxp (synCcom R (synC1st)) (synCcom S (synC2nd))) B)
      (synWex z (synWex w (synW3a (.classEq B (synCop (.cv z) (.cv w)))
            (synWbr A (synCcom R (synC1st)) (.cv z))
            (synWbr A (synCcom S (synC2nd)) (.cv w)))))
      (synWex x (synWex y (synWex z (synWex w
              (synW3a (.classEq A (synCop (.cv x) (.cv y)))
                (.classEq B (synCop (.cv z) (.cv w)))
                (synWa (synWbr (.cv x) R (.cv z)) (synWbr (.cv y) S (.cv w))))))))
      p0001 p0002 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dmpprod`. -/
@[expose]
noncomputable def gDmpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCdm (synCpprod A B)) (synCxp (synCdm A) (synCdm B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let c : Var := freshVar proofSupport 3
  let d : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let u : Var := freshVar proofSupport 6
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_u : a ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_u : b ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_t : c ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_c : t ≠ c := Ne.symm fresh_c_ne_t
  have fresh_c_ne_u : c ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_u_ne_c : u ≠ c := Ne.symm fresh_c_ne_u
  have fresh_d_ne_t : d ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_d : t ≠ d := Ne.symm fresh_d_ne_t
  have fresh_d_ne_u : d ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_u_ne_d : u ≠ d := Ne.symm fresh_d_ne_u
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : x ∉ ((synCop (.cv c) (.cv d))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d, or_false, not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_c, fresh_x_not_A, fresh_x_ne_b,
          fresh_x_ne_d, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCpprod A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((synCop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_b, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b, or_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((synCop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_a, fresh_u_ne_b, or_false, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((synCop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0013 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0014 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0015 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0016 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0017 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0018 : t ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0019 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0020 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_B, not_false_eq_true])
  have dv_cache_0021 : d ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0022 : d ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show d ≠ u from (by exact fresh_d_ne_u))
  have dv_cache_0023 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0024 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0025 : t ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show t ≠ c from (by exact fresh_t_ne_c))
  have dv_cache_0026 : u ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0027 : c ∉ ((synWa (.objEq t a) (.objEq u b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_t, fresh_c_ne_a, fresh_c_ne_u, fresh_c_ne_b,
          or_false, not_false_eq_true])
  have dv_cache_0028 : d ∉ ((synWa (.objEq t a) (.objEq u b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_t, fresh_d_ne_a, fresh_d_ne_u, fresh_d_ne_b,
          or_false, not_false_eq_true])
  have dv_cache_0029 : c ∉ ((Wff.objEq t a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_t, fresh_c_ne_a, or_false, not_false_eq_true])
  have dv_cache_0030 : d ∉ ((Wff.objEq t a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_t, fresh_d_ne_a, or_false, not_false_eq_true])
  have dv_cache_0031 : c ∉ ((Wff.objEq u b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_u, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0032 : d ∉ ((Wff.objEq u b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_u, fresh_d_ne_b, or_false, not_false_eq_true])
  have dv_cache_0033 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0034 : u ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_a, not_false_eq_true])
  have dv_cache_0035 : t ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_b, not_false_eq_true])
  have dv_cache_0036 : u ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_b, not_false_eq_true])
  have dv_cache_0037 :
    u ∉
      ((synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_c,
          fresh_u_ne_d, fresh_u_ne_a, fresh_u_not_A, fresh_u_ne_b, fresh_u_not_B,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0038 :
    t ∉
      ((synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_c,
          fresh_t_ne_d, fresh_t_ne_a, fresh_t_not_A, fresh_t_ne_u, fresh_t_not_B,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0039 : c ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_a, not_false_eq_true])
  have dv_cache_0040 : d ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_b, not_false_eq_true])
  have dv_cache_0041 : d ∉ ((synWbr (.cv a) A (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_c, fresh_d_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0042 : c ∉ ((synWbr (.cv b) B (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_d, fresh_c_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0043 : a ∉ ((synCdm (synCpprod A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true])
  have dv_cache_0044 : b ∉ ((synCdm (synCpprod A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true])
  have dv_cache_0045 : a ∉ ((synCxp (synCdm A) (synCdm B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true])
  have dv_cache_0046 : b ∉ ((synCxp (synCdm A) (synCdm B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true])
  have dv_cache_0047 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 := @gVex c
  have p0001 := @gVex d
  have p0002 := @gOpex (.cv c) (.cv d) p0000 p0001
  have p0003 := @gIsseti x (synCop (.cv c) (.cv d)) dv_cache_0001 p0002
  have p0004 :=
    @gN1941v (.classEq (.cv x) (synCop (.cv c) (.cv d)))
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))) x dv_cache_0002
  have p0005 :=
    @gMpbiran
      (synWex x (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))
      (synWex x (.classEq (.cv x) (synCop (.cv c) (.cv d))))
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))) p0003 p0004
  have p0006 :=
    @gN2exbii
      (synWex x (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))) c d p0005
  have p0007 := (Nominal.biimpRefl (synWbr (.cv a) (synCdm (synCpprod A B)) (.cv b)))
  have p0008 :=
    @gEldm x (synCop (.cv a) (.cv b)) (synCpprod A B) dv_cache_0003 dv_cache_0004
  have p0009 :=
    @gBrpprod t u c d (synCop (.cv a) (.cv b)) (.cv x) A B dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026
  have p0010 :=
    @gN1942vv (synWa (.objEq t a) (.objEq u b))
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      c d dv_cache_0027 dv_cache_0028
  have p0011 :=
    @gN3anass (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
      (.classEq (.cv x) (synCop (.cv c) (.cv d)))
      (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))
  have p0012 := @gEqcom (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u))
  have p0013 := @gOpth (.cv t) (.cv u) (.cv a) (.cv b)
  have p0014_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv t) (.cv u)) (synCop (.cv a) (.cv b)))
        (synWa (.objEq t a) (.objEq u b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gBitri (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
      (.classEq (synCop (.cv t) (.cv u)) (synCop (.cv a) (.cv b)))
      (synWa (.objEq t a) (.objEq u b)) p0012 p0014_e01_recanon
  have p0015 :=
    @gAnbi1i (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
      (synWa (.objEq t a) (.objEq u b))
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      p0014
  have p0016 :=
    @gBitri
      (synW3a (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
        (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      (synWa (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
        (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))
      (synWa (synWa (.objEq t a) (.objEq u b))
        (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))
      p0011 p0015
  have p0017 :=
    @gN2exbii
      (synW3a (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
        (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      (synWa (synWa (.objEq t a) (.objEq u b))
        (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))
      c d p0016
  have p0018 :=
    (Nominal.biimpRefl (synW3a (.objEq t a) (.objEq u b) (synWex c (synWex d
            (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))))))
  have p0019 :=
    @gN3bitr4i
      (synWex c (synWex d (synWa (synWa (.objEq t a) (.objEq u b))
            (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))
      (synWa (synWa (.objEq t a) (.objEq u b)) (synWex c (synWex d
            (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))
      (synWex c (synWex d
          (synW3a (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
            (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))))
      (synW3a (.objEq t a) (.objEq u b) (synWex c (synWex d
            (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))
      p0010 p0017 p0018
  have p0020 :=
    @gN2exbii
      (synWex c (synWex d
          (synW3a (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
            (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))))
      (synW3a (.objEq t a) (.objEq u b) (synWex c (synWex d
            (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))
      t u p0019
  have p0021 := @gVex a
  have p0022 := @gVex b
  have p0023 := @gBreq1 (.cv t) (.cv a) (.cv c) A
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq t a) (synWb (synWbr (.cv t) A (.cv c)) (synWbr (.cv a) A (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0023
  have p0024 :=
    @gAnbi1d (.objEq t a) (synWbr (.cv t) A (.cv c)) (synWbr (.cv a) A (.cv c))
      (synWbr (.cv u) B (.cv d)) p0024_e00_recanon
  have p0025 :=
    @gAnbi2d (.objEq t a)
      (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d)))
      (.classEq (.cv x) (synCop (.cv c) (.cv d))) p0024
  have p0026 :=
    @gN2exbidv (.objEq t a)
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      c d dv_cache_0029 dv_cache_0030 p0025
  have p0027 := @gBreq1 (.cv u) (.cv b) (.cv d) B
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq u b) (synWb (synWbr (.cv u) B (.cv d)) (synWbr (.cv b) B (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0028 :=
    @gAnbi2d (.objEq u b) (synWbr (.cv u) B (.cv d)) (synWbr (.cv b) B (.cv d))
      (synWbr (.cv a) A (.cv c)) p0028_e00_recanon
  have p0029 :=
    @gAnbi2d (.objEq u b)
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d)))
      (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))
      (.classEq (.cv x) (synCop (.cv c) (.cv d))) p0028
  have p0030 :=
    @gN2exbidv (.objEq u b)
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d))))
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))
      c d dv_cache_0031 dv_cache_0032 p0029
  have p0031_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (.cv a)) (synWb (synWex c (synWex d
              (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))) (synWex c
            (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0031_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv u) (.cv b)) (synWb (synWex c (synWex d
              (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d)))))) (synWex c
            (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @gCeqsex2v
      (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))))
      (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv u) B (.cv d))))))
      (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))))
      t u (.cv a) (.cv b) dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
      dv_cache_0037 dv_cache_0038 dv_cache_0024 p0021 p0022 p0031_e02_recanon
      p0031_e03_recanon
  have p0032_e02_recanon :
    Nominal.NPrf
      (synWb (synWex t (synWex u (synW3a (.objEq t a) (.objEq u b) (synWex c (synWex d
                  (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                    (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))))
        (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gN3bitri (synWbr (synCop (.cv a) (.cv b)) (synCpprod A B) (.cv x))
      (synWex t (synWex u (synWex c (synWex d
              (synW3a (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv t) (.cv u)))
                (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d))))))))
      (synWex t (synWex u (synW3a (.objEq t a) (.objEq u b) (synWex c (synWex d
                (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
                  (synWa (synWbr (.cv t) A (.cv c)) (synWbr (.cv u) B (.cv d)))))))))
      (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))))
      p0009 p0020 p0032_e02_recanon
  have p0033 :=
    @gExbii (synWbr (synCop (.cv a) (.cv b)) (synCpprod A B) (.cv x))
      (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))))
      x p0032
  have p0034 :=
    @gExrot3
      (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d))))
      x c d
  have p0035 :=
    @gBitri (synWex x (synWbr (synCop (.cv a) (.cv b)) (synCpprod A B) (.cv x)))
      (synWex x (synWex c (synWex d (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))))
      (synWex c (synWex d (synWex x (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))))
      p0033 p0034
  have p0036 :=
    @gN3bitri (synWbr (.cv a) (synCdm (synCpprod A B)) (.cv b))
      (.classMem (synCop (.cv a) (.cv b)) (synCdm (synCpprod A B)))
      (synWex x (synWbr (synCop (.cv a) (.cv b)) (synCpprod A B) (.cv x)))
      (synWex c (synWex d (synWex x (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))))
      p0007 p0008 p0035
  have p0037 := @gEldm c (.cv a) A dv_cache_0039 dv_cache_0016
  have p0038 := @gEldm d (.cv b) B dv_cache_0040 dv_cache_0017
  have p0039 :=
    @gAnbi12i (.classMem (.cv a) (synCdm A)) (synWex c (synWbr (.cv a) A (.cv c)))
      (.classMem (.cv b) (synCdm B)) (synWex d (synWbr (.cv b) B (.cv d))) p0037 p0038
  have p0040 := @gBrxp (.cv a) (.cv b) (synCdm A) (synCdm B)
  have p0041 :=
    @gEeanv (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)) c d dv_cache_0041
      dv_cache_0042
  have p0042 :=
    @gN3bitr4i (synWa (.classMem (.cv a) (synCdm A)) (.classMem (.cv b) (synCdm B)))
      (synWa (synWex c (synWbr (.cv a) A (.cv c))) (synWex d (synWbr (.cv b) B (.cv d))))
      (synWbr (.cv a) (synCxp (synCdm A) (synCdm B)) (.cv b))
      (synWex c (synWex d (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))
      p0039 p0040 p0041
  have p0043 :=
    @gN3bitr4i
      (synWex c (synWex d (synWex x (synWa (.classEq (.cv x) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))))
      (synWex c (synWex d (synWa (synWbr (.cv a) A (.cv c)) (synWbr (.cv b) B (.cv d)))))
      (synWbr (.cv a) (synCdm (synCpprod A B)) (.cv b))
      (synWbr (.cv a) (synCxp (synCdm A) (synCdm B)) (.cv b)) p0006 p0036 p0042
  have p0044 :=
    @gEqbrriv a b (synCdm (synCpprod A B)) (synCxp (synCdm A) (synCdm B))
      dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cnvpprod`. -/
@[expose]
noncomputable def gCnvpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCpprod A B)) (synCpprod (synCcnv A) (synCcnv B))) :=
  by
  have p0000 :=
    @gCnvin (synCcom (synCcnv (synC1st)) (synCcom A (synC1st)))
      (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd)))
  have p0001 := @gCnvco (synCcnv (synC1st)) (synCcom A (synC1st))
  have p0002 := @gCnvco A (synC1st)
  have p0003 := @gCnvcnv (synC1st)
  have p0004 :=
    @gCoeq12i (synCcnv (synCcom A (synC1st)))
      (synCcom (synCcnv (synC1st)) (synCcnv A)) (synCcnv (synCcnv (synC1st)))
      (synC1st) p0002 p0003
  have p0005 := @gCoass (synCcnv (synC1st)) (synCcnv A) (synC1st)
  have p0006 :=
    @gN3eqtri (synCcnv (synCcom (synCcnv (synC1st)) (synCcom A (synC1st))))
      (synCcom (synCcnv (synCcom A (synC1st))) (synCcnv (synCcnv (synC1st))))
      (synCcom (synCcom (synCcnv (synC1st)) (synCcnv A)) (synC1st))
      (synCcom (synCcnv (synC1st)) (synCcom (synCcnv A) (synC1st))) p0001 p0004
      p0005
  have p0007 := @gCnvco (synCcnv (synC2nd)) (synCcom B (synC2nd))
  have p0008 := @gCnvco B (synC2nd)
  have p0009 := @gCnvcnv (synC2nd)
  have p0010 :=
    @gCoeq12i (synCcnv (synCcom B (synC2nd)))
      (synCcom (synCcnv (synC2nd)) (synCcnv B)) (synCcnv (synCcnv (synC2nd)))
      (synC2nd) p0008 p0009
  have p0011 := @gCoass (synCcnv (synC2nd)) (synCcnv B) (synC2nd)
  have p0012 :=
    @gN3eqtri (synCcnv (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd))))
      (synCcom (synCcnv (synCcom B (synC2nd))) (synCcnv (synCcnv (synC2nd))))
      (synCcom (synCcom (synCcnv (synC2nd)) (synCcnv B)) (synC2nd))
      (synCcom (synCcnv (synC2nd)) (synCcom (synCcnv B) (synC2nd))) p0007 p0010
      p0011
  have p0013 :=
    @gIneq12i (synCcnv (synCcom (synCcnv (synC1st)) (synCcom A (synC1st))))
      (synCcom (synCcnv (synC1st)) (synCcom (synCcnv A) (synC1st)))
      (synCcnv (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd))))
      (synCcom (synCcnv (synC2nd)) (synCcom (synCcnv B) (synC2nd))) p0006 p0012
  have p0014 :=
    @gEqtri
      (synCcnv (synCin (synCcom (synCcnv (synC1st)) (synCcom A (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd)))))
      (synCin (synCcnv (synCcom (synCcnv (synC1st)) (synCcom A (synC1st))))
        (synCcnv (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd)))))
      (synCin (synCcom (synCcnv (synC1st)) (synCcom (synCcnv A) (synC1st)))
        (synCcom (synCcnv (synC2nd)) (synCcom (synCcnv B) (synC2nd))))
      p0000 p0013
  have p0015 := (Nominal.classEqRefl (synCpprod A B))
  have p0016 :=
    (Nominal.classEqRefl (synCtxp (synCcom A (synC1st)) (synCcom B (synC2nd))))
  have p0017 :=
    @gEqtri (synCpprod A B) (synCtxp (synCcom A (synC1st)) (synCcom B (synC2nd)))
      (synCin (synCcom (synCcnv (synC1st)) (synCcom A (synC1st)))
        (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd))))
      p0015 p0016
  have p0018 :=
    @gCnveqi (synCpprod A B)
      (synCin (synCcom (synCcnv (synC1st)) (synCcom A (synC1st)))
        (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd))))
      p0017
  have p0019 := (Nominal.classEqRefl (synCpprod (synCcnv A) (synCcnv B)))
  have p0020 :=
    (Nominal.classEqRefl
      (synCtxp (synCcom (synCcnv A) (synC1st)) (synCcom (synCcnv B) (synC2nd))))
  have p0021 :=
    @gEqtri (synCpprod (synCcnv A) (synCcnv B))
      (synCtxp (synCcom (synCcnv A) (synC1st)) (synCcom (synCcnv B) (synC2nd)))
      (synCin (synCcom (synCcnv (synC1st)) (synCcom (synCcnv A) (synC1st)))
        (synCcom (synCcnv (synC2nd)) (synCcom (synCcnv B) (synC2nd))))
      p0019 p0020
  have p0022 :=
    @gN3eqtr4i
      (synCcnv (synCin (synCcom (synCcnv (synC1st)) (synCcom A (synC1st)))
          (synCcom (synCcnv (synC2nd)) (synCcom B (synC2nd)))))
      (synCin (synCcom (synCcnv (synC1st)) (synCcom (synCcnv A) (synC1st)))
        (synCcom (synCcnv (synC2nd)) (synCcom (synCcnv B) (synC2nd))))
      (synCcnv (synCpprod A B)) (synCpprod (synCcnv A) (synCcnv B)) p0014 p0018 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_rnpprod`. -/
@[expose]
noncomputable def gRnpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCrn (synCpprod A B)) (synCxp (synCrn A) (synCrn B))) :=
  by
  have p0000 := @gCnvpprod A B
  have p0001 :=
    @gDmeqi (synCcnv (synCpprod A B)) (synCpprod (synCcnv A) (synCcnv B)) p0000
  have p0002 := @gDmpprod (synCcnv A) (synCcnv B)
  have p0003 :=
    @gEqtri (synCdm (synCcnv (synCpprod A B)))
      (synCdm (synCpprod (synCcnv A) (synCcnv B)))
      (synCxp (synCdm (synCcnv A)) (synCdm (synCcnv B))) p0001 p0002
  have p0004 := @gDfrn4 (synCpprod A B)
  have p0005 := @gDfrn4 A
  have p0006 := @gDfrn4 B
  have p0007 :=
    @gXpeq12i (synCrn A) (synCdm (synCcnv A)) (synCrn B) (synCdm (synCcnv B)) p0005
      p0006
  have p0008 :=
    @gN3eqtr4i (synCdm (synCcnv (synCpprod A B)))
      (synCxp (synCdm (synCcnv A)) (synCdm (synCcnv B))) (synCrn (synCpprod A B))
      (synCxp (synCrn A) (synCrn B)) p0003 p0004 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fnpprod`. -/
@[expose]
noncomputable def gFnpprod (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWfn G B)) (synWfn (synCpprod F G) (synCxp A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let e : Var := freshVar proofSupport 7
  let f : Var := freshVar proofSupport 8
  let g : Var := freshVar proofSupport 9
  let h : Var := freshVar proofSupport 10
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_G : c ∉ G.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_G : e ∉ G.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_G : f ∉ G.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_G : g ∉ G.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_h_not_F : h ∉ F.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_G : h ∉ G.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_e : x ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_g_ne_x : g ≠ x := Ne.symm fresh_x_ne_g
  have fresh_x_ne_h : x ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
  have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_y_ne_e : y ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_e_ne_y : e ≠ y := Ne.symm fresh_y_ne_e
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_ne_h : y ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_z : d ≠ z := Ne.symm fresh_z_ne_d
  have fresh_z_ne_e : z ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_e_ne_z : e ≠ z := Ne.symm fresh_z_ne_e
  have fresh_z_ne_f : z ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_f_ne_z : f ≠ z := Ne.symm fresh_z_ne_f
  have fresh_z_ne_g : z ≠ g :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_g_ne_z : g ≠ z := Ne.symm fresh_z_ne_g
  have fresh_z_ne_h : z ≠ h :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
  have fresh_h_ne_z : h ≠ z := Ne.symm fresh_z_ne_h
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_e : a ≠ e :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
  have fresh_a_ne_h : a ≠ h :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
  have fresh_h_ne_a : h ≠ a := Ne.symm fresh_a_ne_h
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_e : b ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
  have fresh_b_ne_f : b ≠ f :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_b_ne_g : b ≠ g :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_g_ne_b : g ≠ b := Ne.symm fresh_b_ne_g
  have fresh_b_ne_h : b ≠ h :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
  have fresh_h_ne_b : h ≠ b := Ne.symm fresh_b_ne_h
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_e : c ≠ e :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
  have fresh_c_ne_f : c ≠ f :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_f_ne_c : f ≠ c := Ne.symm fresh_c_ne_f
  have fresh_c_ne_g : c ≠ g :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_g_ne_c : g ≠ c := Ne.symm fresh_c_ne_g
  have fresh_c_ne_h : c ≠ h :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 5) (j := 10) (by decide)
  have fresh_h_ne_c : h ≠ c := Ne.symm fresh_c_ne_h
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_d_ne_f : d ≠ f :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_f_ne_d : f ≠ d := Ne.symm fresh_d_ne_f
  have fresh_d_ne_g : d ≠ g :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_g_ne_d : g ≠ d := Ne.symm fresh_d_ne_g
  have fresh_d_ne_h : d ≠ h :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 6) (j := 10) (by decide)
  have fresh_h_ne_d : h ≠ d := Ne.symm fresh_d_ne_h
  have fresh_e_ne_f : e ≠ f :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_e_ne_g : e ≠ g :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_e_ne_h : e ≠ h :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_h_ne_e : h ≠ e := Ne.symm fresh_e_ne_h
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_f_ne_h : f ≠ h :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_h_ne_f : h ≠ f := Ne.symm fresh_f_ne_h
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have dv_cache_0001 :
    f ∉
      ((synWex c (synWex d (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
              (.classEq (.cv y) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_a, fresh_f_ne_c,
          fresh_f_not_F, fresh_f_ne_b, fresh_f_ne_d, fresh_f_not_G, fresh_f_ne_x,
          fresh_f_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0002 :
    e ∉
      ((synWex c (synWex d (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
              (.classEq (.cv y) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_a, fresh_e_ne_c,
          fresh_e_not_F, fresh_e_ne_b, fresh_e_ne_d, fresh_e_not_G, fresh_e_ne_x,
          fresh_e_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0003 :
    a ∉
      ((synWex g (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
              (.classEq (.cv z) (synCop (.cv g) (.cv h)))
              (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_e, fresh_a_ne_g,
          fresh_a_not_F, fresh_a_ne_f, fresh_a_ne_h, fresh_a_not_G, fresh_a_ne_x,
          fresh_a_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 :
    b ∉
      ((synWex g (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
              (.classEq (.cv z) (synCop (.cv g) (.cv h)))
              (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_e, fresh_b_ne_g,
          fresh_b_not_F, fresh_b_ne_f, fresh_b_ne_h, fresh_b_not_G, fresh_b_ne_x,
          fresh_b_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ a from (by exact fresh_f_ne_a))
  have dv_cache_0006 : b ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show b ≠ e from (by exact fresh_b_ne_e))
  have dv_cache_0007 :
    h ∉
      ((synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
          (.classEq (.cv y) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_a, fresh_h_ne_c, fresh_h_not_F, fresh_h_ne_b,
          fresh_h_ne_d, fresh_h_not_G, fresh_h_ne_x, fresh_h_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    g ∉
      ((synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
          (.classEq (.cv y) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_a, fresh_g_ne_c, fresh_g_not_F, fresh_g_ne_b,
          fresh_g_ne_d, fresh_g_not_G, fresh_g_ne_x, fresh_g_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    c ∉
      ((synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_e, fresh_c_ne_g, fresh_c_not_F, fresh_c_ne_f,
          fresh_c_ne_h, fresh_c_not_G, fresh_c_ne_x, fresh_c_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    d ∉
      ((synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_e, fresh_d_ne_g, fresh_d_not_F, fresh_d_ne_f,
          fresh_d_ne_h, fresh_d_not_G, fresh_d_ne_x, fresh_d_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0011 : h ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show h ≠ c from (by exact fresh_h_ne_c))
  have dv_cache_0012 : d ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ g from (by exact fresh_d_ne_g))
  have dv_cache_0013 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0015 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0017 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_y, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0020 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0021 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0022 : a ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0023 : b ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_F, not_false_eq_true])
  have dv_cache_0024 : c ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_F, not_false_eq_true])
  have dv_cache_0025 : d ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_G, not_false_eq_true])
  have dv_cache_0026 : a ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_G, not_false_eq_true])
  have dv_cache_0027 : b ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_G, not_false_eq_true])
  have dv_cache_0028 : c ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_G, not_false_eq_true])
  have dv_cache_0029 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0030 : d ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0031 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0032 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0033 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0034 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0035 : h ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_x, not_false_eq_true])
  have dv_cache_0036 : e ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_x, not_false_eq_true])
  have dv_cache_0037 : f ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_x, not_false_eq_true])
  have dv_cache_0038 : g ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_x, not_false_eq_true])
  have dv_cache_0039 : h ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_z, not_false_eq_true])
  have dv_cache_0040 : e ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_z, not_false_eq_true])
  have dv_cache_0041 : f ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_z, not_false_eq_true])
  have dv_cache_0042 : g ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_z, not_false_eq_true])
  have dv_cache_0043 : h ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_F, not_false_eq_true])
  have dv_cache_0044 : e ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_F, not_false_eq_true])
  have dv_cache_0045 : f ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0046 : g ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_F, not_false_eq_true])
  have dv_cache_0047 : h ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_G, not_false_eq_true])
  have dv_cache_0048 : e ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_G, not_false_eq_true])
  have dv_cache_0049 : f ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_G, not_false_eq_true])
  have dv_cache_0050 : g ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_G, not_false_eq_true])
  have dv_cache_0051 : h ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show h ≠ e from (by exact fresh_h_ne_e))
  have dv_cache_0052 : h ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show h ≠ f from (by exact fresh_h_ne_f))
  have dv_cache_0053 : h ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (show h ≠ g from (by exact fresh_h_ne_g))
  have dv_cache_0054 : e ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (show e ≠ f from (by exact fresh_e_ne_f))
  have dv_cache_0055 : e ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact (show e ≠ g from (by exact fresh_e_ne_g))
  have dv_cache_0056 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0057 : g ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_g_ne_y, fresh_g_ne_z, or_false, not_false_eq_true])
  have dv_cache_0058 : h ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_h_ne_y, fresh_h_ne_z, or_false, not_false_eq_true])
  have dv_cache_0059 : g ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_g_not_F, fresh_g_not_G, or_false, not_false_eq_true])
  have dv_cache_0060 : h ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_h_not_F, fresh_h_not_G, or_false, not_false_eq_true])
  have dv_cache_0061 : c ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_z, or_false, not_false_eq_true])
  have dv_cache_0062 : d ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_z, or_false, not_false_eq_true])
  have dv_cache_0063 : c ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_c_not_F, fresh_c_not_G, or_false, not_false_eq_true])
  have dv_cache_0064 : d ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_d_not_F, fresh_d_not_G, or_false, not_false_eq_true])
  have dv_cache_0065 : e ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_e_ne_y, fresh_e_ne_z, or_false, not_false_eq_true])
  have dv_cache_0066 : f ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_f_ne_y, fresh_f_ne_z, or_false, not_false_eq_true])
  have dv_cache_0067 : e ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_e_not_F, fresh_e_not_G, or_false, not_false_eq_true])
  have dv_cache_0068 : f ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_f_not_F, fresh_f_not_G, or_false, not_false_eq_true])
  have dv_cache_0069 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0070 : b ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0071 : a ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_a_not_F, fresh_a_not_G, or_false, not_false_eq_true])
  have dv_cache_0072 : b ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_b_not_F, fresh_b_not_G, or_false, not_false_eq_true])
  have dv_cache_0073 : z ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0074 : x ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0075 : y ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0076 : x ∉ ((synCpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0077 : y ∉ ((synCpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0078 : z ∉ ((synCpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0079 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0080 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0081 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @gEe4anv
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
            (.classEq (.cv y) (synCop (.cv c) (.cv d)))
            (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))
      (synWex g (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
            (.classEq (.cv z) (synCop (.cv g) (.cv h)))
            (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))))
      a b e f dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @gEe4anv
      (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
        (.classEq (.cv y) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
      (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
        (.classEq (.cv z) (synCop (.cv g) (.cv h)))
        (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
      c d g h dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0002 :=
    @gN2exbii
      (synWex c (synWex d (synWex g (synWex h (synWa
                (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                  (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                  (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                  (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                  (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))
      (synWa (synWex c (synWex d (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
              (.classEq (.cv y) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))))) (synWex g
          (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
              (.classEq (.cv z) (synCop (.cv g) (.cv h)))
              (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))
      e f p0001
  have p0003 :=
    @gN2exbii
      (synWex e (synWex f (synWex c (synWex d (synWex g (synWex h (synWa
                    (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                      (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                    (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))))
      (synWex e (synWex f (synWa (synWex c (synWex d
                (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                  (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                  (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))))) (synWex g
              (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                  (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                  (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))
      a b p0002
  have p0004 :=
    @gBrpprod a b c d (.cv x) (.cv y) F G dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034
  have p0005 :=
    @gBrpprod e f g h (.cv x) (.cv z) F G dv_cache_0035 dv_cache_0036 dv_cache_0037
      dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
      dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
      dv_cache_0056
  have p0006 :=
    @gAnbi12i (synWbr (.cv x) (synCpprod F G) (.cv y))
      (synWex a (synWex b (synWex c (synWex d
              (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))))
      (synWbr (.cv x) (synCpprod F G) (.cv z))
      (synWex e (synWex f (synWex g (synWex h
              (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))))))
      p0004 p0005
  have p0007 :=
    @gN3bitr4ri
      (synWex a (synWex b (synWex e (synWex f (synWa (synWex c (synWex d
                    (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                      (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))
                (synWex g (synWex h (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))))
      (synWa (synWex a (synWex b (synWex c (synWex d
                (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                  (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                  (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))))))
        (synWex e (synWex f (synWex g (synWex h
                (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                  (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                  (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))
      (synWex a (synWex b (synWex e (synWex f (synWex c (synWex d (synWex g (synWex h
                      (synWa (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                          (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                          (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                        (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                          (synWa (synWbr (.cv e) F (.cv g))
                            (synWbr (.cv f) G (.cv h)))))))))))))
      (synWa (synWbr (.cv x) (synCpprod F G) (.cv y))
        (synWbr (.cv x) (synCpprod F G) (.cv z)))
      p0000 p0003 p0006
  have p0008 :=
    @gAn42 (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))
      (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h))
  have p0009 := @gFununiq (.cv a) (.cv c) (.cv g) F
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun F) (synWbr (.cv a) F (.cv c)) (synWbr (.cv a) F (.cv g)))
        (.objEq c g)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWfun synWss synCin synCcompl synCnin synWnan
          synCcom synCopab synWex synCcnv synCid synWbr synCop synCun synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0009
  have p0010 :=
    @gN3expib (synWfun F) (synWbr (.cv a) F (.cv c)) (synWbr (.cv a) F (.cv g))
      (.objEq c g) p0010_e00_recanon
  have p0011 := @gFununiq (.cv b) (.cv h) (.cv d) G
  have p0012 :=
    @gEqcomd
      (synW3a (synWfun G) (synWbr (.cv b) G (.cv h)) (synWbr (.cv b) G (.cv d)))
      (.cv h) (.cv d) p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun G) (synWbr (.cv b) G (.cv h)) (synWbr (.cv b) G (.cv d)))
        (.objEq d h)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWfun synWss synCin synCcompl synCnin synWnan
          synCcom synCopab synWex synCcnv synCid synWbr synCop synCun synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0012
  have p0013 :=
    @gN3expib (synWfun G) (synWbr (.cv b) G (.cv h)) (synWbr (.cv b) G (.cv d))
      (.objEq d h) p0013_e00_recanon
  have p0014 :=
    @gIm2anan9 (synWfun F)
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv a) F (.cv g))) (.objEq c g)
      (synWfun G) (synWa (synWbr (.cv b) G (.cv h)) (synWbr (.cv b) G (.cv d)))
      (.objEq d h) p0010 p0013
  have p0015 :=
    @gSyl5bi
      (synWa (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
        (synWa (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h))))
      (synWa (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv a) F (.cv g)))
        (synWa (synWbr (.cv b) G (.cv h)) (synWbr (.cv b) G (.cv d))))
      (synWa (synWfun F) (synWfun G)) (synWa (.objEq c g) (.objEq d h)) p0008 p0014
  have p0016 :=
    @gExp3acom23 (synWa (synWfun F) (synWfun G))
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
      (synWa (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h)))
      (synWa (.objEq c g) (.objEq d h)) p0015
  have p0017 := @gBreq1 (.cv e) (.cv a) (.cv g) F
  have p0018 := @gBreq1 (.cv f) (.cv b) (.cv h) G
  have p0019_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq e a) (synWb (synWbr (.cv e) F (.cv g)) (synWbr (.cv a) F (.cv g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0019_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f b) (synWb (synWbr (.cv f) G (.cv h)) (synWbr (.cv b) G (.cv h)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @gBi2anan9 (.objEq e a) (synWbr (.cv e) F (.cv g)) (synWbr (.cv a) F (.cv g))
      (.objEq f b) (synWbr (.cv f) G (.cv h)) (synWbr (.cv b) G (.cv h))
      p0019_e00_recanon p0019_e01_recanon
  have p0020 :=
    @gAdantr (synWa (.objEq e a) (.objEq f b))
      (synWb (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))
        (synWa (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h))))
      (.classEq (.cv z) (synCop (.cv g) (.cv h))) p0019
  have p0021 := @gEqeq2 (.cv z) (synCop (.cv g) (.cv h)) (synCop (.cv c) (.cv d))
  have p0022 := @gOpth (.cv c) (.cv d) (.cv g) (.cv h)
  have p0023_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv c) (.cv d)) (synCop (.cv g) (.cv h)))
        (synWa (.objEq c g) (.objEq d h))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gSyl6bb (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (.classEq (synCop (.cv c) (.cv d)) (.cv z))
      (.classEq (synCop (.cv c) (.cv d)) (synCop (.cv g) (.cv h)))
      (synWa (.objEq c g) (.objEq d h)) p0021 p0023_e01_recanon
  have p0024 :=
    @gImbi2d (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (.classEq (synCop (.cv c) (.cv d)) (.cv z)) (synWa (.objEq c g) (.objEq d h))
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))) p0023
  have p0025 :=
    @gAdantl (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (synWb (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
          (.classEq (synCop (.cv c) (.cv d)) (.cv z)))
        (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
          (synWa (.objEq c g) (.objEq d h))))
      (synWa (.objEq e a) (.objEq f b)) p0024
  have p0026 :=
    @gImbi12d
      (synWa (synWa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (synCop (.cv g) (.cv h))))
      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))
      (synWa (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h)))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
        (.classEq (synCop (.cv c) (.cv d)) (.cv z)))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
        (synWa (.objEq c g) (.objEq d h)))
      p0020 p0025
  have p0027 :=
    @gSyl5ibrcom (synWa (synWfun F) (synWfun G))
      (.imp (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))
        (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
          (.classEq (synCop (.cv c) (.cv d)) (.cv z))))
      (synWa (synWa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (synCop (.cv g) (.cv h))))
      (.imp (synWa (synWbr (.cv a) F (.cv g)) (synWbr (.cv b) G (.cv h)))
        (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
          (synWa (.objEq c g) (.objEq d h))))
      p0016 p0026
  have p0028 :=
    @gExp3a (synWa (synWfun F) (synWfun G)) (synWa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (.imp (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))
        (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
          (.classEq (synCop (.cv c) (.cv d)) (.cv z))))
      p0027
  have p0029 :=
    @gN3impd (synWa (synWfun F) (synWfun G)) (synWa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
        (.classEq (synCop (.cv c) (.cv d)) (.cv z)))
      p0028
  have p0030 :=
    @gCom23 (synWa (synWfun F) (synWfun G))
      (synW3a (synWa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (synCop (.cv g) (.cv h)))
        (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
      (.classEq (synCop (.cv c) (.cv d)) (.cv z)) p0029
  have p0031 := @gEqeq1 (.cv x) (synCop (.cv a) (.cv b)) (synCop (.cv e) (.cv f))
  have p0032 := @gEqcom (synCop (.cv a) (.cv b)) (synCop (.cv e) (.cv f))
  have p0033 := @gOpth (.cv e) (.cv f) (.cv a) (.cv b)
  have p0034_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv e) (.cv f)) (synCop (.cv a) (.cv b)))
        (synWa (.objEq e a) (.objEq f b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @gBitri (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv e) (.cv f)))
      (.classEq (synCop (.cv e) (.cv f)) (synCop (.cv a) (.cv b)))
      (synWa (.objEq e a) (.objEq f b)) p0032 p0034_e01_recanon
  have p0035 :=
    @gSyl6bb (.classEq (.cv x) (synCop (.cv a) (.cv b)))
      (.classEq (.cv x) (synCop (.cv e) (.cv f)))
      (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv e) (.cv f)))
      (synWa (.objEq e a) (.objEq f b)) p0031 p0034
  have p0036 :=
    @gN3anbi1d (.classEq (.cv x) (synCop (.cv a) (.cv b)))
      (.classEq (.cv x) (synCop (.cv e) (.cv f))) (synWa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))) p0035
  have p0037 :=
    @gAdantr (.classEq (.cv x) (synCop (.cv a) (.cv b)))
      (synWb (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
        (synW3a (synWa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))
      (.classEq (.cv y) (synCop (.cv c) (.cv d))) p0036
  have p0038 := @gEqeq1 (.cv y) (synCop (.cv c) (.cv d)) (.cv z)
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (synCop (.cv c) (.cv d)))
        (synWb (.objEq y z) (.classEq (synCop (.cv c) (.cv d)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0038
  have p0039 :=
    @gAdantl (.classEq (.cv y) (synCop (.cv c) (.cv d)))
      (synWb (.objEq y z) (.classEq (synCop (.cv c) (.cv d)) (.cv z)))
      (.classEq (.cv x) (synCop (.cv a) (.cv b))) p0039_e00_recanon
  have p0040 :=
    @gImbi12d
      (synWa (.classEq (.cv x) (synCop (.cv a) (.cv b)))
        (.classEq (.cv y) (synCop (.cv c) (.cv d))))
      (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
        (.classEq (.cv z) (synCop (.cv g) (.cv h)))
        (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
      (synW3a (synWa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (synCop (.cv g) (.cv h)))
        (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
      (.objEq y z) (.classEq (synCop (.cv c) (.cv d)) (.cv z)) p0037 p0039
  have p0041 :=
    @gImbi2d
      (synWa (.classEq (.cv x) (synCop (.cv a) (.cv b)))
        (.classEq (.cv y) (synCop (.cv c) (.cv d))))
      (.imp (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))) (.objEq y z))
      (.imp (synW3a (synWa (.objEq e a) (.objEq f b))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
        (.classEq (synCop (.cv c) (.cv d)) (.cv z)))
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))) p0040
  have p0042 :=
    @gSyl5ibrcom (synWa (synWfun F) (synWfun G))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))) (.imp
          (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
            (.classEq (.cv z) (synCop (.cv g) (.cv h)))
            (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))) (.objEq y z)))
      (synWa (.classEq (.cv x) (synCop (.cv a) (.cv b)))
        (.classEq (.cv y) (synCop (.cv c) (.cv d))))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))) (.imp
          (synW3a (synWa (.objEq e a) (.objEq f b))
            (.classEq (.cv z) (synCop (.cv g) (.cv h)))
            (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
          (.classEq (synCop (.cv c) (.cv d)) (.cv z))))
      p0030 p0041
  have p0043 :=
    @gExp3a (synWa (synWfun F) (synWfun G))
      (.classEq (.cv x) (synCop (.cv a) (.cv b)))
      (.classEq (.cv y) (synCop (.cv c) (.cv d)))
      (.imp (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))) (.imp
          (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
            (.classEq (.cv z) (synCop (.cv g) (.cv h)))
            (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))) (.objEq y z)))
      p0042
  have p0044 :=
    @gN3impd (synWa (synWfun F) (synWfun G))
      (.classEq (.cv x) (synCop (.cv a) (.cv b)))
      (.classEq (.cv y) (synCop (.cv c) (.cv d)))
      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d)))
      (.imp (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))) (.objEq y z))
      p0043
  have p0045 :=
    @gImp3a (synWa (synWfun F) (synWfun G))
      (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
        (.classEq (.cv y) (synCop (.cv c) (.cv d)))
        (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
      (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
        (.classEq (.cv z) (synCop (.cv g) (.cv h)))
        (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h))))
      (.objEq y z) p0044
  have p0046 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWa (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
          (.classEq (.cv y) (synCop (.cv c) (.cv d)))
          (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
        (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
          (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))
      (.objEq y z) g h dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 p0045
  have p0047 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWex g (synWex h (synWa (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
              (.classEq (.cv y) (synCop (.cv c) (.cv d)))
              (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
            (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
              (.classEq (.cv z) (synCop (.cv g) (.cv h)))
              (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))
      (.objEq y z) c d dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 p0046
  have p0048 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWex c (synWex d (synWex g (synWex h (synWa
                (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                  (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                  (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                  (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                  (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))
      (.objEq y z) e f dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 p0047
  have p0049 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWex e (synWex f (synWex c (synWex d (synWex g (synWex h (synWa
                    (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                      (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                      (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                    (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                      (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                      (synWa (synWbr (.cv e) F (.cv g)) (synWbr (.cv f) G (.cv h)))))))))))
      (.objEq y z) a b dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 p0048
  have p0050 :=
    @gSyl5bi
      (synWa (synWbr (.cv x) (synCpprod F G) (.cv y))
        (synWbr (.cv x) (synCpprod F G) (.cv z)))
      (synWex a (synWex b (synWex e (synWex f (synWex c (synWex d (synWex g (synWex h
                      (synWa (synW3a (.classEq (.cv x) (synCop (.cv a) (.cv b)))
                          (.classEq (.cv y) (synCop (.cv c) (.cv d)))
                          (synWa (synWbr (.cv a) F (.cv c)) (synWbr (.cv b) G (.cv d))))
                        (synW3a (.classEq (.cv x) (synCop (.cv e) (.cv f)))
                          (.classEq (.cv z) (synCop (.cv g) (.cv h)))
                          (synWa (synWbr (.cv e) F (.cv g))
                            (synWbr (.cv f) G (.cv h)))))))))))))
      (synWa (synWfun F) (synWfun G)) (.objEq y z) p0007 p0049
  have p0051 :=
    @gAlrimiv (synWa (synWfun F) (synWfun G))
      (.imp (synWa (synWbr (.cv x) (synCpprod F G) (.cv y))
          (synWbr (.cv x) (synCpprod F G) (.cv z))) (.objEq y z))
      z dv_cache_0073 p0050
  have p0052 :=
    @gAlrimivv (synWa (synWfun F) (synWfun G))
      (.all z (.imp (synWa (synWbr (.cv x) (synCpprod F G) (.cv y))
            (synWbr (.cv x) (synCpprod F G) (.cv z))) (.objEq y z)))
      x y dv_cache_0074 dv_cache_0075 p0051
  have p0053 :=
    @gDffun2 x y z (synCpprod F G) dv_cache_0076 dv_cache_0077 dv_cache_0078
      dv_cache_0079 dv_cache_0080 dv_cache_0081
  have p0054 :=
    @gSylibr (synWa (synWfun F) (synWfun G))
      (.all x (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCpprod F G) (.cv y))
                (synWbr (.cv x) (synCpprod F G) (.cv z))) (.objEq y z)))))
      (synWfun (synCpprod F G)) p0052 p0053
  have p0055 := @gDmpprod F G
  have p0056 := @gXpeq12 (synCdm F) A (synCdm G) B
  have p0057 :=
    @gSyl5eq (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synCdm (synCpprod F G)) (synCxp (synCdm F) (synCdm G)) (synCxp A B) p0055
      p0056
  have p0058 :=
    @gAnim12i (synWa (synWfun F) (synWfun G)) (synWfun (synCpprod F G))
      (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (.classEq (synCdm (synCpprod F G)) (synCxp A B)) p0054 p0057
  have p0059 :=
    @gAn4s (synWfun F) (synWfun G) (.classEq (synCdm F) A) (.classEq (synCdm G) B)
      (synWa (synWfun (synCpprod F G)) (.classEq (synCdm (synCpprod F G)) (synCxp A B)))
      p0058
  have p0060 := (Nominal.biimpRefl (synWfn F A))
  have p0061 := (Nominal.biimpRefl (synWfn G B))
  have p0062 :=
    @gAnbi12i (synWfn F A) (synWa (synWfun F) (.classEq (synCdm F) A)) (synWfn G B)
      (synWa (synWfun G) (.classEq (synCdm G) B)) p0060 p0061
  have p0063 := (Nominal.biimpRefl (synWfn (synCpprod F G) (synCxp A B)))
  have p0064 :=
    @gN3imtr4i
      (synWa (synWa (synWfun F) (.classEq (synCdm F) A))
        (synWa (synWfun G) (.classEq (synCdm G) B)))
      (synWa (synWfun (synCpprod F G)) (.classEq (synCdm (synCpprod F G)) (synCxp A B)))
      (synWa (synWfn F A) (synWfn G B)) (synWfn (synCpprod F G) (synCxp A B)) p0059
      p0062 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_f1opprod`. -/
@[expose]
noncomputable def gF1opprod (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F A C) (synWf1o G B D))
        (synWf1o (synCpprod F G) (synCxp A B) (synCxp C D))) :=
  by
  have p0000 := @gFnpprod A B F G
  have p0001 := @gFnpprod C D (synCcnv F) (synCcnv G)
  have p0002 := @gCnvpprod F G
  have p0003 :=
    @gFneq1i (synCxp C D) (synCcnv (synCpprod F G))
      (synCpprod (synCcnv F) (synCcnv G)) p0002
  have p0004 :=
    @gSylibr (synWa (synWfn (synCcnv F) C) (synWfn (synCcnv G) D))
      (synWfn (synCpprod (synCcnv F) (synCcnv G)) (synCxp C D))
      (synWfn (synCcnv (synCpprod F G)) (synCxp C D)) p0001 p0003
  have p0005 :=
    @gAnim12i (synWa (synWfn F A) (synWfn G B))
      (synWfn (synCpprod F G) (synCxp A B))
      (synWa (synWfn (synCcnv F) C) (synWfn (synCcnv G) D))
      (synWfn (synCcnv (synCpprod F G)) (synCxp C D)) p0000 p0004
  have p0006 :=
    @gAn4s (synWfn F A) (synWfn G B) (synWfn (synCcnv F) C) (synWfn (synCcnv G) D)
      (synWa (synWfn (synCpprod F G) (synCxp A B))
        (synWfn (synCcnv (synCpprod F G)) (synCxp C D)))
      p0005
  have p0007 := @gDff1o4 A C F
  have p0008 := @gDff1o4 B D G
  have p0009 :=
    @gAnbi12i (synWf1o F A C) (synWa (synWfn F A) (synWfn (synCcnv F) C))
      (synWf1o G B D) (synWa (synWfn G B) (synWfn (synCcnv G) D)) p0007 p0008
  have p0010 := @gDff1o4 (synCxp A B) (synCxp C D) (synCpprod F G)
  have p0011 :=
    @gN3imtr4i
      (synWa (synWa (synWfn F A) (synWfn (synCcnv F) C))
        (synWa (synWfn G B) (synWfn (synCcnv G) D)))
      (synWa (synWfn (synCpprod F G) (synCxp A B))
        (synWfn (synCcnv (synCpprod F G)) (synCxp C D)))
      (synWa (synWf1o F A C) (synWf1o G B D))
      (synWf1o (synCpprod F G) (synCxp A B) (synCxp C D)) p0006 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ovcross`. -/
@[expose]
noncomputable def gOvcross (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.classEq (synCo A (synCcross) B) (synCxp A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCxp A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := @gXpexg A B (synCvv) (synCvv)
  have p0003 := @gXpeq1 (.cv x) A (.cv y)
  have p0004 := @gXpeq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCross x y
      dv_cache_0001
  have p0006 :=
    @gOvmpt2g x y A B (synCvv) (synCvv) (synCxp (.cv x) (.cv y)) (synCxp A B)
      (synCcross) (synCxp A (.cv y)) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @gMpd3an3 (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCxp A B) (synCvv))
      (.classEq (synCo A (synCcross) B) (synCxp A B)) p0002 p0006
  have p0008 :=
    @gSyl2an (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classEq (synCo A (synCcross) B) (synCxp A B)) (.classMem B W) p0000 p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fncross`. -/
@[expose]
noncomputable def gFncross : Nominal.NPrf (synWfn (synCcross) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCross x y
      dv_cache_0001
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gXpex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @gFnmpt2i x y (synCvv) (synCvv) (synCxp (.cv x) (.cv y)) (synCcross)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @gXpvv
  have p0006 := @gFneq2i (synCxp (synCvv) (synCvv)) (synCvv) (synCcross) p0005
  have p0007 :=
    @gMpbi (synWfn (synCcross) (synCxp (synCvv) (synCvv)))
      (synWfn (synCcross) (synCvv)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_brcrossg`. -/
@[expose]
noncomputable def gBrcrossg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr (synCop A B) (synCcross) C) (.classEq C (synCxp A B)))) :=
  by
  have p0000 := @gEqcom C (synCo A (synCcross) B)
  have p0001 := (Nominal.classEqRefl (synCo A (synCcross) B))
  have p0002 :=
    @gEqeq1i (synCo A (synCcross) B) (synCfv (synCcross) (synCop A B)) C p0001
  have p0003 :=
    @gBitri (.classEq C (synCo A (synCcross) B)) (.classEq (synCo A (synCcross) B) C)
      (.classEq (synCfv (synCcross) (synCop A B)) C) p0000 p0002
  have p0004 := @gFncross
  have p0005 := @gOpexg A B V W
  have p0006 := @gFnbrfvb (synCvv) (synCop A B) C (synCcross)
  have p0007 :=
    @gSylancr (synWa (.classMem A V) (.classMem B W)) (synWfn (synCcross) (synCvv))
      (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synCcross) (synCop A B)) C)
        (synWbr (synCop A B) (synCcross) C))
      p0004 p0005 p0006
  have p0008 :=
    @gSyl5bb (.classEq C (synCo A (synCcross) B))
      (.classEq (synCfv (synCcross) (synCop A B)) C)
      (synWa (.classMem A V) (.classMem B W)) (synWbr (synCop A B) (synCcross) C)
      p0003 p0007
  have p0009 := @gOvcross A B V W
  have p0010 :=
    @gEqeq2d (synWa (.classMem A V) (.classMem B W)) (synCo A (synCcross) B)
      (synCxp A B) C p0009
  have p0011 :=
    @gBitr3d (synWa (.classMem A V) (.classMem B W))
      (.classEq C (synCo A (synCcross) B)) (synWbr (synCop A B) (synCcross) C)
      (.classEq C (synCxp A B)) p0008 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_brcross`. -/
@[expose]
noncomputable def gBrcross (A : Class) (B : Class) (C : Class)
    (hyp_brcross_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brcross_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCcross) C) (.classEq C (synCxp A B))) :=
  by
  have p0000 := @gBrcrossg A B C (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr (synCop A B) (synCcross) C) (.classEq C (synCxp A B)))
      hyp_brcross_1 hyp_brcross_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_crossex`. -/
@[expose]
noncomputable def gCrossex : Nominal.NPrf (.classMem (synCcross) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0004 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0005 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0009 :
    a ∉ ((synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_z, fresh_a_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    a ∉
      ((synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, fresh_b_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
          (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
          (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    z ∉
      ((synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
          (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((synCxp (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0019 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0020 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCross x y
      dv_cache_0001
  have p0001 :=
    @gRexcom (.classEq (.cv z) (synCop (.cv a) (.cv b))) a b (.cv x) (.cv y)
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gElxp2 a b (.cv z) (.cv x) (.cv y) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0004
  have p0003 :=
    @gElin
      (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins2 (synCcnv (synC1st)))
                  (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))
  have p0004 := @gSnex (.cv z)
  have p0005 :=
    @gOtelins2 (synCsn (.cv b)) (synCsn (.cv z)) (synCop (.cv x) (.cv y))
      (synCins2 (synCsset)) p0004
  have p0006 := @gVex x
  have p0007 := @gOtelins2 (synCsn (.cv b)) (.cv x) (.cv y) (synCsset) p0006
  have p0008 := @gVex b
  have p0009 := @gVex y
  have p0010 := @gOpelssetsn (.cv b) (.cv y) p0008 p0009
  have p0011_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv b)) (.cv y)) (synCsset)) (.objMem b y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv b)) (.cv y)) (synCsset)) (.objMem b y) p0005
      p0007 p0011_e02_recanon
  have p0012 :=
    @gOqelins4 (synCsn (.cv b)) (synCsn (.cv z)) (.cv x) (.cv y)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))
      p0009
  have p0013 :=
    @gElin
      (synCop (synCsn (.cv a))
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
            (synCxp (synCvv) (synCcnv (synC2nd))))))
  have p0014 := @gSnex (.cv b)
  have p0015 :=
    @gOtelins2 (synCsn (.cv a)) (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))
      (synCins2 (synCsset)) p0014
  have p0016 := @gOtelins2 (synCsn (.cv a)) (synCsn (.cv z)) (.cv x) (synCsset) p0004
  have p0017 := @gVex a
  have p0018 := @gOpelssetsn (.cv a) (.cv x) p0017 p0006
  have p0019_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv a)) (.cv x)) (synCsset)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv a)) (synCop (synCsn (.cv z)) (.cv x)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv a)) (.cv x)) (synCsset)) (.objMem a x) p0015
      p0016 p0019_e02_recanon
  have p0020 :=
    @gOqelins4 (synCsn (.cv a)) (synCsn (.cv b)) (synCsn (.cv z)) (.cv x)
      (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
          (synCxp (synCvv) (synCcnv (synC2nd)))))
      p0006
  have p0021 := @gVex z
  have p0022 :=
    @gOtsnelsi3 (.cv a) (.cv b) (.cv z)
      (synCin (synCins2 (synCcnv (synC1st))) (synCxp (synCvv) (synCcnv (synC2nd))))
      p0017 p0008 p0021
  have p0023 :=
    @gElin (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins2 (synCcnv (synC1st)))
      (synCxp (synCvv) (synCcnv (synC2nd)))
  have p0024 := @gOtelins2 (.cv a) (.cv b) (.cv z) (synCcnv (synC1st)) p0008
  have p0025 := (Nominal.biimpRefl (synWbr (.cv a) (synCcnv (synC1st)) (.cv z)))
  have p0026 := @gBrcnv (.cv a) (.cv z) (synC1st)
  have p0027 :=
    @gN3bitr2i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins2 (synCcnv (synC1st))))
      (.classMem (synCop (.cv a) (.cv z)) (synCcnv (synC1st)))
      (synWbr (.cv a) (synCcnv (synC1st)) (.cv z)) (synWbr (.cv z) (synC1st) (.cv a))
      p0024 p0025 p0026
  have p0028 :=
    @gOpelxp (.cv a) (synCop (.cv b) (.cv z)) (synCvv) (synCcnv (synC2nd))
  have p0029 :=
    @gMpbiran
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC2nd))))
      (.classMem (.cv a) (synCvv))
      (.classMem (synCop (.cv b) (.cv z)) (synCcnv (synC2nd))) p0017 p0028
  have p0030 := (Nominal.biimpRefl (synWbr (.cv b) (synCcnv (synC2nd)) (.cv z)))
  have p0031 := @gBrcnv (.cv b) (.cv z) (synC2nd)
  have p0032 :=
    @gN3bitr2i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC2nd))))
      (.classMem (synCop (.cv b) (.cv z)) (synCcnv (synC2nd)))
      (synWbr (.cv b) (synCcnv (synC2nd)) (.cv z)) (synWbr (.cv z) (synC2nd) (.cv b))
      p0029 p0030 p0031
  have p0033 :=
    @gAnbi12i
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z))) (synCins2 (synCcnv (synC1st))))
      (synWbr (.cv z) (synC1st) (.cv a))
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC2nd))))
      (synWbr (.cv z) (synC2nd) (.cv b)) p0027 p0032
  have p0034 := @gOp1st2nd (.cv a) (.cv b) (.cv z) p0017 p0008
  have p0035 :=
    @gN3bitri
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
        (synCin (synCins2 (synCcnv (synC1st))) (synCxp (synCvv) (synCcnv (synC2nd)))))
      (synWa (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
          (synCins2 (synCcnv (synC1st))))
        (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
          (synCxp (synCvv) (synCcnv (synC2nd)))))
      (synWa (synWbr (.cv z) (synC1st) (.cv a)) (synWbr (.cv z) (synC2nd) (.cv b)))
      (.classEq (.cv z) (synCop (.cv a) (.cv b))) p0023 p0033 p0034
  have p0036 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4 (synCsi3
            (synCin (synCins2 (synCcnv (synC1st)))
              (synCxp (synCvv) (synCcnv (synC2nd)))))))
      (.classMem (synCop (synCsn (.cv a)) (synCop (synCsn (.cv b)) (synCsn (.cv z))))
        (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
            (synCxp (synCvv) (synCcnv (synC2nd))))))
      (.classMem (synCop (.cv a) (synCop (.cv b) (.cv z)))
        (synCin (synCins2 (synCcnv (synC1st))) (synCxp (synCvv) (synCcnv (synC2nd)))))
      (.classEq (.cv z) (synCop (.cv a) (.cv b))) p0020 p0022 p0035
  have p0037 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem a x)
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4 (synCsi3
            (synCin (synCins2 (synCcnv (synC1st)))
              (synCxp (synCvv) (synCcnv (synC2nd)))))))
      (.classEq (.cv z) (synCop (.cv a) (.cv b))) p0019 p0036
  have p0038 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd))))))))
      (synWa (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))) (synCins4
            (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd))))))))
      (synWa (.objMem a x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) p0013 p0037
  have p0039 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv a))
          (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd))))))))
      (synWa (.objMem a x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) a p0038
  have p0040 :=
    @gElima1c a (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
            (synCin (synCins2 (synCcnv (synC1st)))
              (synCxp (synCvv) (synCcnv (synC2nd)))))))
      dv_cache_0009 dv_cache_0010
  have p0041 :=
    (Nominal.biimpRefl (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
  have p0042_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) (synWex a
          (synWa (.objMem a x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCop, synCun, synCnin,
          synWnan, synCcompl]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @gN3bitr4i
      (synWex a (.classMem (synCop (synCsn (.cv a))
            (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins2 (synCcnv (synC1st)))
                  (synCxp (synCvv) (synCcnv (synC2nd)))))))))
      (synWex a (synWa (.objMem a x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins2 (synCcnv (synC1st)))
                  (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))
      (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) p0039 p0040
      p0042_e02_recanon
  have p0043 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins2 (synCcnv (synC1st)))
                    (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
      (.classMem (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (.cv x))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins2 (synCcnv (synC1st)))
                  (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))
      (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) p0012 p0042
  have p0044 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem b y)
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins2 (synCcnv (synC1st)))
                    (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
      (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))) p0011 p0043
  have p0045 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))))
      (synWa (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))))
      (synWa (.objMem b y) (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      p0003 p0044
  have p0046 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv b)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))))
      (synWa (.objMem b y) (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      b p0045
  have p0047 :=
    @gElima1c b (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins2 (synCcnv (synC1st)))
                    (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
      dv_cache_0011 dv_cache_0012
  have p0048 :=
    (Nominal.biimpRefl (synWrex b (.cv y)
        (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b))))))
  have p0049_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex b (.cv y)
          (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b))))) (synWex b
          (synWa (.objMem b y)
            (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0049 :=
    @gN3bitr4i
      (synWex b (.classMem (synCop (synCsn (.cv b))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))))
      (synWex b (synWa (.objMem b y)
          (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b))))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))) (synC1c)))
      (synWrex b (.cv y) (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      p0046 p0047 p0049_e02_recanon
  have p0050 :=
    @gN3bitr4ri
      (synWrex a (.cv x) (synWrex b (.cv y) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      (synWrex b (.cv y) (synWrex a (.cv x) (.classEq (.cv z) (synCop (.cv a) (.cv b)))))
      (.classMem (.cv z) (synCxp (.cv x) (.cv y)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                      (synCin (synCins2 (synCcnv (synC1st)))
                        (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))) (synC1c)))
      p0001 p0002 p0049
  have p0051 :=
    @gReleqmpt2 x y z (synCvv) (synCvv)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))) (synC1c))
      (synCxp (.cv x) (.cv y)) dv_cache_0013 dv_cache_0014 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0001 dv_cache_0019
      dv_cache_0020 p0050
  have p0052 :=
    @gEqtr4i (synCcross) (synCmpt2 x (synCvv) y (synCvv) (synCxp (.cv x) (.cv y)))
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                            (synCin (synCins2 (synCcnv (synC1st)))
                              (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
                (synC1c)))) (synC1c)))
      p0000 p0051
  have p0053 := @gVvex
  have p0055 := @gSsetex
  have p0056 := @gIns2ex (synCsset) p0055
  have p0057 := @gIns2ex (synCins2 (synCsset)) p0056
  have p0058 := @gN1stex
  have p0059 := @gCnvex (synC1st) p0058
  have p0060 := @gIns2ex (synCcnv (synC1st)) p0059
  have p0062 := @gN2ndex
  have p0063 := @gCnvex (synC2nd) p0062
  have p0064 := @gXpex (synCvv) (synCcnv (synC2nd)) p0053 p0063
  have p0065 :=
    @gInex (synCins2 (synCcnv (synC1st))) (synCxp (synCvv) (synCcnv (synC2nd)))
      p0060 p0064
  have p0066 :=
    @gSi3ex
      (synCin (synCins2 (synCcnv (synC1st))) (synCxp (synCvv) (synCcnv (synC2nd))))
      p0065
  have p0067 :=
    @gIns4ex
      (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
          (synCxp (synCvv) (synCcnv (synC2nd)))))
      p0066
  have p0068 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCsi3 (synCin (synCins2 (synCcnv (synC1st)))
            (synCxp (synCvv) (synCcnv (synC2nd))))))
      p0057 p0067
  have p0069 := @gN1cex
  have p0070 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
            (synCin (synCins2 (synCcnv (synC1st)))
              (synCxp (synCvv) (synCcnv (synC2nd)))))))
      (synC1c) p0068 p0069
  have p0071 :=
    @gIns4ex
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
              (synCin (synCins2 (synCcnv (synC1st)))
                (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))
      p0070
  have p0072 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                (synCin (synCins2 (synCcnv (synC1st)))
                  (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))
      p0057 p0071
  have p0074 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                  (synCin (synCins2 (synCcnv (synC1st)))
                    (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
      (synC1c) p0072 p0069
  have p0075 :=
    @gMpt2exlem (synCvv) (synCvv)
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                    (synCin (synCins2 (synCcnv (synC1st)))
                      (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c)))) (synC1c))
      p0053 p0053 p0074
  have p0076 :=
    @gEqeltri (synCcross)
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCima
                      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCsi3
                            (synCin (synCins2 (synCcnv (synC1st)))
                              (synCxp (synCvv) (synCcnv (synC2nd))))))) (synC1c))))
                (synC1c)))) (synC1c)))
      (synCvv) p0052 p0075
  exact p0076

/-- Checked nominal proof certificate identified upstream as `g_pw1fnval`. -/
@[expose]
noncomputable def gPw1fnval (A : Class)
    (hyp_pw1fnval_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCpw1fn) (synCsn A)) (synCpw1 A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ ((synCsn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCpw1 A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gSnel1c A hyp_pw1fnval_1
  have p0001 := @gUnieq (.cv x) (synCsn A)
  have p0002 := @gUnisn A hyp_pw1fnval_1
  have p0003 :=
    @gSyl6eq (.classEq (.cv x) (synCsn A)) (synCuni (.cv x)) (synCuni (synCsn A)) A
      p0001 p0002
  have p0004 := @gPw1eq (synCuni (.cv x)) A
  have p0005 :=
    @gSyl (.classEq (.cv x) (synCsn A)) (.classEq (synCuni (.cv x)) A)
      (.classEq (synCpw1 (synCuni (.cv x))) (synCpw1 A)) p0003 p0004
  have p0006 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw1fn x
  have p0007 := @gPw1ex A hyp_pw1fnval_1
  have p0008 :=
    @gFvmpt x (synCsn A) (synCpw1 (synCuni (.cv x))) (synCpw1 A) (synC1c)
      (synCpw1fn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 := Nominal.mp p0000 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
