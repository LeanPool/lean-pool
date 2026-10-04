/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C086C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb086_alpha_dummy_000`. -/
@[expose]
noncomputable def nb086AlphaDummy000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb086_alpha_dummy_001`. -/
@[expose]
noncomputable def nb086AlphaDummy001 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb086_alpha_dummy_002`. -/
@[expose]
noncomputable def nb086AlphaDummy002 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb086_alpha_dummy_003`. -/
@[expose]
noncomputable def nb086AlphaDummy003 (x : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0)

theorem nb086_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy002 A B C R) ∉
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv) :=
  by
  simpa only [nb086AlphaDummy002] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv) 0

theorem nb086_fresh_001 (x : Var) (A : Class) (B : Class) (R : Class) :
    (nb086AlphaDummy003 x A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb086AlphaDummy003] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0

theorem nb086_fresh_002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb086AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb086_fresh_003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb086AlphaDummy001] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1

theorem nb086_distinct_004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ≠ (nb086AlphaDummy001 A B C R) := by
  simpa only [nb086AlphaDummy000, nb086AlphaDummy001] using
    (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb086_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∈
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb086_support_mem_0001 (x : Var) (A : Class) (B : Class) (R : Class) :
    x ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb086_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb086_focused_notmem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb086_compact_envfresh_0000 (x : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (q : Var) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) :
    TEnvFresh [((nb086AlphaDummy001 A B C R), x), ((nb086AlphaDummy000 A B C R), q)]
      C.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb086AlphaDummy001 A B C R) x
      (nb086_focused_notmem_0000 A B C R) dv_C_x
      (TEnvFresh.consFresh (nb086AlphaDummy000 A B C R) q
        (nb086_focused_notmem_0001 A B C R) dv_C_q (TEnvFresh.nil C.fv)))

/-- Checked nominal proof certificate identified upstream as `nb086_focused_refl_0000`. -/
@[expose]
noncomputable def nb086FocusedRefl0000 (x : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (q : Var) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) :
    TReflOn [((nb086AlphaDummy001 A B C R), x), ((nb086AlphaDummy000 A B C R), q)]
      C.fv :=
  TEnvFresh.reflOn (nb086_compact_envfresh_0000 x A B C R q dv_C_q dv_C_x)

theorem nb086_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy002 A B C R) ∉ A.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy002 A B C R) ∉ B.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy002 A B C R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb086AlphaDummy001 A B C R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy002 A B C R) ∉ ((synCfdif R A B)).fv := by
  simpa only [nb086AlphaDummy002, fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb086_focused_notmem_0002 A B C R) (nb086_focused_notmem_0003 A B C R))
      (nb086_focused_notmem_0004 A B C R))

theorem nb086_focused_notmem_0005 (x : Var) (A : Class) (B : Class) (R : Class) :
    (nb086AlphaDummy003 x A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0006 (x : Var) (A : Class) (B : Class) (R : Class) :
    (nb086AlphaDummy003 x A B R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0007 (x : Var) (A : Class) (B : Class) (R : Class) :
    (nb086AlphaDummy003 x A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv x)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0001 (x : Var) (A : Class) (B : Class) (R : Class) :
    (nb086AlphaDummy003 x A B R) ∉ ((synCfdif R A B)).fv := by
  simpa only [nb086AlphaDummy003, fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb086_focused_notmem_0005 x A B R) (nb086_focused_notmem_0006 x A B R))
      (nb086_focused_notmem_0007 x A B R))

theorem nb086_focused_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0009 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy001 A B C R) ∉ ((synCfdif R A B)).fv := by
  simpa only [nb086AlphaDummy001, fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb086_focused_notmem_0008 A B C R) (nb086_focused_notmem_0009 A B C R))
      (nb086_focused_notmem_0010 A B C R))

theorem nb086_wpp_notmem_0003 (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    x ∉ ((synCfdif R A B)).fv := by
  simpa only [fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_x dv_B_x) dv_R_x)

theorem nb086_focused_notmem_0011 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb086_focused_notmem_0012 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb086_focused_notmem_0013 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb086_wpp_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb086AlphaDummy000 A B C R) ∉ ((synCfdif R A B)).fv := by
  simpa only [nb086AlphaDummy000, fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb086_focused_notmem_0011 A B C R) (nb086_focused_notmem_0012 A B C R))
      (nb086_focused_notmem_0013 A B C R))

theorem nb086_wpp_notmem_0005 (A : Class) (B : Class) (R : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_B_q : q ∉ B.fv) (dv_R_q : q ∉ R.fv) :
    q ∉ ((synCfdif R A B)).fv := by
  simpa only [fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_q dv_B_q) dv_R_q)

theorem nb086_compact_envfresh_0001 (x : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_B_q : q ∉ B.fv)
    (dv_B_x : x ∉ B.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) :
    TEnvFresh
      [((nb086AlphaDummy002 A B C R), (nb086AlphaDummy003 x A B R)),
        ((nb086AlphaDummy001 A B C R), x), ((nb086AlphaDummy000 A B C R), q)]
      ((synCfdif R A B)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb086AlphaDummy002 A B C R) (nb086AlphaDummy003 x A B R)
      (nb086_wpp_notmem_0000 A B C R) (nb086_wpp_notmem_0001 x A B R)
      (TEnvFresh.consFresh (nb086AlphaDummy001 A B C R) x (nb086_wpp_notmem_0002 A B C R)
        (nb086_wpp_notmem_0003 x A B R dv_A_x dv_B_x dv_R_x)
        (TEnvFresh.consFresh (nb086AlphaDummy000 A B C R) q (nb086_wpp_notmem_0004 A B C R)
          (nb086_wpp_notmem_0005 A B R q dv_A_q dv_B_q dv_R_q)
          (TEnvFresh.nil ((synCfdif R A B)).fv))))

/-- Checked nominal proof certificate identified upstream as `nb086_wpp_refl_0000`. -/
@[expose]
noncomputable def nb086WppRefl0000 (x : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_B_q : q ∉ B.fv)
    (dv_B_x : x ∉ B.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb086AlphaDummy002 A B C R), (nb086AlphaDummy003 x A B R)),
        ((nb086AlphaDummy001 A B C R), x), ((nb086AlphaDummy000 A B C R), q)]
      ((synCfdif R A B)).fv :=
  TEnvFresh.reflOn
    (nb086_compact_envfresh_0001 x A B C R q dv_A_q dv_A_x dv_B_q dv_B_x dv_R_q dv_R_x)

/-- Checked nominal proof certificate identified upstream as `nominal_df_fdcode`. -/
@[expose]
noncomputable def nominalDfFdcode (x : Var) (A : Class) (B : Class) (C : Class)
    (R : Class) (q : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_q : q ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (__dv_B_C : Disjoint B.fv C.fv) (__dv_B_R : Disjoint B.fv R.fv) (dv_B_q : q ∉ B.fv)
    (dv_B_x : x ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv) (dv_C_q : q ∉ C.fv)
    (dv_C_x : x ∉ C.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_q_x : q ≠ x) :
    Nominal.NPrf
      (.classEq (synCfdcode R A B C)
        (.cab q (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb086AlphaDummy001 A B C R), x),
                  ((nb086AlphaDummy000 A B C R), q)]
                C (nb086FocusedRefl0000 x A B C R q dv_C_q dv_C_x))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there
                  (freshVar_injective ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) (by decide))
                  dv_q_x (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.reflOfReflOn
                      [((nb086AlphaDummy002 A B C R), (nb086AlphaDummy003 x A B R)),
                        ((nb086AlphaDummy001 A B C R), x),
                        ((nb086AlphaDummy000 A B C R), q)] (synCfdif R A B)
                      (nb086WppRefl0000 x A B C R q dv_A_q dv_A_x dv_B_q dv_B_x dv_R_q
                        dv_R_x))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                          (nb086AlphaDummy001 A B C R) ≠ (nb086AlphaDummy002 A B C R) from
                          (by
                            unfold nb086AlphaDummy002;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb086_support_mem_0000 A B C R) 0))))
                        (show x ≠ (nb086AlphaDummy003 x A B R) from (by
                            unfold nb086AlphaDummy003;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb086_support_mem_0001 x A B R) 0))))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
