/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C059C001Block001

/-! NF weak partition development: NAR4C059C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0004`. -/
@[expose]
noncomputable def nb059SplitAlpha0004 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy047 R S_cls))
          (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
              (Class.cv (nb059AlphaDummy013 R S_cls))
              (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb059AlphaDummy047 R S_cls))
            (Class.cab (nb059AlphaDummy017 R S_cls) (synWrex (nb059AlphaDummy018 R S_cls)
                (Class.cv (nb059AlphaDummy013 R S_cls))
                (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy018 R S_cls)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy048 R a))
          (Class.cab (nb059AlphaDummy019 R a)
            (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
              (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb059AlphaDummy048 R a))
            (Class.cab (nb059AlphaDummy019 R a)
              (synWrex (nb059AlphaDummy020 R a) (Class.cv (nb059AlphaDummy015 R a))
                (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
                  (synCun (synCphi (Class.cv (nb059AlphaDummy020 R a)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy018 R S_cls) from
                    (by
                      unfold nb059AlphaDummy018;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))))
                  (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy020 R a) from (by
                      unfold nb059AlphaDummy020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0040 R a) 1)))) (TAlphaVar.there
                    (show (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy017 R S_cls) from
                      (by
                        unfold nb059AlphaDummy017;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))))
                    (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy019 R a) from (by
                        unfold nb059AlphaDummy019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))))
                    (TAlphaVar.there (show
                        (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy047 R S_cls) from
                        (by
                          unfold nb059AlphaDummy047;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0042 R S_cls) 0))))
                      (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy048 R a) from (by
                          unfold nb059AlphaDummy048;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0043 R a) 0))))
                      (TAlphaVar.there (show (nb059AlphaDummy013 R S_cls) ≠
                            (nb059AlphaDummy021 R S_cls) from (by
                            unfold nb059AlphaDummy021;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0039 R S_cls) 0))))
                        (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy022 R a) from (by
                            unfold nb059AlphaDummy022;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0041 R a) 0))))
                        (TAlphaVar.there (freshVar_injective
                            ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv)
                            (by decide))
                          (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
                      ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
                      ((Class.cv (nb059AlphaDummy015 R a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb059SplitAlpha0003 R S_cls a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb059SplitAlpha0003 R S_cls a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
                          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                          ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
                          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                          ((nb059AlphaDummy000 R S_cls), a),
                          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
                          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show
                      (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy018 R S_cls) from (by
                        unfold nb059AlphaDummy018;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))))
                    (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy020 R a) from (by
                        unfold nb059AlphaDummy020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))))
                    (TAlphaVar.there (show
                        (nb059AlphaDummy013 R S_cls) ≠ (nb059AlphaDummy017 R S_cls) from
                        (by
                          unfold nb059AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))))
                      (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy019 R a) from (by
                          unfold nb059AlphaDummy019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))))
                      (TAlphaVar.there (show (nb059AlphaDummy013 R S_cls) ≠
                            (nb059AlphaDummy047 R S_cls) from (by
                            unfold nb059AlphaDummy047;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0042 R S_cls) 0))))
                        (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy048 R a) from (by
                            unfold nb059AlphaDummy048;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0043 R a) 0))))
                        (TAlphaVar.there (show (nb059AlphaDummy013 R S_cls) ≠
                              (nb059AlphaDummy021 R S_cls) from (by
                              unfold nb059AlphaDummy021;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0039 R S_cls)
                                      0))))
                          (show (nb059AlphaDummy015 R a) ≠ (nb059AlphaDummy022 R a) from
                            (by
                              unfold nb059AlphaDummy022;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0041 R a) 0))))
                          (TAlphaVar.there (freshVar_injective
                              ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv)
                              (by decide))
                            (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
                        ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
                        ((Class.cv (nb059AlphaDummy015 R a))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb059SplitAlpha0003 R S_cls a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb059SplitAlpha0003 R S_cls a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
                            ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                            ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                            ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
                            ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                            ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                            ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                            ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                            ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                            ((nb059AlphaDummy000 R S_cls), a),
                            ((nb059AlphaDummy002 R S_cls),
                              (nb059AlphaDummy004 R S_cls a)),
                            ((nb059AlphaDummy001 R S_cls),
                              (nb059AlphaDummy003 R S_cls a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb059_focused_notmem_0009 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0148 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy014 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0009 R S_cls)

theorem nb059_focused_notmem_0010 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((Class.cv a)).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0149 (R : Class) (a : Var) :
    (nb059AlphaDummy016 R a) ∉ (R).fv := by exact (nb059_focused_notmem_0010 R a)

theorem nb059_focused_notmem_0011 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy013 R S_cls) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((Class.cv (nb059AlphaDummy000 R S_cls))).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0150 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy013 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0011 R S_cls)

theorem nb059_focused_notmem_0012 (R : Class) (a : Var) :
    (nb059AlphaDummy015 R a) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((Class.cv a)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb059_wpp_notmem_0151 (R : Class) (a : Var) :
    (nb059AlphaDummy015 R a) ∉ (R).fv := by exact (nb059_focused_notmem_0012 R a)

theorem nb059_focused_notmem_0013 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy011 R S_cls) ∉ R.fv :=
  by
  change
    freshVar
        (((synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
          ((Class.cv (nb059AlphaDummy000 R S_cls))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima R (Class.cv (nb059AlphaDummy000 R S_cls))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb059_wpp_notmem_0152 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy011 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0013 R S_cls)

theorem nb059_focused_notmem_0014 (R : Class) (a : Var) :
    (nb059AlphaDummy012 R a) ∉ R.fv :=
  by
  change freshVar (((synCima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) 0 ∉ R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cima R (Class.cv a)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb059_wpp_notmem_0153 (R : Class) (a : Var) :
    (nb059AlphaDummy012 R a) ∉ (R).fv := by exact (nb059_focused_notmem_0014 R a)

theorem nb059_relation_support (R : Class) (a : Var) {u : Var} (hu : u ∈ R.fv) :
    u ∈ (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv :=
  by
  rw [fv_syn_cnin, fv_syn_cima]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

theorem nb059_predicate_support (R S : Class) (a : Var) (ha : a ∉ R.fv) {u : Var}
    (hu : u ∈ R.fv) :
    u ∈
      (Class.cab a (synWa (synWss S (Class.cv a))
            (synWss (synCima R (Class.cv a)) (Class.cv a)))).fv :=
  by
  rw [fv_class_cab, Finset.mem_erase]
  refine ⟨?_, ?_⟩
  · intro h
    exact ha (h ▸ hu)
  · rw [fv_syn_wa, fv_syn_wss, fv_syn_wss, fv_syn_cima]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))

theorem nb059_fresh_relation (R : Class) (a : Var) (offset : Nat) :
    freshVar
        ((synCnin (synCima R (Class.cv a)) (Class.cv a)).fv ∪
          (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv)
        offset ∉
      R.fv :=
  by
  have subset :
    ∀ {u : Var},
      u ∈ R.fv →
        u ∈
          (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv ∪
            (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv :=
    by
    intro u hu
    with_reducible
      exact
        (Finset.mem_union_left (a := u) (s :=
          (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv)
          (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv
          (nb059_relation_support R a (u := u) hu))
  with_reducible
    exact
      (NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset (small :=
        R.fv) (large := (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv ∪
          (synCnin (synCima R (Class.cv a)) (Class.cv a)).fv) offset (fun _ hu => subset hu))

theorem nb059_focused_notmem_0015 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy009 R S_cls) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))).fv ∪
          ((synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls)))).fv)
        0 ∉
      R.fv
  exact nb059_fresh_relation R (nb059AlphaDummy000 R S_cls) 0

theorem nb059_wpp_notmem_0154 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy009 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0015 R S_cls)

theorem nb059_focused_notmem_0016 (R : Class) (a : Var) :
    (nb059AlphaDummy010 R a) ∉ R.fv :=
  by
  change
    freshVar
        (((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv ∪
          ((synCnin (synCima R (Class.cv a)) (Class.cv a))).fv)
        0 ∉
      R.fv
  exact nb059_fresh_relation R a 0

theorem nb059_wpp_notmem_0155 (R : Class) (a : Var) :
    (nb059AlphaDummy010 R a) ∉ (R).fv := by exact (nb059_focused_notmem_0016 R a)

theorem nb059_focused_notmem_0017 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∉ R.fv :=
  by
  change freshVar ((S_cls).fv ∪ (R).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb059_wpp_notmem_0156 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy000 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0017 R S_cls)

theorem nb059_wpp_notmem_0157 (R : Class) (a : Var) (dv_R_a : a ∉ R.fv) : a ∉ (R).fv := by
  exact dv_R_a

theorem nb059_focused_notmem_0018 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy002 R S_cls) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb059AlphaDummy000 R S_cls)
            (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
              (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
                (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv)
        1 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => nb059_predicate_support R S_cls (nb059AlphaDummy000 R S_cls)
          (nb059_focused_notmem_0017 R S_cls) hu)

theorem nb059_wpp_notmem_0158 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy002 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0018 R S_cls)

theorem nb059_focused_notmem_0019 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) : (nb059AlphaDummy004 R S_cls a) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab a (synWa (synWss S_cls (Class.cv a))
              (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv)
        1 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => nb059_predicate_support R S_cls a dv_R_a hu)

theorem nb059_wpp_notmem_0159 (R : Class) (S_cls : Class) (a : Var) (dv_R_a : a ∉ R.fv) :
    (nb059AlphaDummy004 R S_cls a) ∉ (R).fv := by
  exact (nb059_focused_notmem_0019 R S_cls a dv_R_a)

theorem nb059_focused_notmem_0020 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy001 R S_cls) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab (nb059AlphaDummy000 R S_cls)
            (synWa (synWss S_cls (Class.cv (nb059AlphaDummy000 R S_cls)))
              (synWss (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
                (Class.cv (nb059AlphaDummy000 R S_cls)))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => nb059_predicate_support R S_cls (nb059AlphaDummy000 R S_cls)
          (nb059_focused_notmem_0017 R S_cls) hu)

theorem nb059_wpp_notmem_0160 (R : Class) (S_cls : Class) :
    (nb059AlphaDummy001 R S_cls) ∉ (R).fv := by
  exact (nb059_focused_notmem_0020 R S_cls)

theorem nb059_focused_notmem_0021 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) : (nb059AlphaDummy003 R S_cls a) ∉ R.fv :=
  by
  change
    freshVar
        (((Class.cab a (synWa (synWss S_cls (Class.cv a))
              (synWss (synCima R (Class.cv a)) (Class.cv a))))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => nb059_predicate_support R S_cls a dv_R_a hu)

theorem nb059_wpp_notmem_0161 (R : Class) (S_cls : Class) (a : Var) (dv_R_a : a ∉ R.fv) :
    (nb059AlphaDummy003 R S_cls a) ∉ (R).fv := by
  exact (nb059_focused_notmem_0021 R S_cls a dv_R_a)

theorem nb059_compact_envfresh_0009 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TEnvFresh
      [((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (R).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb059AlphaDummy014 R S_cls) (nb059AlphaDummy016 R a)
      (nb059_wpp_notmem_0148 R S_cls) (nb059_wpp_notmem_0149 R a)
      (TEnvFresh.consFresh (nb059AlphaDummy013 R S_cls) (nb059AlphaDummy015 R a)
        (nb059_wpp_notmem_0150 R S_cls) (nb059_wpp_notmem_0151 R a)
        (TEnvFresh.consFresh (nb059AlphaDummy011 R S_cls) (nb059AlphaDummy012 R a)
          (nb059_wpp_notmem_0152 R S_cls) (nb059_wpp_notmem_0153 R a)
          (TEnvFresh.consFresh (nb059AlphaDummy009 R S_cls) (nb059AlphaDummy010 R a)
            (nb059_wpp_notmem_0154 R S_cls) (nb059_wpp_notmem_0155 R a)
            (TEnvFresh.consFresh (nb059AlphaDummy000 R S_cls) a
              (nb059_wpp_notmem_0156 R S_cls) (nb059_wpp_notmem_0157 R a dv_R_a)
              (TEnvFresh.consFresh (nb059AlphaDummy002 R S_cls)
                (nb059AlphaDummy004 R S_cls a) (nb059_wpp_notmem_0158 R S_cls)
                (nb059_wpp_notmem_0159 R S_cls a dv_R_a)
                (TEnvFresh.consFresh (nb059AlphaDummy001 R S_cls)
                  (nb059AlphaDummy003 R S_cls a) (nb059_wpp_notmem_0160 R S_cls)
                  (nb059_wpp_notmem_0161 R S_cls a dv_R_a) (TEnvFresh.nil (R).fv))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
