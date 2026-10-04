/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart003

/-! NF weak partition development: NAR4H5C091M3BPart004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0003`. -/
@[expose]
noncomputable def nb091SplitAlpha0003 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy071 D R), (nb091AlphaDummy072 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy071 D R))
          (Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy071 D R))
            (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy072 D R p))
          (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy072 D R p))
            (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
                (Class.cv (nb091AlphaDummy061 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy066 D R) from (by
                      unfold nb091AlphaDummy066;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
                  (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
                      unfold nb091AlphaDummy068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy065 D R) from (by
                        unfold nb091AlphaDummy065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
                    (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy067 D R p) from (by
                        unfold nb091AlphaDummy067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy071 D R) from (by
                          unfold nb091AlphaDummy071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0052 D R) 0))))
                      (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy072 D R p) from
                        (by
                          unfold nb091AlphaDummy072;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0053 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy069 D R) from (by
                            unfold nb091AlphaDummy069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0049 D R) 0)))) (show
                          (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy070 D R p) from (by
                            unfold nb091AlphaDummy070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0051 D R p) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCin D
                                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                                        (synCuni (Class.cv
        (nb091AlphaDummy000 D R)))))))).fv ∪ ((synCin D
                                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                                        (synCuni
        (Class.cv (nb091AlphaDummy000 D R)))))))).fv) (by decide)) (freshVar_injective
                            (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                                    (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪
                              ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                                    (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
                      ((Class.cv (nb091AlphaDummy060 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
                      ((Class.cv (nb091AlphaDummy062 D R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy073 D R) from
                            (by
                              unfold nb091AlphaDummy073;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0054 D R) 0)))) (show
                            (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy075 D R p) from
                            (by
                              unfold nb091AlphaDummy075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                          (TAlphaVar.there (show
                              (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy074 D R) from (by
                                unfold nb091AlphaDummy074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0054 D R) 1)))) (show
                              (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy076 D R p) from
                              (by
                                unfold nb091AlphaDummy076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091AlphaDummy066 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb091AlphaDummy068 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy080 D R) from
        (by
          unfold nb091AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R) 1)))) (show (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy083 D R p) from (by
          unfold nb091AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy079 D R) from (by
          unfold nb091AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  0)))) (show (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy082 D R p) from
        (by
          unfold nb091AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy077 D R) from (by
          unfold nb091AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R)
                  0)))) (show (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
        (by
          unfold nb091AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy081 D R), (nb091AlphaDummy084 D R p)),
        ((nb091AlphaDummy080 D R), (nb091AlphaDummy083 D R p)),
        ((nb091AlphaDummy079 D R), (nb091AlphaDummy082 D R p)),
        ((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
        ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
        ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy071 D R), (nb091AlphaDummy072 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy081 D R), (nb091AlphaDummy084 D R p)),
        ((nb091AlphaDummy080 D R), (nb091AlphaDummy083 D R p)),
        ((nb091AlphaDummy079 D R), (nb091AlphaDummy082 D R p)),
        ((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
        ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
        ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy071 D R), (nb091AlphaDummy072 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R
        p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from
        (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from
        (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081
        D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081
        D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R)
                                      from (by
                                        unfold nb091AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091AlphaDummy075 D R p) ≠
                                        (nb091AlphaDummy078 D R p) from (by
                                        unfold nb091AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                                    ((nb091AlphaDummy073 D R),
                                      (nb091AlphaDummy075 D R p)),
                                    ((nb091AlphaDummy074 D R),
                                      (nb091AlphaDummy076 D R p)),
                                    ((nb091AlphaDummy066 D R),
                                      (nb091AlphaDummy068 D R p)),
                                    ((nb091AlphaDummy065 D R),
                                      (nb091AlphaDummy067 D R p)),
                                    ((nb091AlphaDummy071 D R),
                                      (nb091AlphaDummy072 D R p)),
                                    ((nb091AlphaDummy069 D R),
                                      (nb091AlphaDummy070 D R p)),
                                    ((nb091AlphaDummy060 D R),
                                      (nb091AlphaDummy062 D R p)),
                                    ((nb091AlphaDummy059 D R),
                                      (nb091AlphaDummy061 D R p)),
                                    ((nb091AlphaDummy063 D R),
                                      (nb091AlphaDummy064 D R p)),
                                    ((nb091AlphaDummy057 D R),
                                      (nb091AlphaDummy058 D R p)),
                                    ((nb091AlphaDummy055 D R),
                                      (nb091AlphaDummy056 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy053 D R),
                                      (nb091AlphaDummy054 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R)
                                    from (by
                                      unfold nb091AlphaDummy077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                              0)))) (show (nb091AlphaDummy075 D R p) ≠
                                      (nb091AlphaDummy078 D R p) from (by
                                      unfold nb091AlphaDummy078;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0057 D R p) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R)
                                      from (by
                                        unfold nb091AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091AlphaDummy075 D R p) ≠
                                        (nb091AlphaDummy078 D R p) from (by
                                        unfold nb091AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                                    ((nb091AlphaDummy073 D R),
                                      (nb091AlphaDummy075 D R p)),
                                    ((nb091AlphaDummy074 D R),
                                      (nb091AlphaDummy076 D R p)),
                                    ((nb091AlphaDummy066 D R),
                                      (nb091AlphaDummy068 D R p)),
                                    ((nb091AlphaDummy065 D R),
                                      (nb091AlphaDummy067 D R p)),
                                    ((nb091AlphaDummy071 D R),
                                      (nb091AlphaDummy072 D R p)),
                                    ((nb091AlphaDummy069 D R),
                                      (nb091AlphaDummy070 D R p)),
                                    ((nb091AlphaDummy060 D R),
                                      (nb091AlphaDummy062 D R p)),
                                    ((nb091AlphaDummy059 D R),
                                      (nb091AlphaDummy061 D R p)),
                                    ((nb091AlphaDummy063 D R),
                                      (nb091AlphaDummy064 D R p)),
                                    ((nb091AlphaDummy057 D R),
                                      (nb091AlphaDummy058 D R p)),
                                    ((nb091AlphaDummy055 D R),
                                      (nb091AlphaDummy056 D R p)),
                                    ((nb091AlphaDummy048 D R),
                                      (nb091AlphaDummy050 D R p)),
                                    ((nb091AlphaDummy047 D R),
                                      (nb091AlphaDummy049 D R p)),
                                    ((nb091AlphaDummy053 D R),
                                      (nb091AlphaDummy054 D R p)),
                                    ((nb091AlphaDummy051 D R),
                                      (nb091AlphaDummy052 D R p)),
                                    ((nb091AlphaDummy045 D R),
                                      (nb091AlphaDummy046 D R p)),
                                    ((nb091AlphaDummy042 D R),
                                      (nb091AlphaDummy044 D R p)),
                                    ((nb091AlphaDummy041 D R),
                                      (nb091AlphaDummy043 D R p)),
                                    ((nb091AlphaDummy001 D R),
                                      (nb091AlphaDummy002 D R p)),
                                    ((nb091AlphaDummy000 D R), p),
                                    ((nb091AlphaDummy003 D R),
                                      (nb091AlphaDummy004 D R p))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy066 D R) from (by
                        unfold nb091AlphaDummy066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
                    (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
                        unfold nb091AlphaDummy068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy065 D R) from (by
                          unfold nb091AlphaDummy065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
                      (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy067 D R p) from
                        (by
                          unfold nb091AlphaDummy067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy071 D R) from (by
                            unfold nb091AlphaDummy071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0052 D R) 0)))) (show
                          (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy072 D R p) from (by
                            unfold nb091AlphaDummy072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0053 D R p) 0))))
                        (TAlphaVar.there
                          (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy069 D R) from
                            (by
                              unfold nb091AlphaDummy069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0049 D R) 0)))) (show
                            (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy070 D R p) from
                            (by
                              unfold nb091AlphaDummy070;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0051 D R p) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCin D
                                    (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                        (synCuni (synCuni (Class.cv
        (nb091AlphaDummy000 D R)))))))).fv ∪ ((synCin D
                                    (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                        (synCuni (synCuni (Class.cv
        (nb091AlphaDummy000 D R)))))))).fv) (by decide)) (freshVar_injective (((synCin D
                                    (synCima (synCcnv (synCdif R (synCid)))
                                      (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪
                                ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                                      (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
                        ((Class.cv (nb091AlphaDummy060 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
                        ((Class.cv (nb091AlphaDummy062 D R p))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy073 D R) from (by
                                unfold nb091AlphaDummy073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0054 D R) 0)))) (show
                              (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy075 D R p) from
                              (by
                                unfold nb091AlphaDummy075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy074 D R) from
                                (by
                                  unfold nb091AlphaDummy074;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0054 D R)
                                          1)))) (show (nb091AlphaDummy068 D R p) ≠
                                  (nb091AlphaDummy076 D R p) from (by
                                  unfold nb091AlphaDummy076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb091AlphaDummy066 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb091AlphaDummy068 D R p))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy080 D R) from (by
          unfold nb091AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  1)))) (show (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy083 D R p) from
        (by
          unfold nb091AlphaDummy083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy079 D R) from (by
          unfold nb091AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  0)))) (show (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy082 D R p) from
        (by
          unfold nb091AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy077 D R) from (by
          unfold nb091AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R)
                  0)))) (show (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
        (by
          unfold nb091AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy081 D R), (nb091AlphaDummy084 D R p)),
        ((nb091AlphaDummy080 D R), (nb091AlphaDummy083 D R p)),
        ((nb091AlphaDummy079 D R), (nb091AlphaDummy082 D R p)),
        ((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
        ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
        ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy071 D R), (nb091AlphaDummy072 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy081 D R), (nb091AlphaDummy084 D R p)),
        ((nb091AlphaDummy080 D R), (nb091AlphaDummy083 D R p)),
        ((nb091AlphaDummy079 D R), (nb091AlphaDummy082 D R p)),
        ((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
        ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
        ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy071 D R), (nb091AlphaDummy072 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R
        p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from
        (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from
        (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081
        D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081
        D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy077 D R) from (by
                                          unfold nb091AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0056 D R) 0)))) (show
                                        (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy078 D R p) from (by
                                          unfold nb091AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0057 D R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb091AlphaDummy077 D R),
                                        (nb091AlphaDummy078 D R p)),
                                      ((nb091AlphaDummy073 D R),
                                        (nb091AlphaDummy075 D R p)),
                                      ((nb091AlphaDummy074 D R),
                                        (nb091AlphaDummy076 D R p)),
                                      ((nb091AlphaDummy066 D R),
                                        (nb091AlphaDummy068 D R p)),
                                      ((nb091AlphaDummy065 D R),
                                        (nb091AlphaDummy067 D R p)),
                                      ((nb091AlphaDummy071 D R),
                                        (nb091AlphaDummy072 D R p)),
                                      ((nb091AlphaDummy069 D R),
                                        (nb091AlphaDummy070 D R p)),
                                      ((nb091AlphaDummy060 D R),
                                        (nb091AlphaDummy062 D R p)),
                                      ((nb091AlphaDummy059 D R),
                                        (nb091AlphaDummy061 D R p)),
                                      ((nb091AlphaDummy063 D R),
                                        (nb091AlphaDummy064 D R p)),
                                      ((nb091AlphaDummy057 D R),
                                        (nb091AlphaDummy058 D R p)),
                                      ((nb091AlphaDummy055 D R),
                                        (nb091AlphaDummy056 D R p)),
                                      ((nb091AlphaDummy048 D R),
                                        (nb091AlphaDummy050 D R p)),
                                      ((nb091AlphaDummy047 D R),
                                        (nb091AlphaDummy049 D R p)),
                                      ((nb091AlphaDummy053 D R),
                                        (nb091AlphaDummy054 D R p)),
                                      ((nb091AlphaDummy051 D R),
                                        (nb091AlphaDummy052 D R p)),
                                      ((nb091AlphaDummy045 D R),
                                        (nb091AlphaDummy046 D R p)),
                                      ((nb091AlphaDummy042 D R),
                                        (nb091AlphaDummy044 D R p)),
                                      ((nb091AlphaDummy041 D R),
                                        (nb091AlphaDummy043 D R p)),
                                      ((nb091AlphaDummy001 D R),
                                        (nb091AlphaDummy002 D R p)),
                                      ((nb091AlphaDummy000 D R), p),
                                      ((nb091AlphaDummy003 D R),
                                        (nb091AlphaDummy004 D R p))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R)
                                      from (by
                                        unfold nb091AlphaDummy077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091AlphaDummy075 D R p) ≠
                                        (nb091AlphaDummy078 D R p) from (by
                                        unfold nb091AlphaDummy078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy077 D R) from (by
                                          unfold nb091AlphaDummy077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0056 D R) 0)))) (show
                                        (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy078 D R p) from (by
                                          unfold nb091AlphaDummy078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0057 D R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb091AlphaDummy077 D R),
                                        (nb091AlphaDummy078 D R p)),
                                      ((nb091AlphaDummy073 D R),
                                        (nb091AlphaDummy075 D R p)),
                                      ((nb091AlphaDummy074 D R),
                                        (nb091AlphaDummy076 D R p)),
                                      ((nb091AlphaDummy066 D R),
                                        (nb091AlphaDummy068 D R p)),
                                      ((nb091AlphaDummy065 D R),
                                        (nb091AlphaDummy067 D R p)),
                                      ((nb091AlphaDummy071 D R),
                                        (nb091AlphaDummy072 D R p)),
                                      ((nb091AlphaDummy069 D R),
                                        (nb091AlphaDummy070 D R p)),
                                      ((nb091AlphaDummy060 D R),
                                        (nb091AlphaDummy062 D R p)),
                                      ((nb091AlphaDummy059 D R),
                                        (nb091AlphaDummy061 D R p)),
                                      ((nb091AlphaDummy063 D R),
                                        (nb091AlphaDummy064 D R p)),
                                      ((nb091AlphaDummy057 D R),
                                        (nb091AlphaDummy058 D R p)),
                                      ((nb091AlphaDummy055 D R),
                                        (nb091AlphaDummy056 D R p)),
                                      ((nb091AlphaDummy048 D R),
                                        (nb091AlphaDummy050 D R p)),
                                      ((nb091AlphaDummy047 D R),
                                        (nb091AlphaDummy049 D R p)),
                                      ((nb091AlphaDummy053 D R),
                                        (nb091AlphaDummy054 D R p)),
                                      ((nb091AlphaDummy051 D R),
                                        (nb091AlphaDummy052 D R p)),
                                      ((nb091AlphaDummy045 D R),
                                        (nb091AlphaDummy046 D R p)),
                                      ((nb091AlphaDummy042 D R),
                                        (nb091AlphaDummy044 D R p)),
                                      ((nb091AlphaDummy041 D R),
                                        (nb091AlphaDummy043 D R p)),
                                      ((nb091AlphaDummy001 D R),
                                        (nb091AlphaDummy002 D R p)),
                                      ((nb091AlphaDummy000 D R), p),
                                      ((nb091AlphaDummy003 D R),
                                        (nb091AlphaDummy004 D R p))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0004`. -/
@[expose]
noncomputable def nb091SplitAlpha0004 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
        ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy099 D R))
          (synCphi (Class.cv (nb091AlphaDummy066 D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy099 D R))
            (synCphi (Class.cv (nb091AlphaDummy066 D R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy100 D R p))
          (synCphi (Class.cv (nb091AlphaDummy068 D R p)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy100 D R p))
            (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy073 D R) from (by
                      unfold nb091AlphaDummy073;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0054 D R) 0))))
                  (show (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy075 D R p) from (by
                      unfold nb091AlphaDummy075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                  (TAlphaVar.there
                    (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy074 D R) from (by
                        unfold nb091AlphaDummy074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0054 D R) 1))))
                    (show (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy076 D R p) from (by
                        unfold nb091AlphaDummy076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0055 D R p) 1))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy099 D R) from (by
                          unfold nb091AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0084 D R) 0))))
                      (show (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy100 D R p) from
                        (by
                          unfold nb091AlphaDummy100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0085 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy097 D R) from (by
                            unfold nb091AlphaDummy097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0082 D R) 0)))) (show
                          (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy098 D R p) from (by
                            unfold nb091AlphaDummy098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0083 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb091AlphaDummy066 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091AlphaDummy068 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy080 D R)
                                      from (by
                                        unfold nb091AlphaDummy080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0058 D R) 1)))) (show
                                      (nb091AlphaDummy075 D R p) ≠
                                        (nb091AlphaDummy083 D R p) from (by
                                        unfold nb091AlphaDummy083;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0059 D R p) 1))))
                                    (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy079 D R) from (by
                                          unfold nb091AlphaDummy079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0058 D R) 0)))) (show
                                        (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy082 D R p) from (by
                                          unfold nb091AlphaDummy082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0059 D R p) 0))))
                                      (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy077 D R) from (by
          unfold nb091AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R) 0)))) (show (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy078 D R p) from (by
          unfold nb091AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb091AlphaDummy081 D R),
        (nb091AlphaDummy084 D R p)), ((nb091AlphaDummy080 D R),
        (nb091AlphaDummy083 D R p)), ((nb091AlphaDummy079 D R),
        (nb091AlphaDummy082 D R p)), ((nb091AlphaDummy077 D R),
        (nb091AlphaDummy078 D R p)), ((nb091AlphaDummy073 D R),
        (nb091AlphaDummy075 D R p)), ((nb091AlphaDummy074 D R),
        (nb091AlphaDummy076 D R p)), ((nb091AlphaDummy099 D R),
        (nb091AlphaDummy100 D R p)), ((nb091AlphaDummy097 D R),
        (nb091AlphaDummy098 D R p)), ((nb091AlphaDummy066 D R),
        (nb091AlphaDummy068 D R p)), ((nb091AlphaDummy065 D R),
        (nb091AlphaDummy067 D R p)), ((nb091AlphaDummy095 D R),
        (nb091AlphaDummy096 D R p)), ((nb091AlphaDummy069 D R),
        (nb091AlphaDummy070 D R p)), ((nb091AlphaDummy060 D R),
        (nb091AlphaDummy062 D R p)), ((nb091AlphaDummy059 D R),
        (nb091AlphaDummy061 D R p)), ((nb091AlphaDummy063 D R),
        (nb091AlphaDummy064 D R p)), ((nb091AlphaDummy057 D R),
        (nb091AlphaDummy058 D R p)), ((nb091AlphaDummy055 D R),
        (nb091AlphaDummy056 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy053 D R),
        (nb091AlphaDummy054 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
                                        ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy087 D R) from (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy087 D R) from (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb091AlphaDummy081 D R),
        (nb091AlphaDummy084 D R p)), ((nb091AlphaDummy080 D R),
        (nb091AlphaDummy083 D R p)), ((nb091AlphaDummy079 D R),
        (nb091AlphaDummy082 D R p)), ((nb091AlphaDummy077 D R),
        (nb091AlphaDummy078 D R p)), ((nb091AlphaDummy073 D R),
        (nb091AlphaDummy075 D R p)), ((nb091AlphaDummy074 D R),
        (nb091AlphaDummy076 D R p)), ((nb091AlphaDummy099 D R),
        (nb091AlphaDummy100 D R p)), ((nb091AlphaDummy097 D R),
        (nb091AlphaDummy098 D R p)), ((nb091AlphaDummy066 D R),
        (nb091AlphaDummy068 D R p)), ((nb091AlphaDummy065 D R),
        (nb091AlphaDummy067 D R p)), ((nb091AlphaDummy095 D R),
        (nb091AlphaDummy096 D R p)), ((nb091AlphaDummy069 D R),
        (nb091AlphaDummy070 D R p)), ((nb091AlphaDummy060 D R),
        (nb091AlphaDummy062 D R p)), ((nb091AlphaDummy059 D R),
        (nb091AlphaDummy061 D R p)), ((nb091AlphaDummy063 D R),
        (nb091AlphaDummy064 D R p)), ((nb091AlphaDummy057 D R),
        (nb091AlphaDummy058 D R p)), ((nb091AlphaDummy055 D R),
        (nb091AlphaDummy056 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy053 D R),
        (nb091AlphaDummy054 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy091 D R) from (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from (by
                                unfold nb091AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
                              (by
                                unfold nb091AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                            ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
                            ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
                            ((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
                            ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
                            ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
                            ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
                            ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
                            ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
                            ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
                            ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
                            ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
                            ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
                            ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
                            ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                            ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                            ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
                            ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                            ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                            ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                            ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                            ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                            ((nb091AlphaDummy000 D R), p),
                            ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from
                            (by
                              unfold nb091AlphaDummy077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                            (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
                            (by
                              unfold nb091AlphaDummy078;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0057 D R p) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from (by
                                unfold nb091AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
                              (by
                                unfold nb091AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                            ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
                            ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
                            ((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
                            ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
                            ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
                            ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
                            ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
                            ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
                            ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
                            ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
                            ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
                            ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
                            ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
                            ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                            ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                            ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
                            ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                            ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                            ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                            ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                            ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                            ((nb091AlphaDummy000 D R), p),
                            ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy073 D R) from (by
                        unfold nb091AlphaDummy073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0054 D R) 0))))
                    (show (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy075 D R p) from (by
                        unfold nb091AlphaDummy075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy074 D R) from (by
                          unfold nb091AlphaDummy074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0054 D R) 1))))
                      (show (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy076 D R p) from
                        (by
                          unfold nb091AlphaDummy076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0055 D R p) 1))))
                      (TAlphaVar.there
                        (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy099 D R) from (by
                            unfold nb091AlphaDummy099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0084 D R) 0)))) (show
                          (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy100 D R p) from (by
                            unfold nb091AlphaDummy100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0085 D R p) 0))))
                        (TAlphaVar.there
                          (show (nb091AlphaDummy066 D R) ≠ (nb091AlphaDummy097 D R) from
                            (by
                              unfold nb091AlphaDummy097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0082 D R) 0)))) (show
                            (nb091AlphaDummy068 D R p) ≠ (nb091AlphaDummy098 D R p) from
                            (by
                              unfold nb091AlphaDummy098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0083 D R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb091AlphaDummy066 D R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb091AlphaDummy068 D R p))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy080 D R) from (by
                                          unfold nb091AlphaDummy080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0058 D R) 1)))) (show
                                        (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy083 D R p) from (by
                                          unfold nb091AlphaDummy083;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0059 D R p) 1))))
                                      (TAlphaVar.there (show (nb091AlphaDummy073 D R) ≠
        (nb091AlphaDummy079 D R) from (by
          unfold nb091AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R) 0)))) (show (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy082 D R p) from (by
          unfold nb091AlphaDummy082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from (by
          unfold nb091AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R) 0)))) (show (nb091AlphaDummy075 D R p) ≠
        (nb091AlphaDummy078 D R p) from (by
          unfold nb091AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb091AlphaDummy081 D R),
        (nb091AlphaDummy084 D R p)), ((nb091AlphaDummy080 D R),
        (nb091AlphaDummy083 D R p)), ((nb091AlphaDummy079 D R),
        (nb091AlphaDummy082 D R p)), ((nb091AlphaDummy077 D R),
        (nb091AlphaDummy078 D R p)), ((nb091AlphaDummy073 D R),
        (nb091AlphaDummy075 D R p)), ((nb091AlphaDummy074 D R),
        (nb091AlphaDummy076 D R p)), ((nb091AlphaDummy099 D R),
        (nb091AlphaDummy100 D R p)), ((nb091AlphaDummy097 D R),
        (nb091AlphaDummy098 D R p)), ((nb091AlphaDummy066 D R),
        (nb091AlphaDummy068 D R p)), ((nb091AlphaDummy065 D R),
        (nb091AlphaDummy067 D R p)), ((nb091AlphaDummy095 D R),
        (nb091AlphaDummy096 D R p)), ((nb091AlphaDummy069 D R),
        (nb091AlphaDummy070 D R p)), ((nb091AlphaDummy060 D R),
        (nb091AlphaDummy062 D R p)), ((nb091AlphaDummy059 D R),
        (nb091AlphaDummy061 D R p)), ((nb091AlphaDummy063 D R),
        (nb091AlphaDummy064 D R p)), ((nb091AlphaDummy057 D R),
        (nb091AlphaDummy058 D R p)), ((nb091AlphaDummy055 D R),
        (nb091AlphaDummy056 D R p)), ((nb091AlphaDummy048 D R),
        (nb091AlphaDummy050 D R p)), ((nb091AlphaDummy047 D R),
        (nb091AlphaDummy049 D R p)), ((nb091AlphaDummy053 D R),
        (nb091AlphaDummy054 D R p)), ((nb091AlphaDummy051 D R),
        (nb091AlphaDummy052 D R p)), ((nb091AlphaDummy045 D R),
        (nb091AlphaDummy046 D R p)), ((nb091AlphaDummy042 D R),
        (nb091AlphaDummy044 D R p)), ((nb091AlphaDummy041 D R),
        (nb091AlphaDummy043 D R p)), ((nb091AlphaDummy001 D R),
        (nb091AlphaDummy002 D R p)), ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy080 D
        R) ≠ (nb091AlphaDummy087 D R) from (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠ (nb091AlphaDummy087 D R) from
        (by
          unfold
            nb091AlphaDummy087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy088 D R p) from
        (by
          unfold
            nb091AlphaDummy088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy085 D R) from (by
          unfold
            nb091AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy086 D R p) from
        (by
          unfold
            nb091AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy081 D R), (nb091AlphaDummy084 D R p)),
        ((nb091AlphaDummy080 D R), (nb091AlphaDummy083 D R p)),
        ((nb091AlphaDummy079 D R), (nb091AlphaDummy082 D R p)),
        ((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
        ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
        ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
        ((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
        ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
        ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
        ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
        ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
        ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy080 D
        R) ≠ (nb091AlphaDummy091 D R) from (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠ (nb091AlphaDummy091 D R) from
        (by
          unfold
            nb091AlphaDummy091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy092 D R p) from
        (by
          unfold
            nb091AlphaDummy092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy080 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091AlphaDummy083 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy073
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081 D
        R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy081 D
        R) ≠ (nb091AlphaDummy093 D R) from (by
          unfold
            nb091AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy094 D R p) from
        (by
          unfold
            nb091AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy081 D R) ≠
        (nb091AlphaDummy089 D R) from (by
          unfold
            nb091AlphaDummy089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091AlphaDummy084 D R p) ≠ (nb091AlphaDummy090 D R p) from
        (by
          unfold
            nb091AlphaDummy090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from
                                (by
                                  unfold nb091AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                          0)))) (show (nb091AlphaDummy075 D R p) ≠
                                  (nb091AlphaDummy078 D R p) from (by
                                  unfold nb091AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                              ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
                              ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
                              ((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
                              ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
                              ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
                              ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
                              ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
                              ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
                              ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
                              ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
                              ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
                              ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
                              ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
                              ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                              ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                              ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
                              ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                              ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                              ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                              ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                              ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                              ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
                                (nb091AlphaDummy004 D R p))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from (by
                                unfold nb091AlphaDummy077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091AlphaDummy075 D R p) ≠ (nb091AlphaDummy078 D R p) from
                              (by
                                unfold nb091AlphaDummy078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091AlphaDummy073 D R) ≠ (nb091AlphaDummy077 D R) from
                                (by
                                  unfold nb091AlphaDummy077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                          0)))) (show (nb091AlphaDummy075 D R p) ≠
                                  (nb091AlphaDummy078 D R p) from (by
                                  unfold nb091AlphaDummy078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb091AlphaDummy077 D R), (nb091AlphaDummy078 D R p)),
                              ((nb091AlphaDummy073 D R), (nb091AlphaDummy075 D R p)),
                              ((nb091AlphaDummy074 D R), (nb091AlphaDummy076 D R p)),
                              ((nb091AlphaDummy099 D R), (nb091AlphaDummy100 D R p)),
                              ((nb091AlphaDummy097 D R), (nb091AlphaDummy098 D R p)),
                              ((nb091AlphaDummy066 D R), (nb091AlphaDummy068 D R p)),
                              ((nb091AlphaDummy065 D R), (nb091AlphaDummy067 D R p)),
                              ((nb091AlphaDummy095 D R), (nb091AlphaDummy096 D R p)),
                              ((nb091AlphaDummy069 D R), (nb091AlphaDummy070 D R p)),
                              ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
                              ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
                              ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
                              ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
                              ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
                              ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
                              ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
                              ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
                              ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
                              ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
                              ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                              ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                              ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                              ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
                                (nb091AlphaDummy004 D R p))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb091_focused_notmem_0028 (D : Class) (R : Class) :
    (nb091AlphaDummy103 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0029 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy104 D R p) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p)))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0030 (D : Class) (R : Class) :
    (nb091AlphaDummy101 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
          ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0031 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy102 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCnin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0032 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0033 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0034 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0035 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0036 (D : Class) (R : Class) :
    (nb091AlphaDummy063 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
            ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
              (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
      (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091AlphaDummy059 D R))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0037 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy064 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
            ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))))
              (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))
      (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091AlphaDummy061 D R p))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0038 (D : Class) (R : Class) :
    (nb091AlphaDummy057 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0039 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy058 D R p) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0040 (D : Class) (R : Class) :
    (nb091AlphaDummy055 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0041 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy056 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0042 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0043 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0044 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0045 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0046 (D : Class) (R : Class) :
    (nb091AlphaDummy053 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
          ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091AlphaDummy047 D R)
      (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0044 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy048 D R)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0042 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0047 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy054 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
          ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091AlphaDummy049 D R p)
      (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0045 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy050 D R p)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0043 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0048 (D : Class) (R : Class) :
    (nb091AlphaDummy051 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb091AlphaDummy047 D R)
                (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                              (synCuni (Class.cv (nb091AlphaDummy000 D R))))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                              (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                    (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
              (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
          (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
            (synCphi (Class.cv (nb091AlphaDummy048 D R))))))]
  rw [fv_class_cab (nb091AlphaDummy047 D R)
      (synWrex (nb091AlphaDummy048 D R) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0044 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy048 D R)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
          (synCphi (Class.cv (nb091AlphaDummy048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0042 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0049 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy052 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
                (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (synCuni (synCuni (Class.cv p))))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                    (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
              (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                  (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))
                  (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                      (synCsn (synC0c)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
          (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))
          (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
            (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))]
  rw [fv_class_cab (nb091AlphaDummy049 D R p)
      (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0045 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091AlphaDummy050 D R p)
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
          (synCphi (Class.cv (nb091AlphaDummy050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0043 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0050 (D : Class) (R : Class) :
    (nb091AlphaDummy045 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synChnwcutcode R D
            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0051 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy046 D R p) ∉ D.fv :=
  by
  change freshVar (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) 0 ∉ D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (synCuni (synCuni (Class.cv p)))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0052 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0053 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪
          ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0054 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0055 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((synChwniso D)).fv ∪
          ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_compact_envfresh_0016 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091AlphaDummy103 D R) (nb091AlphaDummy104 D R p)
      (nb091_focused_notmem_0028 D R) (nb091_focused_notmem_0029 D R p)
      (TEnvFresh.consFresh (nb091AlphaDummy101 D R) (nb091AlphaDummy102 D R p)
        (nb091_focused_notmem_0030 D R) (nb091_focused_notmem_0031 D R p)
        (TEnvFresh.consFresh (nb091AlphaDummy060 D R) (nb091AlphaDummy062 D R p)
          (nb091_focused_notmem_0032 D R) (nb091_focused_notmem_0033 D R p)
          (TEnvFresh.consFresh (nb091AlphaDummy059 D R) (nb091AlphaDummy061 D R p)
            (nb091_focused_notmem_0034 D R) (nb091_focused_notmem_0035 D R p)
            (TEnvFresh.consFresh (nb091AlphaDummy063 D R) (nb091AlphaDummy064 D R p)
              (nb091_focused_notmem_0036 D R) (nb091_focused_notmem_0037 D R p)
              (TEnvFresh.consFresh (nb091AlphaDummy057 D R)
                (nb091AlphaDummy058 D R p) (nb091_focused_notmem_0038 D R)
                (nb091_focused_notmem_0039 D R p)
                (TEnvFresh.consFresh (nb091AlphaDummy055 D R)
                  (nb091AlphaDummy056 D R p) (nb091_focused_notmem_0040 D R)
                  (nb091_focused_notmem_0041 D R p)
                  (TEnvFresh.consFresh (nb091AlphaDummy048 D R)
                    (nb091AlphaDummy050 D R p) (nb091_focused_notmem_0042 D R)
                    (nb091_focused_notmem_0043 D R p)
                    (TEnvFresh.consFresh (nb091AlphaDummy047 D R)
                      (nb091AlphaDummy049 D R p) (nb091_focused_notmem_0044 D R)
                      (nb091_focused_notmem_0045 D R p)
                      (TEnvFresh.consFresh (nb091AlphaDummy053 D R)
                        (nb091AlphaDummy054 D R p) (nb091_focused_notmem_0046 D R)
                        (nb091_focused_notmem_0047 D R p)
                        (TEnvFresh.consFresh (nb091AlphaDummy051 D R)
                          (nb091AlphaDummy052 D R p) (nb091_focused_notmem_0048 D R)
                          (nb091_focused_notmem_0049 D R p)
                          (TEnvFresh.consFresh (nb091AlphaDummy045 D R)
                            (nb091AlphaDummy046 D R p) (nb091_focused_notmem_0050 D R)
                            (nb091_focused_notmem_0051 D R p)
                            (TEnvFresh.consFresh (nb091AlphaDummy042 D R)
                              (nb091AlphaDummy044 D R p) (nb091_focused_notmem_0052 D R)
                              (nb091_focused_notmem_0053 D R p)
                              (TEnvFresh.consFresh (nb091AlphaDummy041 D R)
                                (nb091AlphaDummy043 D R p) (nb091_focused_notmem_0054 D R)
                                (nb091_focused_notmem_0055 D R p)
                                (TEnvFresh.consFresh (nb091AlphaDummy001 D R)
                                  (nb091AlphaDummy002 D R p) (nb091_focused_notmem_0000 D R)
                                  (nb091_focused_notmem_0001 D R p)
                                  (TEnvFresh.consFresh (nb091AlphaDummy000 D R) p
                                    (nb091_focused_notmem_0002 D R) dv_D_p
                                    (TEnvFresh.consFresh (nb091AlphaDummy003 D R)
                                      (nb091AlphaDummy004 D R p)
                                      (nb091_focused_notmem_0003 D R)
                                      (nb091_focused_notmem_0004 D R p)
                                      (TEnvFresh.nil D.fv))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb091_focused_refl_0001`. -/
@[expose]
noncomputable def nb091FocusedRefl0001 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      D.fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0016 D R p dv_D_p)

theorem nb091_compact_fv_empty_0102 (D : Class) (R : Class) :
    (nb091AlphaDummy106 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0103 (R : Class) (p : Var) :
    (nb091AlphaDummy108 R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0104 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0105 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0106 (D : Class) (R : Class) :
    (nb091AlphaDummy103 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0107 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy104 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0108 (D : Class) (R : Class) :
    (nb091AlphaDummy101 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0109 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy102 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
