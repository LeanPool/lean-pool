/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart007

/-! NF weak partition development: NAR4H5C091M3BPart008. -/


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

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0013`. -/
@[expose]
noncomputable def nb091SplitAlpha0013 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy184 D R))
          (Class.cv (nb091AlphaDummy041 D R))) (Wff.neg
          (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
            (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy186 D R p))
          (Class.cv (nb091AlphaDummy043 D R p))) (Wff.neg
          (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
            (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy184 D R) from
            (by
              unfold nb091AlphaDummy184;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
          (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy186 D R p) from (by
              unfold nb091AlphaDummy186;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
          (TAlphaVar.there (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy183 D R) from
              (by
                unfold nb091AlphaDummy183;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
            (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy185 D R p) from (by
                unfold nb091AlphaDummy185;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
            (TAlphaVar.there
              (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy213 D R) from (by
                  unfold nb091AlphaDummy213;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0214 D R) 0))))
              (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy214 D R p) from (by
                  unfold nb091AlphaDummy214;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0215 D R p) 0))))
              (TAlphaVar.there
                (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy187 D R) from (by
                    unfold nb091AlphaDummy187;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0211 D R) 0))))
                (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy188 D R p) from (by
                    unfold nb091AlphaDummy188;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb091_support_mem_0213 D R p) 0)))) (TAlphaVar.there
                  (freshVar_injective (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
                            (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
                    (by decide)) (freshVar_injective (((synChwniso D)).fv ∪ ((synCsn
                          (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
                ((Class.cv (nb091AlphaDummy041 D R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
                ((Class.cv (nb091AlphaDummy043 D R p))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy191 D R)
                                      from (by
                                        unfold nb091AlphaDummy191;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 0)))) (show
                                      (nb091AlphaDummy186 D R p) ≠
                                        (nb091AlphaDummy193 D R p) from (by
                                        unfold nb091AlphaDummy193;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
        (nb091AlphaDummy192 D R) from (by
                                          unfold nb091AlphaDummy192;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0188 D R) 1)))) (show
                                        (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy194 D R p) from (by
                                          unfold nb091AlphaDummy194;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0189 D R p) 1))))
                                      (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
        (nb091AlphaDummy217 D R) from (by
          unfold nb091AlphaDummy217;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0218 D R) 0)))) (show (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy218 D R p) from (by
          unfold nb091AlphaDummy218;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0219 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy215 D R) from (by
          unfold nb091AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0216 D R) 0)))) (show (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy216 D R p) from (by
          unfold nb091AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0217 D R p) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb091AlphaDummy184 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb091AlphaDummy186 D R p))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy198 D R) from
        (by
          unfold nb091AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  1)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy201 D R p) from
        (by
          unfold nb091AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy197 D R) from (by
          unfold nb091AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy200 D R p) from
        (by
          unfold nb091AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold
            nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold
            nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠ (nb091AlphaDummy211 D R) from
        (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy211 D R) from (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from
        (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy191 D R)
                                      from (by
                                        unfold nb091AlphaDummy191;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 0)))) (show
                                      (nb091AlphaDummy186 D R p) ≠
                                        (nb091AlphaDummy193 D R p) from (by
                                        unfold nb091AlphaDummy193;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 0))))
                                    (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
        (nb091AlphaDummy192 D R) from (by
                                          unfold nb091AlphaDummy192;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0188 D R) 1)))) (show
                                        (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy194 D R p) from (by
                                          unfold nb091AlphaDummy194;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0189 D R p) 1))))
                                      (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
        (nb091AlphaDummy217 D R) from (by
          unfold nb091AlphaDummy217;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0218 D R) 0)))) (show (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy218 D R p) from (by
          unfold nb091AlphaDummy218;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0219 D R p) 0)))) (TAlphaVar.there (show
        (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy215 D R) from (by
          unfold nb091AlphaDummy215;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0216 D R) 0)))) (show (nb091AlphaDummy186 D R p) ≠
        (nb091AlphaDummy216 D R p) from (by
          unfold nb091AlphaDummy216;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0217 D R p) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb091AlphaDummy184 D R))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb091AlphaDummy186 D R p))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy198 D R) from
        (by
          unfold nb091AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  1)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy201 D R p) from
        (by
          unfold nb091AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy197 D R) from (by
          unfold nb091AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy200 D R p) from
        (by
          unfold nb091AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold
            nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold
            nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠ (nb091AlphaDummy211 D R) from
        (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy211 D R) from (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from
        (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy217 D R), (nb091AlphaDummy218 D R p)),
        ((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb091AlphaDummy215 D R), (nb091AlphaDummy216 D R p)),
                    ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
                    ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
                    ((nb091AlphaDummy213 D R), (nb091AlphaDummy214 D R p)),
                    ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
                    ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                    ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                    ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                    ((nb091AlphaDummy000 D R), p),
                    ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb091_split_alpha_0014`. -/
@[expose]
noncomputable def nb091SplitAlpha0014 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy187 D R)) (synCcompl
            (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy187 D R)) (synCcompl
              (Class.cab (nb091AlphaDummy183 D R) (synWrex (nb091AlphaDummy184 D R)
                  (Class.cv (nb091AlphaDummy041 D R))
                  (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091AlphaDummy188 D R p)) (synCcompl
            (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                (Class.cv (nb091AlphaDummy044 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091AlphaDummy188 D R p)) (synCcompl
              (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                  (Class.cv (nb091AlphaDummy043 D R p))
                  (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                    (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy184 D R) from
                            (by
                              unfold nb091AlphaDummy184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0182 D R) 1)))) (show
                            (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy186 D R p) from
                            (by
                              unfold nb091AlphaDummy186;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
                          (TAlphaVar.there (show
                              (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy183 D R) from (by
                                unfold nb091AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0182 D R) 0)))) (show
                              (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy185 D R p) from
                              (by
                                unfold nb091AlphaDummy185;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0184 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy189 D R) from
                                (by
                                  unfold nb091AlphaDummy189;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0186 D R)
                                          0)))) (show (nb091AlphaDummy044 D R p) ≠
                                  (nb091AlphaDummy190 D R p) from (by
                                  unfold nb091AlphaDummy190;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0187 D R p)
                                          0)))) (TAlphaVar.there (show
                                  (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy187 D R) from
                                  (by
                                    unfold nb091AlphaDummy187;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0183 D R)
                                            0)))) (show (nb091AlphaDummy044 D R p) ≠
                                    (nb091AlphaDummy188 D R p) from (by
                                    unfold nb091AlphaDummy188;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0185 D R p)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
                              ((Class.cv (nb091AlphaDummy041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
                              ((Class.cv (nb091AlphaDummy043 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy191 D R)
                                    from (by
                                      unfold nb091AlphaDummy191;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0188 D R)
                                              0)))) (show (nb091AlphaDummy186 D R p) ≠
                                      (nb091AlphaDummy193 D R p) from (by
                                      unfold nb091AlphaDummy193;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0189 D R p) 0))))
                                  (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
                                        (nb091AlphaDummy192 D R) from (by
                                        unfold nb091AlphaDummy192;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 1)))) (show
                                      (nb091AlphaDummy186 D R p) ≠
                                        (nb091AlphaDummy194 D R p) from (by
                                        unfold nb091AlphaDummy194;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb091AlphaDummy184 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb091AlphaDummy186 D R p))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy198 D R) from (by
          unfold nb091AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192 D
                    R)
                  1)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy201 D R p) from
        (by
          unfold nb091AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193 D
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy197 D R) from (by
          unfold nb091AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy200 D R p) from
        (by
          unfold nb091AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193
        D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy209 D R) from
        (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠ (nb091AlphaDummy211 D R) from
        (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy211 D R) from (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy184 D R) from
                            (by
                              unfold nb091AlphaDummy184;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0182 D R) 1)))) (show
                            (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy186 D R p) from
                            (by
                              unfold nb091AlphaDummy186;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
                          (TAlphaVar.there (show
                              (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy183 D R) from (by
                                unfold nb091AlphaDummy183;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0182 D R) 0)))) (show
                              (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy185 D R p) from
                              (by
                                unfold nb091AlphaDummy185;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0184 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy189 D R) from
                                (by
                                  unfold nb091AlphaDummy189;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0186 D R)
                                          0)))) (show (nb091AlphaDummy044 D R p) ≠
                                  (nb091AlphaDummy190 D R p) from (by
                                  unfold nb091AlphaDummy190;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0187 D R p)
                                          0)))) (TAlphaVar.there (show
                                  (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy187 D R) from
                                  (by
                                    unfold nb091AlphaDummy187;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0183 D R)
                                            0)))) (show (nb091AlphaDummy044 D R p) ≠
                                    (nb091AlphaDummy188 D R p) from (by
                                    unfold nb091AlphaDummy188;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb091_support_mem_0185 D R p)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
                              ((Class.cv (nb091AlphaDummy041 D R))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
                              ((Class.cv (nb091AlphaDummy043 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091AlphaDummy184 D R) ≠ (nb091AlphaDummy191 D R)
                                    from (by
                                      unfold nb091AlphaDummy191;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0188 D R)
                                              0)))) (show (nb091AlphaDummy186 D R p) ≠
                                      (nb091AlphaDummy193 D R p) from (by
                                      unfold nb091AlphaDummy193;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0189 D R p) 0))))
                                  (TAlphaVar.there (show (nb091AlphaDummy184 D R) ≠
                                        (nb091AlphaDummy192 D R) from (by
                                        unfold nb091AlphaDummy192;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0188 D R) 1)))) (show
                                      (nb091AlphaDummy186 D R p) ≠
                                        (nb091AlphaDummy194 D R p) from (by
                                        unfold nb091AlphaDummy194;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0189 D R p) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb091AlphaDummy184 D R))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb091AlphaDummy186 D R p))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy198 D R) from (by
          unfold nb091AlphaDummy198;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192 D
                    R)
                  1)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy201 D R p) from
        (by
          unfold nb091AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193 D
                    R p)
                  1)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy197 D R) from (by
          unfold nb091AlphaDummy197;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0192
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy200 D R p) from
        (by
          unfold nb091AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0193
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190
                    D R)
                  0)))) (show (nb091AlphaDummy193 D R p) ≠ (nb091AlphaDummy196 D R p) from
        (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy205 D R) from
        (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0196
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0197
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0194
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0195
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy205 D R) from (by
          unfold
            nb091AlphaDummy205;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0200
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy206 D R p) from
        (by
          unfold
            nb091AlphaDummy206;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0201
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy203 D R) from (by
          unfold
            nb091AlphaDummy203;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0198
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy204 D R p) from
        (by
          unfold
            nb091AlphaDummy204;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0199
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy199 D R), (nb091AlphaDummy202 D R p)),
        ((nb091AlphaDummy198 D R), (nb091AlphaDummy201 D R p)),
        ((nb091AlphaDummy197 D R), (nb091AlphaDummy200 D R p)),
        ((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191 D R))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193
        D R p))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠ (nb091AlphaDummy209 D R) from
        (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy198
        D R) ≠ (nb091AlphaDummy209 D R) from (by
          unfold
            nb091AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0204
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy210 D R p) from
        (by
          unfold
            nb091AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0205
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy198 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0202
                    D
                    R)
                  0)))) (show (nb091AlphaDummy201 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0203
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091AlphaDummy191
        D R))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠ (nb091AlphaDummy211 D R) from
        (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091AlphaDummy199
        D R) ≠ (nb091AlphaDummy211 D R) from (by
          unfold
            nb091AlphaDummy211;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0208
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy212 D R p) from
        (by
          unfold
            nb091AlphaDummy212;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0209
                    D
                    R
                    p)
                  0)))) (TAlphaVar.there (show (nb091AlphaDummy199 D R) ≠
        (nb091AlphaDummy207 D R) from (by
          unfold
            nb091AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0206
                    D
                    R)
                  0)))) (show (nb091AlphaDummy202 D R p) ≠ (nb091AlphaDummy208 D R p) from
        (by
          unfold
            nb091AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0207
                    D
                    R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb091AlphaDummy191 D R) ≠
        (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb091AlphaDummy191 D R) ≠ (nb091AlphaDummy195 D R) from (by
          unfold nb091AlphaDummy195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0190 D R) 0)))) (show (nb091AlphaDummy193 D R p) ≠
        (nb091AlphaDummy196 D R p) from (by
          unfold nb091AlphaDummy196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0191 D R p)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb091AlphaDummy195 D R), (nb091AlphaDummy196 D R p)),
        ((nb091AlphaDummy191 D R), (nb091AlphaDummy193 D R p)),
        ((nb091AlphaDummy192 D R), (nb091AlphaDummy194 D R p)),
        ((nb091AlphaDummy184 D R), (nb091AlphaDummy186 D R p)),
        ((nb091AlphaDummy183 D R), (nb091AlphaDummy185 D R p)),
        ((nb091AlphaDummy189 D R), (nb091AlphaDummy190 D R p)),
        ((nb091AlphaDummy187 D R), (nb091AlphaDummy188 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
        (nb091AlphaDummy004 D R p))] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb091SplitAlpha0013 D R p)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb091SplitAlpha0013 D R p)))))))))))

theorem nb091_wpp_notmem_0578 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy042, fv_syn_chwniso] using (nb091_focused_notmem_0052 D R)

theorem nb091_wpp_notmem_0579 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy044, fv_syn_chwniso] using
    (nb091_focused_notmem_0053 D R p)

theorem nb091_wpp_notmem_0580 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy041, fv_syn_chwniso] using (nb091_focused_notmem_0054 D R)

theorem nb091_wpp_notmem_0581 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy043, fv_syn_chwniso] using
    (nb091_focused_notmem_0055 D R p)

theorem nb091_wpp_notmem_0582 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy001, fv_syn_chwniso] using (nb091_focused_notmem_0000 D R)

theorem nb091_wpp_notmem_0583 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy002, fv_syn_chwniso] using
    (nb091_focused_notmem_0001 D R p)

theorem nb091_wpp_notmem_0584 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy000, fv_syn_chwniso] using (nb091_focused_notmem_0002 D R)

theorem nb091_wpp_notmem_0585 (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) :
    p ∉ ((synChwniso D)).fv := by simpa only [fv_syn_chwniso] using dv_D_p

theorem nb091_wpp_notmem_0586 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy003, fv_syn_chwniso] using (nb091_focused_notmem_0003 D R)

theorem nb091_wpp_notmem_0587 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ ((synChwniso D)).fv := by
  simpa only [nb091AlphaDummy004, fv_syn_chwniso] using
    (nb091_focused_notmem_0004 D R p)

theorem nb091_compact_envfresh_0048 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synChwniso D)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091AlphaDummy042 D R) (nb091AlphaDummy044 D R p)
      (nb091_wpp_notmem_0578 D R) (nb091_wpp_notmem_0579 D R p)
      (TEnvFresh.consFresh (nb091AlphaDummy041 D R) (nb091AlphaDummy043 D R p)
        (nb091_wpp_notmem_0580 D R) (nb091_wpp_notmem_0581 D R p)
        (TEnvFresh.consFresh (nb091AlphaDummy001 D R) (nb091AlphaDummy002 D R p)
          (nb091_wpp_notmem_0582 D R) (nb091_wpp_notmem_0583 D R p)
          (TEnvFresh.consFresh (nb091AlphaDummy000 D R) p (nb091_wpp_notmem_0584 D R)
            (nb091_wpp_notmem_0585 D p dv_D_p)
            (TEnvFresh.consFresh (nb091AlphaDummy003 D R) (nb091AlphaDummy004 D R p)
              (nb091_wpp_notmem_0586 D R) (nb091_wpp_notmem_0587 D R p)
              (TEnvFresh.nil ((synChwniso D)).fv))))))

/-- Checked nominal proof certificate identified upstream as `nb091_wpp_refl_0045`. -/
@[expose]
noncomputable def nb091WppRefl0045 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synChwniso D)).fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0048 D R p dv_D_p)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_hnwcutmap`. -/
@[expose]
noncomputable def nominalDfHnwcutmap (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synChnwcutmap R D) (synCmpt p (synCpw1 (synCpw1 D))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb091SplitAlpha0002 D R p) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy001 D R) from (by
                          unfold nb091AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0004 D R) 0))))
                      (show p ≠ (nb091AlphaDummy002 D R p) from (by
                          unfold nb091AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0005 D R p) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                    [((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                      ((nb091AlphaDummy000 D R), p),
                      ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
                    (synCpw1 (synCpw1 D)) (nb091WppRefl0007 D R p dv_D_p)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb091SplitAlpha0008 D R p dv_D_p dv_R_p)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb091SplitAlpha0008 D R p dv_D_p dv_R_p)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb091SplitAlpha0012 D R p dv_D_p dv_R_p))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb091SplitAlpha0014 D R p))))
                          (TAlphaClass.reflOfReflOn
                            [((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
                              ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
                              ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
                              ((nb091AlphaDummy000 D R), p), ((nb091AlphaDummy003 D R),
                                (nb091AlphaDummy004 D R p))]
                            (synChwniso D) (nb091WppRefl0045 D R p dv_D_p))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
