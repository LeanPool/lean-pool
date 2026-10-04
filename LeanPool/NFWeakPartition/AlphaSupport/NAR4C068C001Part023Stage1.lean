/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block006

/-! NF weak partition development: NAR4C068C001Part023. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0031`. -/
@[expose]
noncomputable def nb068SplitAlpha0031 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
        ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
        ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy233))
          (Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy233))
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy234 f))
          (Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy234 f))
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from
                    (by
                      unfold nb068AlphaDummy204;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                  (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
                      unfold nb068AlphaDummy206;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from
                      (by
                        unfold nb068AlphaDummy203;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
                        unfold nb068AlphaDummy205;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy233) from (by
                          unfold nb068AlphaDummy233;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy234 f) from (by
                          unfold nb068AlphaDummy234;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy207) from (by
                            unfold nb068AlphaDummy207;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy208 f) from (by
                            unfold nb068AlphaDummy208;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb068AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb068AlphaDummy047))).fv ∪
                      ((Class.cv (nb068AlphaDummy046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0030 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0030 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                          ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                          ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                          ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                          ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                          ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                          ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                          ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                          ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                          ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                          ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from
                      (by
                        unfold nb068AlphaDummy204;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
                    (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
                        unfold nb068AlphaDummy206;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0244 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from (by
                          unfold nb068AlphaDummy203;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0242) 0))))
                      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
                          unfold nb068AlphaDummy205;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy233) from (by
                            unfold nb068AlphaDummy233;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0246) 0))))
                        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy234 f) from (by
                            unfold nb068AlphaDummy234;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0247 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy207) from (by
                              unfold nb068AlphaDummy207;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0243) 0))))
                          (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy208 f) from (by
                              unfold nb068AlphaDummy208;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0245 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb068AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy047))).fv ∪
                        ((Class.cv (nb068AlphaDummy046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0030 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0030 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy235), (nb068AlphaDummy236 f)),
                            ((nb068AlphaDummy204), (nb068AlphaDummy206 f)),
                            ((nb068AlphaDummy203), (nb068AlphaDummy205 f)),
                            ((nb068AlphaDummy233), (nb068AlphaDummy234 f)),
                            ((nb068AlphaDummy207), (nb068AlphaDummy208 f)),
                            ((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
                            ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
                            ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
                            ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
                            ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
                            ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0032`. -/
@[expose]
noncomputable def nb068SplitAlpha0032 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy047), (nb068AlphaDummy050 f)),
        ((nb068AlphaDummy046), (nb068AlphaDummy049 f)),
        ((nb068AlphaDummy045), (nb068AlphaDummy048 f)),
        ((nb068AlphaDummy051), (nb068AlphaDummy052 f)),
        ((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy045))
          (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy047)))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy047)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy046)))))
      (Wff.imp (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
          (Class.cv (nb068AlphaDummy050 f))) (Wff.neg
          (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy049 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from
                                    (by
                                      unfold nb068AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from
                                    (by
                                      unfold nb068AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
                                        unfold nb068AlphaDummy089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068AlphaDummy048 f) ≠
                                        (nb068AlphaDummy091 f) from (by
                                        unfold nb068AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy045) ≠ (nb068AlphaDummy095) from
                                        (by
                                          unfold nb068AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy096 f) from (by
                                          unfold nb068AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy045) ≠
        (nb068AlphaDummy093) from (by
          unfold nb068AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy094 f) from (by
          unfold nb068AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
                                      ((Class.cv (nb068AlphaDummy047))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy050 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0011 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from
                                    (by
                                      unfold nb068AlphaDummy090;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0084)
                                              1)))) (show
                                    (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from
                                    (by
                                      unfold nb068AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0086 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
                                        unfold nb068AlphaDummy089;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0084)
                                                0)))) (show (nb068AlphaDummy048 f) ≠
                                        (nb068AlphaDummy091 f) from (by
                                        unfold nb068AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0086 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy045) ≠ (nb068AlphaDummy095) from
                                        (by
                                          unfold nb068AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0088)
                                                  0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy096 f) from (by
                                          unfold nb068AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0089 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy045) ≠
        (nb068AlphaDummy093) from (by
          unfold nb068AlphaDummy093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0085) 0)))) (show (nb068AlphaDummy048 f) ≠
        (nb068AlphaDummy094 f) from (by
          unfold nb068AlphaDummy094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0087 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy045))).fv ∪
                                      ((Class.cv (nb068AlphaDummy047))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy048 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy050 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0011 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0014 x y f))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0026 x y f)))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
                                        unfold nb068AlphaDummy204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068AlphaDummy050 f) ≠
                                        (nb068AlphaDummy206 f) from (by
                                        unfold nb068AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from
                                        (by
                                          unfold nb068AlphaDummy203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy205 f) from (by
                                          unfold nb068AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy047) ≠
        (nb068AlphaDummy209) from (by
          unfold nb068AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy210 f) from (by
          unfold nb068AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy047) ≠ (nb068AlphaDummy207) from (by
          unfold nb068AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy208 f) from (by
          unfold nb068AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy047))).fv ∪
                                        ((Class.cv (nb068AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0028 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
                                        unfold nb068AlphaDummy204;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0214)
                                                1)))) (show (nb068AlphaDummy050 f) ≠
                                        (nb068AlphaDummy206 f) from (by
                                        unfold nb068AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0216 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from
                                        (by
                                          unfold nb068AlphaDummy203;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0214)
                                                  0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy205 f) from (by
                                          unfold nb068AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0216 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy047) ≠
        (nb068AlphaDummy209) from (by
          unfold nb068AlphaDummy209;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0218) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy210 f) from (by
          unfold nb068AlphaDummy210;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0219 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy047) ≠ (nb068AlphaDummy207) from (by
          unfold nb068AlphaDummy207;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0215) 0)))) (show (nb068AlphaDummy050 f) ≠
        (nb068AlphaDummy208 f) from (by
          unfold nb068AlphaDummy208;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0217 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy047))).fv ∪
                                        ((Class.cv (nb068AlphaDummy046))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy050 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy049 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0028 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0031 x y f))))))))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy047) from (by
                unfold nb068AlphaDummy047;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
            (show f ≠ (nb068AlphaDummy050 f) from (by
                unfold nb068AlphaDummy050;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy046) from (by
                  unfold nb068AlphaDummy046;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 1))))
              (show f ≠ (nb068AlphaDummy049 f) from (by
                  unfold nb068AlphaDummy049;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 1))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy045) from (by
                    unfold nb068AlphaDummy045;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 0))))
                (show f ≠ (nb068AlphaDummy048 f) from (by
                    unfold nb068AlphaDummy048;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy051) from
                    (by
                      unfold nb068AlphaDummy051;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0207) 0))))
                  (show f ≠ (nb068AlphaDummy052 f) from (by
                      unfold nb068AlphaDummy052;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0209 f) 0))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy043) from
                      (by
                        unfold nb068AlphaDummy043;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0204) 0))))
                    (show f ≠ (nb068AlphaDummy044 f) from (by
                        unfold nb068AlphaDummy044;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0205 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy041) from (by
                          unfold nb068AlphaDummy041;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0202) 0))))
                      (show f ≠ (nb068AlphaDummy042 f) from (by
                          unfold nb068AlphaDummy042;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0203 f) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

theorem nb068_wpp_notmem_0596 : (nb068AlphaDummy043) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy043, fv_syn_cid] using (nb068_compact_fv_empty_0058)

theorem nb068_wpp_notmem_0597 (f : Var) : (nb068AlphaDummy044 f) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy044, fv_syn_cid] using (nb068_compact_fv_empty_0059 f)

theorem nb068_wpp_notmem_0598 : (nb068AlphaDummy041) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy041, fv_syn_cid] using (nb068_compact_fv_empty_0060)

theorem nb068_wpp_notmem_0599 (f : Var) : (nb068AlphaDummy042 f) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy042, fv_syn_cid] using (nb068_compact_fv_empty_0061 f)

theorem nb068_wpp_notmem_0600 : (nb068AlphaDummy000) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy000, fv_syn_cid] using (nb068_compact_fv_empty_0062)

theorem nb068_wpp_notmem_0601 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0063 f)

theorem nb068_wpp_notmem_0602 : (nb068AlphaDummy002) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy002, fv_syn_cid] using (nb068_compact_fv_empty_0020)

theorem nb068_wpp_notmem_0603 (y : Var) : y ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0021 y)

theorem nb068_wpp_notmem_0604 : (nb068AlphaDummy001) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy001, fv_syn_cid] using (nb068_compact_fv_empty_0022)

theorem nb068_wpp_notmem_0605 (x : Var) : x ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb068_compact_fv_empty_0023 x)

theorem nb068_wpp_notmem_0606 : (nb068AlphaDummy003) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy003, fv_syn_cid] using (nb068_compact_fv_empty_0024)

theorem nb068_wpp_notmem_0607 (x : Var) (y : Var) (f : Var) :
    (nb068AlphaDummy004 x y f) ∉ ((synCid)).fv := by
  simpa only [nb068AlphaDummy004, fv_syn_cid] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0042 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb068AlphaDummy043), (nb068AlphaDummy044 f)),
        ((nb068AlphaDummy041), (nb068AlphaDummy042 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb068AlphaDummy043) (nb068AlphaDummy044 f)
      (nb068_wpp_notmem_0596) (nb068_wpp_notmem_0597 f)
      (TEnvFresh.consFresh (nb068AlphaDummy041) (nb068AlphaDummy042 f)
        (nb068_wpp_notmem_0598) (nb068_wpp_notmem_0599 f)
        (TEnvFresh.consFresh (nb068AlphaDummy000) f (nb068_wpp_notmem_0600)
          (nb068_wpp_notmem_0601 f)
          (TEnvFresh.consFresh (nb068AlphaDummy002) y (nb068_wpp_notmem_0602)
            (nb068_wpp_notmem_0603 y)
            (TEnvFresh.consFresh (nb068AlphaDummy001) x (nb068_wpp_notmem_0604)
              (nb068_wpp_notmem_0605 x)
              (TEnvFresh.consFresh (nb068AlphaDummy003) (nb068AlphaDummy004 x y f)
                (nb068_wpp_notmem_0606) (nb068_wpp_notmem_0607 x y f)
                (TEnvFresh.nil ((synCid)).fv)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
