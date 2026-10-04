/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part018

/-! NF weak partition development: NAR4H5C095M3Part019. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0029`. -/
@[expose]
noncomputable def nb095SplitAlpha0029 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (synWfun (Class.cv (nb095AlphaDummy000 D R S_cls E))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb095AlphaDummy000 D R S_cls E))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))))
      (Wff.imp (synWfun (Class.cv f)) (Wff.neg (Wff.classEq (synCdm (Class.cv f)) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                              (nb095SplitAlpha0010 x u D R S_cls f E dv_f_u dv_f_x))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                          ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)]
                        (synCid) (nb095WppRefl0035 x u D R S_cls f E)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                              (nb095SplitAlpha0010 x u D R S_cls f E dv_f_u dv_f_x))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb095AlphaDummy009 D R S_cls E), (nb095AlphaDummy010 f)),
                          ((nb095AlphaDummy007 D R S_cls E), (nb095AlphaDummy008 f)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)]
                        (synCid) (nb095WppRefl0035 x u D R S_cls f E))))))))))
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                        (nb095AlphaDummy012 D R S_cls E) ≠
                          (nb095AlphaDummy017 D R S_cls E) from (by
                          unfold nb095AlphaDummy017;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0002 D R S_cls E)
                                  0))))) (Ne.symm
                      (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy018 f) from (by
                          unfold nb095AlphaDummy018;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0003 f) 0)))))
                    (TAlphaVar.there (Ne.symm (show (nb095AlphaDummy011 D R S_cls E) ≠
                            (nb095AlphaDummy017 D R S_cls E) from (by
                            unfold nb095AlphaDummy017;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0000 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095AlphaDummy014 f) ≠ (nb095AlphaDummy018 f) from (by
                            unfold nb095AlphaDummy018;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0001 f) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb095SplitAlpha0011 x u D R S_cls f E)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb095SplitAlpha0012 x u D R S_cls f E)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb095SplitAlpha0012 x u D R S_cls f E)))))))))))))
              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                  (nb095SplitAlpha0013 x u D R S_cls f E)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy056 D R S_cls E) from (by
          unfold nb095AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy058 f) from (by
          unfold nb095AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy055 D R S_cls E) from (by
          unfold nb095AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy057 f) from (by
          unfold nb095AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy085 D R S_cls E) from (by
          unfold nb095AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy086 f) from (by
          unfold nb095AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy059 D R S_cls E) from (by
          unfold nb095AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy060 f) from (by
          unfold nb095AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy011 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0014 x u D R S_cls f E))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy013 D R S_cls E) ≠ (nb095AlphaDummy056 D R S_cls E) from (by
          unfold nb095AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy058 f) from (by
          unfold nb095AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy055 D R S_cls E) from (by
          unfold nb095AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0070 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy057 f) from (by
          unfold nb095AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0072 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy085 D R S_cls E) from (by
          unfold nb095AlphaDummy085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0074 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy086 f) from (by
          unfold nb095AlphaDummy086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0075 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy013 D R S_cls E) ≠
        (nb095AlphaDummy059 D R S_cls E) from (by
          unfold nb095AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0071
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy016 f) ≠ (nb095AlphaDummy060 f) from (by
          unfold nb095AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0073
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy011 D R S_cls
        E))).fv ∪ ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0014 x u D R S_cls f E)))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                                (TAlphaVar.there (Ne.symm (show
                                      (nb095AlphaDummy092 D R S_cls E) ≠
                                        (nb095AlphaDummy095 D R S_cls E) from (by
                                        unfold nb095AlphaDummy095;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0082 D R S_cls E)
                                                0))))) (Ne.symm (show
                                      (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f) from
                                      (by
                                        unfold nb095AlphaDummy096;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0083 f)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy095 D R S_cls E) from (by
                                          unfold nb095AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0080 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f)
                                        from (by
                                          unfold nb095AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0081 f) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0015 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy098 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold
            nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold
            nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold
            nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold
            nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold
            nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold
            nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold
            nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D
        R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0016 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D
        R S_cls E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099
        f)), ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy092 D R S_cls E) ≠ (nb095AlphaDummy098 D R S_cls E) from (by
          unfold
            nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold
            nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold
            nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold
            nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold
            nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold
            nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold
            nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold
            nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D
        R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0016 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129 D
        R S_cls E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099
        f)), ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0017 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy134 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold
            nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold
            nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold
            nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold
            nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold
            nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold
            nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold
            nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0018 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy134 D R S_cls E) from (by
          unfold
            nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold
            nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold
            nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold
            nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold
            nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold
            nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold
            nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold
            nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0018 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy013 D R S_cls E), (nb095AlphaDummy016 f)),
        ((nb095AlphaDummy012 D R S_cls E), (nb095AlphaDummy015 f)),
        ((nb095AlphaDummy011 D R S_cls E), (nb095AlphaDummy014 f)),
        ((nb095AlphaDummy017 D R S_cls E), (nb095AlphaDummy018 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy092 D R S_cls E) from (by
                                      unfold nb095AlphaDummy092;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0170 D R S_cls E) 1))))
                                  (show f ≠ (nb095AlphaDummy094 f) from (by
                                      unfold nb095AlphaDummy094;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0171 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy091 D R S_cls E) from (by
                                        unfold nb095AlphaDummy091;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0170 D R S_cls E) 0))))
                                    (show f ≠ (nb095AlphaDummy093 f) from (by
                                        unfold nb095AlphaDummy093;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy095 D R S_cls E) from (by
                                          unfold nb095AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0168 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy096 f) from
                                        (by
                                          unfold nb095AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0169 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy013 D R S_cls E) from (by
          unfold nb095AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls E)
                  2)))) (show f ≠ (nb095AlphaDummy016 f) from (by
          unfold nb095AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 2)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy012 D R S_cls E) from (by
          unfold nb095AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls E)
                  1)))) (show f ≠ (nb095AlphaDummy015 f) from (by
          unfold nb095AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy011 D R S_cls E) from (by
          unfold nb095AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0164 D R S_cls
                    E)
                  0)))) (show f ≠ (nb095AlphaDummy014 f) from (by
          unfold nb095AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0166 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy017 D R S_cls E) from (by
          unfold nb095AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0165 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy018 f) from (by
          unfold nb095AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0167 f) 0)))) (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x
        (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                  (nb095SplitAlpha0019 x u D R S_cls f E)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy170 D R S_cls E) from (by
          unfold nb095AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy172 f) from (by
          unfold nb095AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy169 D R S_cls E) from (by
          unfold nb095AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy171 f) from (by
          unfold nb095AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy199 D R S_cls E) from (by
          unfold nb095AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy200 f) from (by
          unfold nb095AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy173 D R S_cls E) from (by
          unfold nb095AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy174 f) from (by
          unfold nb095AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv (Class.cv (nb095AlphaDummy000 D
        R S_cls E)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy012 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
        ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0020 x u D R S_cls f E))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy170 D R S_cls E) from (by
          unfold nb095AlphaDummy170;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy172 f) from (by
          unfold nb095AlphaDummy172;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy169 D R S_cls E) from (by
          unfold nb095AlphaDummy169;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0200 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy171 f) from (by
          unfold nb095AlphaDummy171;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0202 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy199 D R S_cls E) from (by
          unfold nb095AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0204 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy200 f) from (by
          unfold nb095AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0205 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy012 D R S_cls E) ≠
        (nb095AlphaDummy173 D R S_cls E) from (by
          unfold nb095AlphaDummy173;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0201
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy015 f) ≠ (nb095AlphaDummy174 f) from (by
          unfold nb095AlphaDummy174;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0203
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCcnv (Class.cv (nb095AlphaDummy000 D
        R S_cls E)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy013 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy012 D R S_cls
        E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
        ((Class.cv (nb095AlphaDummy015 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0020 x u D R S_cls f E)))))))))))))) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                            (nb095AlphaDummy013 D R S_cls E) from (by
                            unfold nb095AlphaDummy013;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E)
                                    2)))) (show f ≠ (nb095AlphaDummy016 f) from (by
                            unfold nb095AlphaDummy016;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0166 f) 2))))
                        (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                              (nb095AlphaDummy012 D R S_cls E) from (by
                              unfold nb095AlphaDummy012;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0164 D R S_cls E)
                                      1)))) (show f ≠ (nb095AlphaDummy015 f) from (by
                              unfold nb095AlphaDummy015;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0166 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                (nb095AlphaDummy011 D R S_cls E) from (by
                                unfold nb095AlphaDummy011;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0164 D R S_cls E) 0))))
                            (show f ≠ (nb095AlphaDummy014 f) from (by
                                unfold nb095AlphaDummy014;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0166 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy017 D R S_cls E) from (by
                                  unfold nb095AlphaDummy017;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0165 D R S_cls E) 0))))
                              (show f ≠ (nb095AlphaDummy018 f) from (by
                                  unfold nb095AlphaDummy018;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0167 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u
                                (TAlphaVar.there (freshVar_injective
                                    ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
                                  dv_f_x (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb095AlphaDummy206 D R S_cls E), (nb095AlphaDummy208 f)),
                    ((nb095AlphaDummy205 D R S_cls E), (nb095AlphaDummy207 f)),
                    ((nb095AlphaDummy001 D R S_cls E), u),
                    ((nb095AlphaDummy002 D R S_cls E), x),
                    ((nb095AlphaDummy000 D R S_cls E), f)]
                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0022 x u D R S_cls f E))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                  (nb095AlphaDummy092 D R S_cls E) ≠
                                    (nb095AlphaDummy095 D R S_cls E) from (by
                                    unfold nb095AlphaDummy095;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0082 D R S_cls E) 0))))) (Ne.symm
                                (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f) from
                                  (by
                                    unfold nb095AlphaDummy096;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0083 f)
                                            0))))) (TAlphaVar.there (Ne.symm (show
                                    (nb095AlphaDummy091 D R S_cls E) ≠
                                      (nb095AlphaDummy095 D R S_cls E) from (by
                                      unfold nb095AlphaDummy095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0080 D R S_cls E) 0)))))
                                (Ne.symm (show
                                    (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f) from
                                    (by
                                      unfold nb095AlphaDummy096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0081 f)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.neg
                                        (nb095SplitAlpha0023 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold
            nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold
            nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold
            nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold
            nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R
        S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0024 x u D R S_cls f E)))))))))
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy098 D R S_cls E) from (by
          unfold nb095AlphaDummy098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy100 f) from (by
          unfold nb095AlphaDummy100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy097 D R S_cls E) from (by
          unfold nb095AlphaDummy097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy099 f) from (by
          unfold nb095AlphaDummy099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy127 D R S_cls E) from (by
          unfold
            nb095AlphaDummy127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy128 f) from (by
          unfold
            nb095AlphaDummy128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy101 D R S_cls E) from (by
          unfold
            nb095AlphaDummy101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy102 f) from (by
          unfold
            nb095AlphaDummy102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R
        S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0024 x u D R S_cls f E)))))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                        (nb095SplitAlpha0025 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold
            nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold
            nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold
            nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold
            nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0026 x u D R S_cls f E))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy134 D R S_cls E) from (by
          unfold nb095AlphaDummy134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy136 f) from (by
          unfold nb095AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy133 D R S_cls E) from (by
          unfold nb095AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy135 f) from (by
          unfold nb095AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy163 D R S_cls E) from (by
          unfold
            nb095AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy164 f) from (by
          unfold
            nb095AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
        (nb095AlphaDummy137 D R S_cls E) from (by
          unfold
            nb095AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy138 f) from (by
          unfold
            nb095AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0026 x u D R S_cls f E)))))))))))))))) (TAlphaClass.cv
                            (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                  (nb095AlphaDummy092 D R S_cls E) from (by
                                  unfold nb095AlphaDummy092;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0170 D R S_cls E) 1))))
                              (show f ≠ (nb095AlphaDummy094 f) from (by
                                  unfold nb095AlphaDummy094;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0171 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                                    (nb095AlphaDummy091 D R S_cls E) from (by
                                    unfold nb095AlphaDummy091;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0170 D R S_cls E) 0))))
                                (show f ≠ (nb095AlphaDummy093 f) from (by
                                    unfold nb095AlphaDummy093;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0171 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy000 D R S_cls E) ≠
                                      (nb095AlphaDummy095 D R S_cls E) from (by
                                      unfold nb095AlphaDummy095;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0168 D R S_cls E) 0))))
                                  (show f ≠ (nb095AlphaDummy096 f) from (by
                                      unfold nb095AlphaDummy096;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0169 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy000 D R S_cls E) ≠
                                        (nb095AlphaDummy206 D R S_cls E) from (by
                                        unfold nb095AlphaDummy206;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0248 D R S_cls E) 1))))
                                    (show f ≠ (nb095AlphaDummy208 f) from (by
                                        unfold nb095AlphaDummy208;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0249 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy000 D R S_cls E) ≠
        (nb095AlphaDummy205 D R S_cls E) from (by
                                          unfold nb095AlphaDummy205;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0248 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy207 f) from
                                        (by
                                          unfold nb095AlphaDummy207;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0249 f) 0))))
                                      (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_u (TAlphaVar.there
        (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide))
        dv_f_x (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                              (nb095AlphaDummy248 x D R)),
                            ((nb095AlphaDummy245 D R S_cls E),
                              (nb095AlphaDummy246 x D R)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] D
                          (nb095FocusedRefl0002 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy253 D R S_cls E) from (by
          unfold nb095AlphaDummy253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy254 x) from (by
          unfold nb095AlphaDummy254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0027 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0028 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0028 x u D R S_cls f E)))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif R (synCid)))
                                  (nb095WppRefl0100 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                              (nb095AlphaDummy248 x D R)),
                            ((nb095AlphaDummy245 D R S_cls E),
                              (nb095AlphaDummy246 x D R)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] D
                          (nb095FocusedRefl0002 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy253 D R S_cls E) from (by
          unfold nb095AlphaDummy253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy254 x) from (by
          unfold nb095AlphaDummy254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy250 D R S_cls E) from (by
          unfold nb095AlphaDummy250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy252 x R) from (by
          unfold nb095AlphaDummy252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy249 D R S_cls E) from (by
          unfold nb095AlphaDummy249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095AlphaDummy251 x R) from (by
          unfold nb095AlphaDummy251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy002 D R S_cls E) ≠ (nb095AlphaDummy247 D R S_cls E) from (by
          unfold nb095AlphaDummy247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy248 x D R) from (by
          unfold nb095AlphaDummy248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy245 D R S_cls E) from (by
          unfold nb095AlphaDummy245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy246 x D R) from (by
          unfold nb095AlphaDummy246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _)))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0027 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0028 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy258 x R) from (by
          unfold
            nb095AlphaDummy258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy255 D R S_cls E) from (by
          unfold
            nb095AlphaDummy255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy257 x R) from (by
          unfold
            nb095AlphaDummy257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy285 D R S_cls E) from (by
          unfold
            nb095AlphaDummy285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy286 x R) from (by
          unfold
            nb095AlphaDummy286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy249 D R S_cls E) ≠
        (nb095AlphaDummy259 D R S_cls E) from (by
          unfold
            nb095AlphaDummy259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy251 x R) ≠ (nb095AlphaDummy260 x R) from (by
          unfold
            nb095AlphaDummy260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy250
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪ ((Class.cv
        (nb095AlphaDummy251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb095SplitAlpha0028 x u D R S_cls f E)))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif R (synCid)))
                                  (nb095WppRefl0100 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))))))))

theorem nb095_compact_fv_empty_0222 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy293 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0223 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy294 u S_cls f E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0224 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy291 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0225 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy292 u S_cls f E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
