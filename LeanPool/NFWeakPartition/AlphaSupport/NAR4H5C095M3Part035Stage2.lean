/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part035Stage1


/-! NF weak partition development: NAR4H5C095M3Part035. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0259`. -/
@[expose]
noncomputable def nb095WppRefl0259 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCcnv (synCdif S_cls (synCid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0264 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0078`. -/
@[expose]
noncomputable def nb095SplitAlpha0078 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (synWf1 (Class.cv (nb095AlphaDummy000 D R S_cls E)) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))) (Wff.neg
          (synWfo (Class.cv (nb095AlphaDummy000 D R S_cls E)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))))
      (Wff.imp (synWf1 (Class.cv f)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
          (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
        (Wff.neg (synWfo (Class.cv f) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.neg
          (nb095SplitAlpha0029 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_R_f dv_R_u
            dv_R_x dv_f_u dv_f_x dv_u_x)) (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.neg
                (nb095SplitAlpha0034 x u D R S_cls f E dv_E_f dv_E_u dv_E_x dv_S_f
                  dv_S_u dv_S_x dv_f_u dv_f_x)))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
                      ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
                      ((nb095AlphaDummy001 D R S_cls E), u),
                      ((nb095AlphaDummy002 D R S_cls E), x),
                      ((nb095AlphaDummy000 D R S_cls E), f)]
                    (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0036 x u D R S_cls f E))))
                  (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                          (nb095AlphaDummy296 D R S_cls E) from (by
                          unfold nb095AlphaDummy296;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                  1)))) (show f ≠ (nb095AlphaDummy298 f) from (by
                          unfold nb095AlphaDummy298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                            (nb095AlphaDummy295 D R S_cls E) from (by
                            unfold nb095AlphaDummy295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                    0)))) (show f ≠ (nb095AlphaDummy297 f) from (by
                            unfold nb095AlphaDummy297;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0339 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                            (by decide)) dv_f_u (TAlphaVar.there
                            (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                              (by decide)) dv_f_x (TAlphaVar.here _ _ _))))))))))))
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                                (nb095SplitAlpha0056 x u D R S_cls f E dv_f_u dv_f_x))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy383 D R S_cls E),
                              (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
                              (nb095AlphaDummy382 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCid) (nb095WppRefl0188 x u D R S_cls f E)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                                (nb095SplitAlpha0056 x u D R S_cls f E dv_f_u dv_f_x))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy383 D R S_cls E),
                              (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
                              (nb095AlphaDummy382 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCid) (nb095WppRefl0188 x u D R S_cls f E))))))))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                  (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                          (nb095AlphaDummy386 D R S_cls E) ≠
                            (nb095AlphaDummy391 D R S_cls E) from (by
                            unfold nb095AlphaDummy391;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0392 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy392 f) from (by
                            unfold nb095AlphaDummy392;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0393 f) 0)))))
                      (TAlphaVar.there (Ne.symm (show (nb095AlphaDummy385 D R S_cls E) ≠
                              (nb095AlphaDummy391 D R S_cls E) from (by
                              unfold nb095AlphaDummy391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0390 D R S_cls E)
                                      0))))) (Ne.symm
                          (show (nb095AlphaDummy388 f) ≠ (nb095AlphaDummy392 f) from (by
                              unfold nb095AlphaDummy392;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0391 f) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095SplitAlpha0057 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb095SplitAlpha0058 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb095SplitAlpha0058 x u D R S_cls f E)))))))))))))
                (TAlphaWff.ex
                  (TAlphaWff.conj (nb095SplitAlpha0069 x u D R S_cls f E dv_f_u dv_f_x)
                    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095SplitAlpha0070 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy544 D R S_cls E) from (by
          unfold nb095AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
          unfold nb095AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy573 D R S_cls E) from (by
          unfold nb095AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy574 f) from (by
          unfold nb095AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy547 D R S_cls E) from (by
          unfold nb095AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy548 f) from (by
          unfold nb095AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E))))).fv) (by decide)) (freshVar_injective (((synCcnv
        (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy386 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0071 x u D R S_cls f
        E))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy386 D R S_cls E) ≠ (nb095AlphaDummy544 D R S_cls E) from (by
          unfold nb095AlphaDummy544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy546 f) from (by
          unfold nb095AlphaDummy546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy543 D R S_cls E) from (by
          unfold nb095AlphaDummy543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D
                    R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy545 f) from (by
          unfold nb095AlphaDummy545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy573 D R S_cls E) from (by
          unfold nb095AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy574 f) from (by
          unfold nb095AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy386 D R S_cls E) ≠
        (nb095AlphaDummy547 D R S_cls E) from (by
          unfold nb095AlphaDummy547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy389 f) ≠ (nb095AlphaDummy548 f) from (by
          unfold nb095AlphaDummy548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E)))).fv ∪ ((synCcnv (synCcnv (Class.cv
        (nb095AlphaDummy000 D R S_cls E))))).fv) (by decide)) (freshVar_injective (((synCcnv
        (Class.cv f))).fv ∪ ((synCcnv (synCcnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy386 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy390 f))).fv ∪ ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095SplitAlpha0071 x u D R S_cls f
        E)))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy092 D R S_cls E) ≠
        (nb095AlphaDummy095 D R S_cls E) from (by
                                          unfold nb095AlphaDummy095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0082 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy094 f) ≠ (nb095AlphaDummy096 f)
                                        from (by
                                          unfold nb095AlphaDummy096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0083 f) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy095 D R S_cls E) from (by
          unfold nb095AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0080 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy096 f)
        from (by
          unfold nb095AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0081 f) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0072 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
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
                    D R S_cls
                    E)
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
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0073 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129
        D R S_cls E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099
        f)), ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
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
                    D R S_cls
                    E)
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
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy091
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv
        (nb095AlphaDummy094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0073 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy129
        D R S_cls E), (nb095AlphaDummy130 f)), ((nb095AlphaDummy098 D R S_cls E),
        (nb095AlphaDummy100 f)), ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099
        f)), ((nb095AlphaDummy127 D R S_cls E), (nb095AlphaDummy128 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0074 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
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
                    D R S_cls
                    E)
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0075 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
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
                    D R S_cls
                    E)
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0075 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy165 D R S_cls E), (nb095AlphaDummy166 f)),
        ((nb095AlphaDummy134 D R S_cls E), (nb095AlphaDummy136 f)),
        ((nb095AlphaDummy133 D R S_cls E), (nb095AlphaDummy135 f)),
        ((nb095AlphaDummy163 D R S_cls E), (nb095AlphaDummy164 f)),
        ((nb095AlphaDummy137 D R S_cls E), (nb095AlphaDummy138 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
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
                                                  (nb095_support_mem_0170 D R S_cls E)
                                                  0)))) (show f ≠ (nb095AlphaDummy093 f) from
                                        (by
                                          unfold nb095AlphaDummy093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0171 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy095 D R S_cls E) from (by
          unfold nb095AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0168 D R S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy096 f) from (by
          unfold nb095AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy387 D R S_cls E) from (by
          unfold nb095AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R S_cls E)
                  2)))) (show f ≠ (nb095AlphaDummy390 f) from (by
          unfold nb095AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 2)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy386 D R S_cls E) from (by
          unfold nb095AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R S_cls
                    E)
                  1)))) (show f ≠ (nb095AlphaDummy389 f) from (by
          unfold nb095AlphaDummy389;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy385 D R S_cls E) from (by
          unfold nb095AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy388 f) from (by
          unfold nb095AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy391 D R S_cls E) from (by
          unfold nb095AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0555 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095AlphaDummy392 f) from (by
          unfold nb095AlphaDummy392;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0557 f)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) dv_f_u (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x (TAlphaVar.here _ _
        _))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.neg
          (nb095SplitAlpha0029 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_R_f dv_R_u
            dv_R_x dv_f_u dv_f_x dv_u_x)) (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [((nb095AlphaDummy296 D R S_cls E), (nb095AlphaDummy298 f)),
                      ((nb095AlphaDummy295 D R S_cls E), (nb095AlphaDummy297 f)),
                      ((nb095AlphaDummy001 D R S_cls E), u),
                      ((nb095AlphaDummy002 D R S_cls E), x),
                      ((nb095AlphaDummy000 D R S_cls E), f)]
                    (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0036 x u D R S_cls f E))))
                  (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                          (nb095AlphaDummy296 D R S_cls E) from (by
                          unfold nb095AlphaDummy296;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                  1)))) (show f ≠ (nb095AlphaDummy298 f) from (by
                          unfold nb095AlphaDummy298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy000 D R S_cls E) ≠
                            (nb095AlphaDummy295 D R S_cls E) from (by
                            unfold nb095AlphaDummy295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                    0)))) (show f ≠ (nb095AlphaDummy297 f) from (by
                            unfold nb095AlphaDummy297;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0339 f) 0))))
                        (TAlphaVar.there
                          (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                            (by decide)) dv_f_u (TAlphaVar.there
                            (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv)
                              (by decide)) dv_f_x (TAlphaVar.here _ _ _))))))))))
          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                                (nb095AlphaDummy338 u S_cls E)),
                              ((nb095AlphaDummy335 D R S_cls E),
                                (nb095AlphaDummy336 u S_cls E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)] E
                            (nb095FocusedRefl0004 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls
                    E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0076 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0077 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D
        R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0077 x u D R S_cls f E))))))))))))))
                                  (TAlphaClass.reflOfReflOn
                                    [((nb095AlphaDummy340 D R S_cls E),
                                        (nb095AlphaDummy342 u S_cls)),
                                      ((nb095AlphaDummy339 D R S_cls E),
                                        (nb095AlphaDummy341 u S_cls)),
                                      ((nb095AlphaDummy337 D R S_cls E),
                                        (nb095AlphaDummy338 u S_cls E)),
                                      ((nb095AlphaDummy335 D R S_cls E),
                                        (nb095AlphaDummy336 u S_cls E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCcnv (synCdif S_cls (synCid)))
                                    (nb095WppRefl0259 x u D R S_cls f E dv_S_f dv_S_u
                                      dv_S_x)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                                (nb095AlphaDummy338 u S_cls E)),
                              ((nb095AlphaDummy335 D R S_cls E),
                                (nb095AlphaDummy336 u S_cls E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)] E
                            (nb095FocusedRefl0004 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy343 D R S_cls E) from (by
          unfold nb095AlphaDummy343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy344 u) from (by
          unfold nb095AlphaDummy344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls
                    E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy341 u S_cls) from (by
          unfold nb095AlphaDummy341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy337 D R S_cls E) from (by
          unfold nb095AlphaDummy337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy335 D R S_cls E) from (by
          unfold nb095AlphaDummy335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy336 u S_cls E) from (by
          unfold nb095AlphaDummy336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0076 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0077 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D
        R S_cls E) from (by
          unfold
            nb095AlphaDummy346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy348 u S_cls)
        from (by
          unfold
            nb095AlphaDummy348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy345 D R S_cls E) from (by
          unfold
            nb095AlphaDummy345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy347 u S_cls)
        from (by
          unfold
            nb095AlphaDummy347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy375 D R S_cls E) from (by
          unfold
            nb095AlphaDummy375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy376 u S_cls)
        from (by
          unfold
            nb095AlphaDummy376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠
        (nb095AlphaDummy349 D R S_cls E) from (by
          unfold
            nb095AlphaDummy349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy341 u S_cls) ≠ (nb095AlphaDummy350 u S_cls)
        from (by
          unfold
            nb095AlphaDummy350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif S_cls
        (synCid)))).fv ∪ ((synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((synCcnv (synCdif S_cls (synCid)))).fv ∪ ((synCsn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy340
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy342 u S_cls))).fv ∪ ((Class.cv
        (nb095AlphaDummy341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095SplitAlpha0077 x u D R S_cls f E))))))))))))))
                                  (TAlphaClass.reflOfReflOn
                                    [((nb095AlphaDummy340 D R S_cls E),
                                        (nb095AlphaDummy342 u S_cls)),
                                      ((nb095AlphaDummy339 D R S_cls E),
                                        (nb095AlphaDummy341 u S_cls)),
                                      ((nb095AlphaDummy337 D R S_cls E),
                                        (nb095AlphaDummy338 u S_cls E)),
                                      ((nb095AlphaDummy335 D R S_cls E),
                                        (nb095AlphaDummy336 u S_cls E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCcnv (synCdif S_cls (synCid)))
                                    (nb095WppRefl0259 x u D R S_cls f E dv_S_f dv_S_u
                                      dv_S_x))))))))))))))))))

theorem nb095_focused_notmem_0044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn
                            (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
              ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0045 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                      (synCin D (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0265 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy247 D R S_cls E) (nb095AlphaDummy248 x D R)
      (nb095_focused_notmem_0005 D R S_cls E) (nb095_focused_notmem_0006 x D R)
      (TEnvFresh.consFresh (nb095AlphaDummy245 D R S_cls E)
        (nb095AlphaDummy246 x D R) (nb095_focused_notmem_0007 D R S_cls E)
        (nb095_focused_notmem_0008 x D R)
        (TEnvFresh.consFresh (nb095AlphaDummy003 D R S_cls E)
          (nb095AlphaDummy005 x u D R S_cls f E) (nb095_focused_notmem_0044 D R S_cls E)
          (nb095_focused_notmem_0045 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
            (nb095_focused_notmem_0009 D R S_cls E) dv_D_u
            (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
              (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
              (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                (nb095_focused_notmem_0001 D R S_cls E) dv_D_f (TEnvFresh.nil D.fv)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
