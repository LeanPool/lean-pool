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

@[expose]
noncomputable def nb095_wpp_refl_0259 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
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

@[expose]
noncomputable def nb095_split_alpha_0078 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (syn_wf1 (Class.cv (nb095_alpha_dummy_000 D R S_cls E)) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))) (Wff.neg
          (syn_wfo (Class.cv (nb095_alpha_dummy_000 D R S_cls E)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))))
      (Wff.imp (syn_wf1 (Class.cv f)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
        (Wff.neg (syn_wfo (Class.cv f) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.neg
          (nb095_split_alpha_0029 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_R_f dv_R_u
            dv_R_x dv_f_u dv_f_x dv_u_x)) (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.neg
                (nb095_split_alpha_0034 x u D R S_cls f E dv_E_f dv_E_u dv_E_x dv_S_f
                  dv_S_u dv_S_x dv_f_u dv_f_x)))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_closed
                    [((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
                      ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                    (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0036 x u D R S_cls f E))))
                  (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                          (nb095_alpha_dummy_296 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_296;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                  1)))) (show f ≠ (nb095_alpha_dummy_298 f) from (by
                          unfold nb095_alpha_dummy_298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                            (nb095_alpha_dummy_295 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                    0)))) (show f ≠ (nb095_alpha_dummy_297 f) from (by
                            unfold nb095_alpha_dummy_297;
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
                                (nb095_split_alpha_0056 x u D R S_cls f E dv_f_u dv_f_x))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_383 D R S_cls E),
                              (nb095_alpha_dummy_384 f)), ((nb095_alpha_dummy_381 D R S_cls E),
                              (nb095_alpha_dummy_382 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cid) (nb095_wpp_refl_0188 x u D R S_cls f E)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
                                (nb095_split_alpha_0056 x u D R S_cls f E dv_f_u dv_f_x))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_383 D R S_cls E),
                              (nb095_alpha_dummy_384 f)), ((nb095_alpha_dummy_381 D R S_cls E),
                              (nb095_alpha_dummy_382 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cid) (nb095_wpp_refl_0188 x u D R S_cls f E))))))))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                  (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                          (nb095_alpha_dummy_386 D R S_cls E) ≠
                            (nb095_alpha_dummy_391 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_391;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0392 D R S_cls E)
                                    0))))) (Ne.symm
                        (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_392 f) from (by
                            unfold nb095_alpha_dummy_392;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0393 f) 0)))))
                      (TAlphaVar.there (Ne.symm (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                              (nb095_alpha_dummy_391 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_391;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0390 D R S_cls E)
                                      0))))) (Ne.symm
                          (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_392 f) from (by
                              unfold nb095_alpha_dummy_392;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0391 f) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                (nb095_split_alpha_0057 x u D R S_cls f E)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb095_split_alpha_0058 x u D R S_cls f E)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb095_split_alpha_0058 x u D R S_cls f E)))))))))))))
                (TAlphaWff.ex
                  (TAlphaWff.conj (nb095_split_alpha_0069 x u D R S_cls f E dv_f_u dv_f_x)
                    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb095_split_alpha_0070 x u D R S_cls f E)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_544 D R S_cls E) from (by
          unfold nb095_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_546 f) from (by
          unfold nb095_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_573 D R S_cls E) from (by
          unfold nb095_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_574 f) from (by
          unfold nb095_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_547 D R S_cls E) from (by
          unfold nb095_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_548 f) from (by
          unfold nb095_alpha_dummy_548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095_split_alpha_0071 x u D R S_cls f
        E))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_544 D R S_cls E) from (by
          unfold nb095_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_546 f) from (by
          unfold nb095_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_543 D R S_cls E) from (by
          unfold nb095_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0590 D
                    R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_545 f) from (by
          unfold nb095_alpha_dummy_545;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0592 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_573 D R S_cls E) from (by
          unfold nb095_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0594
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_574 f) from (by
          unfold nb095_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0595
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
        (nb095_alpha_dummy_547 D R S_cls E) from (by
          unfold nb095_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0591
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_548 f) from (by
          unfold nb095_alpha_dummy_548;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0593
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_390 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb095_split_alpha_0071 x u D R S_cls f
        E)))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_095 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0082 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_096 f)
                                        from (by
                                          unfold nb095_alpha_dummy_096;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0083 f) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_095 D R S_cls E) from (by
          unfold nb095_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0080 D R S_cls E)
                  0))))) (Ne.symm (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_096 f)
        from (by
          unfold nb095_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0081 f) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0072 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold
            nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold
            nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0073 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129
        D R S_cls E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099
        f)), ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_092 D R S_cls E) ≠ (nb095_alpha_dummy_098 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_100 f) from (by
          unfold
            nb095_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_097 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0112
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_099 f) from (by
          unfold
            nb095_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0114
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_127 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0116
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_128 f) from (by
          unfold
            nb095_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0117
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_092 D R S_cls E) ≠
        (nb095_alpha_dummy_101 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0113
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_094 f) ≠ (nb095_alpha_dummy_102 f) from (by
          unfold
            nb095_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0115
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_091
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_094 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0073 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_129
        D R S_cls E), (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099
        f)), ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0074 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold
            nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold
            nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0075 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_091 D R S_cls E) ≠ (nb095_alpha_dummy_134 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_136 f) from (by
          unfold
            nb095_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_133 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0150
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_135 f) from (by
          unfold
            nb095_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0152
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_163 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0154
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_164 f) from (by
          unfold
            nb095_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0155
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
        (nb095_alpha_dummy_137 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0151
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_138 f) from (by
          unfold
            nb095_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0153
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_000
        D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_091 D R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_094 f))).fv ∪ ((Class.cv (nb095_alpha_dummy_093 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0075 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_165 D R S_cls E), (nb095_alpha_dummy_166 f)),
        ((nb095_alpha_dummy_134 D R S_cls E), (nb095_alpha_dummy_136 f)),
        ((nb095_alpha_dummy_133 D R S_cls E), (nb095_alpha_dummy_135 f)),
        ((nb095_alpha_dummy_163 D R S_cls E), (nb095_alpha_dummy_164 f)),
        ((nb095_alpha_dummy_137 D R S_cls E), (nb095_alpha_dummy_138 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_000 D R S_cls E) ≠
                                        (nb095_alpha_dummy_092 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0170 D R S_cls E) 1))))
                                    (show f ≠ (nb095_alpha_dummy_094 f) from (by
                                        unfold nb095_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0171 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_000 D R S_cls E) ≠
        (nb095_alpha_dummy_091 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_091;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0170 D R S_cls E)
                                                  0)))) (show f ≠ (nb095_alpha_dummy_093 f) from
                                        (by
                                          unfold nb095_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0171 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_095 D R S_cls E) from (by
          unfold nb095_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0168 D R S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_096 f) from (by
          unfold nb095_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0169 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_387 D R S_cls E) from (by
          unfold nb095_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R S_cls E)
                  2)))) (show f ≠ (nb095_alpha_dummy_390 f) from (by
          unfold nb095_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 2)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_386 D R S_cls E) from (by
          unfold nb095_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R S_cls
                    E)
                  1)))) (show f ≠ (nb095_alpha_dummy_389 f) from (by
          unfold nb095_alpha_dummy_389;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_385 D R S_cls E) from (by
          unfold nb095_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0554 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_388 f) from (by
          unfold nb095_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0556 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_391 D R S_cls E) from (by
          unfold nb095_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0555 D R
                    S_cls E)
                  0)))) (show f ≠ (nb095_alpha_dummy_392 f) from (by
          unfold nb095_alpha_dummy_392;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0557 f)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) dv_f_u (TAlphaVar.there (freshVar_injective
        ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) (by decide)) dv_f_x (TAlphaVar.here _ _
        _))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.neg
          (nb095_split_alpha_0029 x u D R S_cls f E dv_D_f dv_D_u dv_D_x dv_R_f dv_R_u
            dv_R_x dv_f_u dv_f_x dv_u_x)) (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_closed
                    [((nb095_alpha_dummy_296 D R S_cls E), (nb095_alpha_dummy_298 f)),
                      ((nb095_alpha_dummy_295 D R S_cls E), (nb095_alpha_dummy_297 f)),
                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                    (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0036 x u D R S_cls f E))))
                  (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                          (nb095_alpha_dummy_296 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_296;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                  1)))) (show f ≠ (nb095_alpha_dummy_298 f) from (by
                          unfold nb095_alpha_dummy_298;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0339 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_000 D R S_cls E) ≠
                            (nb095_alpha_dummy_295 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_295;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0338 D R S_cls E)
                                    0)))) (show f ≠ (nb095_alpha_dummy_297 f) from (by
                            unfold nb095_alpha_dummy_297;
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
                          (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                                (nb095_alpha_dummy_338 u S_cls E)),
                              ((nb095_alpha_dummy_335 D R S_cls E),
                                (nb095_alpha_dummy_336 u S_cls E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                            (nb095_focused_refl_0004 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_343 D R S_cls E) from (by
          unfold nb095_alpha_dummy_343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_344 u) from (by
          unfold nb095_alpha_dummy_344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_340 D R S_cls E) from (by
          unfold nb095_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls
                    E)
                  1)))) (show u ≠ (nb095_alpha_dummy_342 u S_cls) from (by
          unfold nb095_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_339 D R S_cls E) from (by
          unfold nb095_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_341 u S_cls) from (by
          unfold nb095_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_337 D R S_cls E) from (by
          unfold nb095_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_338 u S_cls E) from (by
          unfold nb095_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_335 D R S_cls E) from (by
          unfold nb095_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_336 u S_cls E) from (by
          unfold nb095_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0076 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_375 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_376 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_349 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_350 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif S_cls
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_340
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0077 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D
        R S_cls E) from (by
          unfold
            nb095_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_375 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_376 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_349 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_350 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif S_cls
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_340
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0077 x u D R S_cls f E))))))))))))))
                                  (TAlphaClass.refl_of_reflOn
                                    [((nb095_alpha_dummy_340 D R S_cls E),
                                        (nb095_alpha_dummy_342 u S_cls)),
                                      ((nb095_alpha_dummy_339 D R S_cls E),
                                        (nb095_alpha_dummy_341 u S_cls)),
                                      ((nb095_alpha_dummy_337 D R S_cls E),
                                        (nb095_alpha_dummy_338 u S_cls E)),
                                      ((nb095_alpha_dummy_335 D R S_cls E),
                                        (nb095_alpha_dummy_336 u S_cls E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (nb095_wpp_refl_0259 x u D R S_cls f E dv_S_f dv_S_u
                                      dv_S_x)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                                (nb095_alpha_dummy_338 u S_cls E)),
                              ((nb095_alpha_dummy_335 D R S_cls E),
                                (nb095_alpha_dummy_336 u S_cls E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                            (nb095_focused_refl_0004 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_343 D R S_cls E) from (by
          unfold nb095_alpha_dummy_343;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0350 D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_344 u) from (by
          unfold nb095_alpha_dummy_344;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0351 u) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_340 D R S_cls E) from (by
          unfold nb095_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls
                    E)
                  1)))) (show u ≠ (nb095_alpha_dummy_342 u S_cls) from (by
          unfold nb095_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_339 D R S_cls E) from (by
          unfold nb095_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_341 u S_cls) from (by
          unfold nb095_alpha_dummy_341;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_337 D R S_cls E) from (by
          unfold nb095_alpha_dummy_337;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0346 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_338 u S_cls E) from (by
          unfold nb095_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_335 D R S_cls E) from (by
          unfold nb095_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0344 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_336 u S_cls E) from (by
          unfold nb095_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0345 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0076 x u D R S_cls f E))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_375 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_376 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_349 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_350 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif S_cls
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_340
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0077 x u D R S_cls f E))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D
        R S_cls E) from (by
          unfold
            nb095_alpha_dummy_346;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_348;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_345 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_345;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0380
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_347;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0382
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_375 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0384
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_376 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0385
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠
        (nb095_alpha_dummy_349 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_349;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0381
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_341 u S_cls) ≠ (nb095_alpha_dummy_350 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_350;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0383
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif S_cls
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv u))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_340
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_341 u S_cls))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (nb095_split_alpha_0077 x u D R S_cls f E))))))))))))))
                                  (TAlphaClass.refl_of_reflOn
                                    [((nb095_alpha_dummy_340 D R S_cls E),
                                        (nb095_alpha_dummy_342 u S_cls)),
                                      ((nb095_alpha_dummy_339 D R S_cls E),
                                        (nb095_alpha_dummy_341 u S_cls)),
                                      ((nb095_alpha_dummy_337 D R S_cls E),
                                        (nb095_alpha_dummy_338 u S_cls E)),
                                      ((nb095_alpha_dummy_335 D R S_cls E),
                                        (nb095_alpha_dummy_336 u S_cls E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (nb095_wpp_refl_0259 x u D R S_cls f E dv_S_f dv_S_u
                                      dv_S_x))))))))))))))))))

theorem nb095_focused_notmem_0044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
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
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0045 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
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
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0265 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_247 D R S_cls E) (nb095_alpha_dummy_248 x D R)
      (nb095_focused_notmem_0005 D R S_cls E) (nb095_focused_notmem_0006 x D R)
      (TEnvFresh.consFresh (nb095_alpha_dummy_245 D R S_cls E)
        (nb095_alpha_dummy_246 x D R) (nb095_focused_notmem_0007 D R S_cls E)
        (nb095_focused_notmem_0008 x D R)
        (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
          (nb095_alpha_dummy_005 x u D R S_cls f E) (nb095_focused_notmem_0044 D R S_cls E)
          (nb095_focused_notmem_0045 x u D R S_cls f E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
            (nb095_focused_notmem_0009 D R S_cls E) dv_D_u
            (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
              (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
              (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                (nb095_focused_notmem_0001 D R S_cls E) dv_D_f (TEnvFresh.nil D.fv)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
