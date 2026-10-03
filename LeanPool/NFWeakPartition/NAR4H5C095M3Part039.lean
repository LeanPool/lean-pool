/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part039Stage1


/-! NF weak partition development: NAR4H5C095M3Part039. -/


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
noncomputable def nb095_wpp_refl_0297 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0306 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)

@[expose]
noncomputable def nb095_split_alpha_0089 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
        (Wff.neg (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
            (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv) (by decide))
          (freshVar_injective (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv x))))).fv ∪ ((syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                            (nb095_alpha_dummy_248 x D R)),
                          ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
                          ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
                          ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
                          ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
                          ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
                          ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                        (nb095_focused_refl_0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_253 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from
                                        (by
                                          unfold nb095_alpha_dummy_254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_620 D R S_cls E) from (by
          unfold nb095_alpha_dummy_620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_622 x D R) from (by
          unfold nb095_alpha_dummy_622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_619 D R S_cls E) from (by
          unfold nb095_alpha_dummy_619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_621 x D R) from (by
          unfold nb095_alpha_dummy_621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_617 D R S_cls E) from (by
          unfold nb095_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_618 x D R) from (by
          unfold nb095_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_615 D R S_cls E) from (by
          unfold nb095_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_616 x D R) from (by
          unfold nb095_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0087 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_250 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x
        R))).fv ∪ ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_250 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x
        R))).fv ∪ ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
                                  ((nb095_alpha_dummy_620 D R S_cls E),
                                    (nb095_alpha_dummy_622 x D R)),
                                  ((nb095_alpha_dummy_619 D R S_cls E),
                                    (nb095_alpha_dummy_621 x D R)),
                                  ((nb095_alpha_dummy_623 D R S_cls E),
                                    (nb095_alpha_dummy_624 x D R)),
                                  ((nb095_alpha_dummy_617 D R S_cls E),
                                    (nb095_alpha_dummy_618 x D R)),
                                  ((nb095_alpha_dummy_615 D R S_cls E),
                                    (nb095_alpha_dummy_616 x D R)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_ccnv (syn_cdif R (syn_cid)))
                                (nb095_wpp_refl_0297 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                            (nb095_alpha_dummy_248 x D R)),
                          ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
                          ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
                          ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
                          ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
                          ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
                          ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                        (nb095_focused_refl_0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_253 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from
                                        (by
                                          unfold nb095_alpha_dummy_254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_620 D R S_cls E) from (by
          unfold nb095_alpha_dummy_620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_622 x D R) from (by
          unfold nb095_alpha_dummy_622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_619 D R S_cls E) from (by
          unfold nb095_alpha_dummy_619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_621 x D R) from (by
          unfold nb095_alpha_dummy_621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_617 D R S_cls E) from (by
          unfold nb095_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_618 x D R) from (by
          unfold nb095_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_615 D R S_cls E) from (by
          unfold nb095_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_616 x D R) from (by
          unfold nb095_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0087 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_250 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x
        R))).fv ∪ ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_250 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x
        R))).fv ∪ ((Class.cv (nb095_alpha_dummy_251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_287 D R S_cls E), (nb095_alpha_dummy_288 x R)),
        ((nb095_alpha_dummy_256 D R S_cls E), (nb095_alpha_dummy_258 x R)),
        ((nb095_alpha_dummy_255 D R S_cls E), (nb095_alpha_dummy_257 x R)),
        ((nb095_alpha_dummy_285 D R S_cls E), (nb095_alpha_dummy_286 x R)),
        ((nb095_alpha_dummy_259 D R S_cls E), (nb095_alpha_dummy_260 x R)),
        ((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb095_alpha_dummy_250 D R S_cls E),
                                    (nb095_alpha_dummy_252 x R)),
                                  ((nb095_alpha_dummy_249 D R S_cls E),
                                    (nb095_alpha_dummy_251 x R)),
                                  ((nb095_alpha_dummy_247 D R S_cls E),
                                    (nb095_alpha_dummy_248 x D R)),
                                  ((nb095_alpha_dummy_245 D R S_cls E),
                                    (nb095_alpha_dummy_246 x D R)),
                                  ((nb095_alpha_dummy_620 D R S_cls E),
                                    (nb095_alpha_dummy_622 x D R)),
                                  ((nb095_alpha_dummy_619 D R S_cls E),
                                    (nb095_alpha_dummy_621 x D R)),
                                  ((nb095_alpha_dummy_623 D R S_cls E),
                                    (nb095_alpha_dummy_624 x D R)),
                                  ((nb095_alpha_dummy_617 D R S_cls E),
                                    (nb095_alpha_dummy_618 x D R)),
                                  ((nb095_alpha_dummy_615 D R S_cls E),
                                    (nb095_alpha_dummy_616 x D R)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_ccnv (syn_cdif R (syn_cid)))
                                (nb095_wpp_refl_0297 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                              (nb095_alpha_dummy_248 x D R)),
                            ((nb095_alpha_dummy_245 D R S_cls E),
                              (nb095_alpha_dummy_246 x D R)),
                            ((nb095_alpha_dummy_620 D R S_cls E),
                              (nb095_alpha_dummy_622 x D R)),
                            ((nb095_alpha_dummy_619 D R S_cls E),
                              (nb095_alpha_dummy_621 x D R)),
                            ((nb095_alpha_dummy_623 D R S_cls E),
                              (nb095_alpha_dummy_624 x D R)),
                            ((nb095_alpha_dummy_617 D R S_cls E),
                              (nb095_alpha_dummy_618 x D R)),
                            ((nb095_alpha_dummy_615 D R S_cls E),
                              (nb095_alpha_dummy_616 x D R)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                          (nb095_focused_refl_0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_253 D R S_cls E) from (by
          unfold nb095_alpha_dummy_253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from (by
          unfold nb095_alpha_dummy_254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_620 D R S_cls E) from (by
          unfold nb095_alpha_dummy_620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_622 x D R) from (by
          unfold nb095_alpha_dummy_622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_619 D R S_cls E) from (by
          unfold nb095_alpha_dummy_619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_621 x D R) from (by
          unfold nb095_alpha_dummy_621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_617 D R S_cls E) from (by
          unfold nb095_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_618 x D R) from (by
          unfold nb095_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_615 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_616 x D R) from (by
          unfold
            nb095_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0087 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_287
        D R S_cls E), (nb095_alpha_dummy_288 x R)), ((nb095_alpha_dummy_256 D R S_cls E),
        (nb095_alpha_dummy_258 x R)), ((nb095_alpha_dummy_255 D R S_cls E),
        (nb095_alpha_dummy_257 x R)), ((nb095_alpha_dummy_285 D R S_cls E),
        (nb095_alpha_dummy_286 x R)), ((nb095_alpha_dummy_259 D R S_cls E),
        (nb095_alpha_dummy_260 x R)), ((nb095_alpha_dummy_250 D R S_cls E),
        (nb095_alpha_dummy_252 x R)), ((nb095_alpha_dummy_249 D R S_cls E),
        (nb095_alpha_dummy_251 x R)), ((nb095_alpha_dummy_247 D R S_cls E),
        (nb095_alpha_dummy_248 x D R)), ((nb095_alpha_dummy_245 D R S_cls E),
        (nb095_alpha_dummy_246 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_287
        D R S_cls E), (nb095_alpha_dummy_288 x R)), ((nb095_alpha_dummy_256 D R S_cls E),
        (nb095_alpha_dummy_258 x R)), ((nb095_alpha_dummy_255 D R S_cls E),
        (nb095_alpha_dummy_257 x R)), ((nb095_alpha_dummy_285 D R S_cls E),
        (nb095_alpha_dummy_286 x R)), ((nb095_alpha_dummy_259 D R S_cls E),
        (nb095_alpha_dummy_260 x R)), ((nb095_alpha_dummy_250 D R S_cls E),
        (nb095_alpha_dummy_252 x R)), ((nb095_alpha_dummy_249 D R S_cls E),
        (nb095_alpha_dummy_251 x R)), ((nb095_alpha_dummy_247 D R S_cls E),
        (nb095_alpha_dummy_248 x D R)), ((nb095_alpha_dummy_245 D R S_cls E),
        (nb095_alpha_dummy_246 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_250 D R S_cls E),
                                      (nb095_alpha_dummy_252 x R)),
                                    ((nb095_alpha_dummy_249 D R S_cls E),
                                      (nb095_alpha_dummy_251 x R)),
                                    ((nb095_alpha_dummy_247 D R S_cls E),
                                      (nb095_alpha_dummy_248 x D R)),
                                    ((nb095_alpha_dummy_245 D R S_cls E),
                                      (nb095_alpha_dummy_246 x D R)),
                                    ((nb095_alpha_dummy_620 D R S_cls E),
                                      (nb095_alpha_dummy_622 x D R)),
                                    ((nb095_alpha_dummy_619 D R S_cls E),
                                      (nb095_alpha_dummy_621 x D R)),
                                    ((nb095_alpha_dummy_623 D R S_cls E),
                                      (nb095_alpha_dummy_624 x D R)),
                                    ((nb095_alpha_dummy_617 D R S_cls E),
                                      (nb095_alpha_dummy_618 x D R)),
                                    ((nb095_alpha_dummy_615 D R S_cls E),
                                      (nb095_alpha_dummy_616 x D R)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif R (syn_cid)))
                                  (nb095_wpp_refl_0297 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_247 D R S_cls E),
                              (nb095_alpha_dummy_248 x D R)),
                            ((nb095_alpha_dummy_245 D R S_cls E),
                              (nb095_alpha_dummy_246 x D R)),
                            ((nb095_alpha_dummy_620 D R S_cls E),
                              (nb095_alpha_dummy_622 x D R)),
                            ((nb095_alpha_dummy_619 D R S_cls E),
                              (nb095_alpha_dummy_621 x D R)),
                            ((nb095_alpha_dummy_623 D R S_cls E),
                              (nb095_alpha_dummy_624 x D R)),
                            ((nb095_alpha_dummy_617 D R S_cls E),
                              (nb095_alpha_dummy_618 x D R)),
                            ((nb095_alpha_dummy_615 D R S_cls E),
                              (nb095_alpha_dummy_616 x D R)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] D
                          (nb095_focused_refl_0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_253 D R S_cls E) from (by
          unfold nb095_alpha_dummy_253;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0256 D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_254 x) from (by
          unfold nb095_alpha_dummy_254;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0257 x) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_250 D R S_cls E) from (by
          unfold nb095_alpha_dummy_250;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_252 x R) from (by
          unfold nb095_alpha_dummy_252;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_249 D R S_cls E) from (by
          unfold nb095_alpha_dummy_249;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0254 D R S_cls
                    E)
                  0)))) (show x ≠ (nb095_alpha_dummy_251 x R) from (by
          unfold nb095_alpha_dummy_251;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0255 x R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_002 D R S_cls E) ≠ (nb095_alpha_dummy_247 D R S_cls E) from (by
          unfold nb095_alpha_dummy_247;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0252 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_248 x D R) from (by
          unfold nb095_alpha_dummy_248;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0253 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_245 D R S_cls E) from (by
          unfold nb095_alpha_dummy_245;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0250 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_246 x D R) from (by
          unfold nb095_alpha_dummy_246;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0251 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_620 D R S_cls E) from (by
          unfold nb095_alpha_dummy_620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_622 x D R) from (by
          unfold nb095_alpha_dummy_622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_619 D R S_cls E) from (by
          unfold nb095_alpha_dummy_619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_621 x D R) from (by
          unfold nb095_alpha_dummy_621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_617 D R S_cls E) from (by
          unfold nb095_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_618 x D R) from (by
          unfold nb095_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_615 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_616 x D R) from (by
          unfold
            nb095_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_002 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪
        (E).fv) (by decide)) (Ne.symm dv_u_x) (TAlphaVar.here _ _ _))))))))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0087 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_287
        D R S_cls E), (nb095_alpha_dummy_288 x R)), ((nb095_alpha_dummy_256 D R S_cls E),
        (nb095_alpha_dummy_258 x R)), ((nb095_alpha_dummy_255 D R S_cls E),
        (nb095_alpha_dummy_257 x R)), ((nb095_alpha_dummy_285 D R S_cls E),
        (nb095_alpha_dummy_286 x R)), ((nb095_alpha_dummy_259 D R S_cls E),
        (nb095_alpha_dummy_260 x R)), ((nb095_alpha_dummy_250 D R S_cls E),
        (nb095_alpha_dummy_252 x R)), ((nb095_alpha_dummy_249 D R S_cls E),
        (nb095_alpha_dummy_251 x R)), ((nb095_alpha_dummy_247 D R S_cls E),
        (nb095_alpha_dummy_248 x D R)), ((nb095_alpha_dummy_245 D R S_cls E),
        (nb095_alpha_dummy_246 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_249 D R S_cls E) ≠ (nb095_alpha_dummy_256 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_256;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_258 x R) from (by
          unfold
            nb095_alpha_dummy_258;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_255 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_255;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0286
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_257 x R) from (by
          unfold
            nb095_alpha_dummy_257;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0288
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_285 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0290
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_286 x R) from (by
          unfold
            nb095_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0291
                    x R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_249 D R S_cls E) ≠
        (nb095_alpha_dummy_259 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_259;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0287
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_251 x R) ≠ (nb095_alpha_dummy_260 x R) from (by
          unfold
            nb095_alpha_dummy_260;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0289
                    x R)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))).fv)
        (by decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (Class.cv x))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_250
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_249 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_252 x R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_251 x R))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_287
        D R S_cls E), (nb095_alpha_dummy_288 x R)), ((nb095_alpha_dummy_256 D R S_cls E),
        (nb095_alpha_dummy_258 x R)), ((nb095_alpha_dummy_255 D R S_cls E),
        (nb095_alpha_dummy_257 x R)), ((nb095_alpha_dummy_285 D R S_cls E),
        (nb095_alpha_dummy_286 x R)), ((nb095_alpha_dummy_259 D R S_cls E),
        (nb095_alpha_dummy_260 x R)), ((nb095_alpha_dummy_250 D R S_cls E),
        (nb095_alpha_dummy_252 x R)), ((nb095_alpha_dummy_249 D R S_cls E),
        (nb095_alpha_dummy_251 x R)), ((nb095_alpha_dummy_247 D R S_cls E),
        (nb095_alpha_dummy_248 x D R)), ((nb095_alpha_dummy_245 D R S_cls E),
        (nb095_alpha_dummy_246 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_250 D R S_cls E),
                                      (nb095_alpha_dummy_252 x R)),
                                    ((nb095_alpha_dummy_249 D R S_cls E),
                                      (nb095_alpha_dummy_251 x R)),
                                    ((nb095_alpha_dummy_247 D R S_cls E),
                                      (nb095_alpha_dummy_248 x D R)),
                                    ((nb095_alpha_dummy_245 D R S_cls E),
                                      (nb095_alpha_dummy_246 x D R)),
                                    ((nb095_alpha_dummy_620 D R S_cls E),
                                      (nb095_alpha_dummy_622 x D R)),
                                    ((nb095_alpha_dummy_619 D R S_cls E),
                                      (nb095_alpha_dummy_621 x D R)),
                                    ((nb095_alpha_dummy_623 D R S_cls E),
                                      (nb095_alpha_dummy_624 x D R)),
                                    ((nb095_alpha_dummy_617 D R S_cls E),
                                      (nb095_alpha_dummy_618 x D R)),
                                    ((nb095_alpha_dummy_615 D R S_cls E),
                                      (nb095_alpha_dummy_616 x D R)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif R (syn_cid)))
                                  (nb095_wpp_refl_0297 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
