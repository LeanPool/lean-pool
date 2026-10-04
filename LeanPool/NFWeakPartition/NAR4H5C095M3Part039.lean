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

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0297`. -/
@[expose]
noncomputable def nb095WppRefl0297 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCcnv (synCdif R (synCid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0306 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0089`. -/
@[expose]
noncomputable def nb095SplitAlpha0089 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
        (Wff.neg (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
            (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv) (by decide))
          (freshVar_injective (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv x))))).fv ∪ ((synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                            (nb095AlphaDummy248 x D R)),
                          ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
                          ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
                          ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
                          ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
                          ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] D
                        (nb095FocusedRefl0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy253 D R S_cls E) from (by
                                          unfold nb095AlphaDummy253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095AlphaDummy254 x) from
                                        (by
                                          unfold nb095AlphaDummy254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0254 D R S_cls E)
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
                  (nb095_support_mem_0252 D R S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy620 D R S_cls E) from (by
          unfold nb095AlphaDummy620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy622 x D R) from (by
          unfold nb095AlphaDummy622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy619 D R S_cls E) from (by
          unfold nb095AlphaDummy619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy621 x D R) from (by
          unfold nb095AlphaDummy621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy617 D R S_cls E) from (by
          unfold nb095AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy618 x D R) from (by
          unfold nb095AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy615 D R S_cls E) from (by
          unfold nb095AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy616 x D R) from (by
          unfold nb095AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
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
        (nb095SplitAlpha0087 x u D R S_cls f E))))) (TAlphaWff.classMem
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy250 D R S_cls E),
                                    (nb095AlphaDummy252 x R)),
                                  ((nb095AlphaDummy249 D R S_cls E),
                                    (nb095AlphaDummy251 x R)),
                                  ((nb095AlphaDummy247 D R S_cls E),
                                    (nb095AlphaDummy248 x D R)),
                                  ((nb095AlphaDummy245 D R S_cls E),
                                    (nb095AlphaDummy246 x D R)),
                                  ((nb095AlphaDummy620 D R S_cls E),
                                    (nb095AlphaDummy622 x D R)),
                                  ((nb095AlphaDummy619 D R S_cls E),
                                    (nb095AlphaDummy621 x D R)),
                                  ((nb095AlphaDummy623 D R S_cls E),
                                    (nb095AlphaDummy624 x D R)),
                                  ((nb095AlphaDummy617 D R S_cls E),
                                    (nb095AlphaDummy618 x D R)),
                                  ((nb095AlphaDummy615 D R S_cls E),
                                    (nb095AlphaDummy616 x D R)),
                                  ((nb095AlphaDummy004 D R S_cls E),
                                    (nb095AlphaDummy006 x u D R S_cls f E)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif R (synCid)))
                                (nb095WppRefl0297 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                            (nb095AlphaDummy248 x D R)),
                          ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
                          ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
                          ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
                          ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
                          ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] D
                        (nb095FocusedRefl0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy253 D R S_cls E) from (by
                                          unfold nb095AlphaDummy253;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0256 D R S_cls E)
                                                  0)))) (show x ≠ (nb095AlphaDummy254 x) from
                                        (by
                                          unfold nb095AlphaDummy254;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0257 x) 0))))
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0254 D R S_cls E)
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
                  (nb095_support_mem_0252 D R S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy620 D R S_cls E) from (by
          unfold nb095AlphaDummy620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy622 x D R) from (by
          unfold nb095AlphaDummy622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy619 D R S_cls E) from (by
          unfold nb095AlphaDummy619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy621 x D R) from (by
          unfold nb095AlphaDummy621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy617 D R S_cls E) from (by
          unfold nb095AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy618 x D R) from (by
          unfold nb095AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy615 D R S_cls E) from (by
          unfold nb095AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy616 x D R) from (by
          unfold nb095AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
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
        (nb095SplitAlpha0087 x u D R S_cls f E))))) (TAlphaWff.classMem
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy250 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy249 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy252 x
        R))).fv ∪ ((Class.cv (nb095AlphaDummy251 x R))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0088 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy287 D R S_cls E), (nb095AlphaDummy288 x R)),
        ((nb095AlphaDummy256 D R S_cls E), (nb095AlphaDummy258 x R)),
        ((nb095AlphaDummy255 D R S_cls E), (nb095AlphaDummy257 x R)),
        ((nb095AlphaDummy285 D R S_cls E), (nb095AlphaDummy286 x R)),
        ((nb095AlphaDummy259 D R S_cls E), (nb095AlphaDummy260 x R)),
        ((nb095AlphaDummy250 D R S_cls E), (nb095AlphaDummy252 x R)),
        ((nb095AlphaDummy249 D R S_cls E), (nb095AlphaDummy251 x R)),
        ((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy250 D R S_cls E),
                                    (nb095AlphaDummy252 x R)),
                                  ((nb095AlphaDummy249 D R S_cls E),
                                    (nb095AlphaDummy251 x R)),
                                  ((nb095AlphaDummy247 D R S_cls E),
                                    (nb095AlphaDummy248 x D R)),
                                  ((nb095AlphaDummy245 D R S_cls E),
                                    (nb095AlphaDummy246 x D R)),
                                  ((nb095AlphaDummy620 D R S_cls E),
                                    (nb095AlphaDummy622 x D R)),
                                  ((nb095AlphaDummy619 D R S_cls E),
                                    (nb095AlphaDummy621 x D R)),
                                  ((nb095AlphaDummy623 D R S_cls E),
                                    (nb095AlphaDummy624 x D R)),
                                  ((nb095AlphaDummy617 D R S_cls E),
                                    (nb095AlphaDummy618 x D R)),
                                  ((nb095AlphaDummy615 D R S_cls E),
                                    (nb095AlphaDummy616 x D R)),
                                  ((nb095AlphaDummy004 D R S_cls E),
                                    (nb095AlphaDummy006 x u D R S_cls f E)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif R (synCid)))
                                (nb095WppRefl0297 x u D R S_cls f E dv_R_f dv_R_u
                                  dv_R_x))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                              (nb095AlphaDummy248 x D R)),
                            ((nb095AlphaDummy245 D R S_cls E),
                              (nb095AlphaDummy246 x D R)),
                            ((nb095AlphaDummy620 D R S_cls E),
                              (nb095AlphaDummy622 x D R)),
                            ((nb095AlphaDummy619 D R S_cls E),
                              (nb095AlphaDummy621 x D R)),
                            ((nb095AlphaDummy623 D R S_cls E),
                              (nb095AlphaDummy624 x D R)),
                            ((nb095AlphaDummy617 D R S_cls E),
                              (nb095AlphaDummy618 x D R)),
                            ((nb095AlphaDummy615 D R S_cls E),
                              (nb095AlphaDummy616 x D R)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] D
                          (nb095FocusedRefl0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy620 D R S_cls E) from (by
          unfold nb095AlphaDummy620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy622 x D R) from (by
          unfold nb095AlphaDummy622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy619 D R S_cls E) from (by
          unfold nb095AlphaDummy619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy621 x D R) from (by
          unfold nb095AlphaDummy621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy617 D R S_cls E) from (by
          unfold nb095AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy618 x D R) from (by
          unfold nb095AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy615 D R S_cls E) from (by
          unfold
            nb095AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy616 x D R) from (by
          unfold
            nb095AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0087 x u D R S_cls f E)))))
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy287
        D R S_cls E), (nb095AlphaDummy288 x R)), ((nb095AlphaDummy256 D R S_cls E),
        (nb095AlphaDummy258 x R)), ((nb095AlphaDummy255 D R S_cls E),
        (nb095AlphaDummy257 x R)), ((nb095AlphaDummy285 D R S_cls E),
        (nb095AlphaDummy286 x R)), ((nb095AlphaDummy259 D R S_cls E),
        (nb095AlphaDummy260 x R)), ((nb095AlphaDummy250 D R S_cls E),
        (nb095AlphaDummy252 x R)), ((nb095AlphaDummy249 D R S_cls E),
        (nb095AlphaDummy251 x R)), ((nb095AlphaDummy247 D R S_cls E),
        (nb095AlphaDummy248 x D R)), ((nb095AlphaDummy245 D R S_cls E),
        (nb095AlphaDummy246 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy287
        D R S_cls E), (nb095AlphaDummy288 x R)), ((nb095AlphaDummy256 D R S_cls E),
        (nb095AlphaDummy258 x R)), ((nb095AlphaDummy255 D R S_cls E),
        (nb095AlphaDummy257 x R)), ((nb095AlphaDummy285 D R S_cls E),
        (nb095AlphaDummy286 x R)), ((nb095AlphaDummy259 D R S_cls E),
        (nb095AlphaDummy260 x R)), ((nb095AlphaDummy250 D R S_cls E),
        (nb095AlphaDummy252 x R)), ((nb095AlphaDummy249 D R S_cls E),
        (nb095AlphaDummy251 x R)), ((nb095AlphaDummy247 D R S_cls E),
        (nb095AlphaDummy248 x D R)), ((nb095AlphaDummy245 D R S_cls E),
        (nb095AlphaDummy246 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy620 D R S_cls E),
                                      (nb095AlphaDummy622 x D R)),
                                    ((nb095AlphaDummy619 D R S_cls E),
                                      (nb095AlphaDummy621 x D R)),
                                    ((nb095AlphaDummy623 D R S_cls E),
                                      (nb095AlphaDummy624 x D R)),
                                    ((nb095AlphaDummy617 D R S_cls E),
                                      (nb095AlphaDummy618 x D R)),
                                    ((nb095AlphaDummy615 D R S_cls E),
                                      (nb095AlphaDummy616 x D R)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif R (synCid)))
                                  (nb095WppRefl0297 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy247 D R S_cls E),
                              (nb095AlphaDummy248 x D R)),
                            ((nb095AlphaDummy245 D R S_cls E),
                              (nb095AlphaDummy246 x D R)),
                            ((nb095AlphaDummy620 D R S_cls E),
                              (nb095AlphaDummy622 x D R)),
                            ((nb095AlphaDummy619 D R S_cls E),
                              (nb095AlphaDummy621 x D R)),
                            ((nb095AlphaDummy623 D R S_cls E),
                              (nb095AlphaDummy624 x D R)),
                            ((nb095AlphaDummy617 D R S_cls E),
                              (nb095AlphaDummy618 x D R)),
                            ((nb095AlphaDummy615 D R S_cls E),
                              (nb095AlphaDummy616 x D R)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] D
                          (nb095FocusedRefl0008 x u D R S_cls f E dv_D_f dv_D_u dv_D_x)))
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy620 D R S_cls E) from (by
          unfold nb095AlphaDummy620;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D R
                    S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy622 x D R) from (by
          unfold nb095AlphaDummy622;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x D
                    R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy619 D R S_cls E) from (by
          unfold nb095AlphaDummy619;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0688 D
                    R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy621 x D R) from (by
          unfold nb095AlphaDummy621;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0689 x
                    D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0686
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0687
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy617 D R S_cls E) from (by
          unfold nb095AlphaDummy617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0684
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy618 x D R) from (by
          unfold nb095AlphaDummy618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0685
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy615 D R S_cls E) from (by
          unfold
            nb095AlphaDummy615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0682
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy616 x D R) from (by
          unfold
            nb095AlphaDummy616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0683
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  1)))) (show x ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0601
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy002 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0600
                    D R S_cls E)
                  0)))) (show x ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0087 x u D R S_cls f E)))))
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy287
        D R S_cls E), (nb095AlphaDummy288 x R)), ((nb095AlphaDummy256 D R S_cls E),
        (nb095AlphaDummy258 x R)), ((nb095AlphaDummy255 D R S_cls E),
        (nb095AlphaDummy257 x R)), ((nb095AlphaDummy285 D R S_cls E),
        (nb095AlphaDummy286 x R)), ((nb095AlphaDummy259 D R S_cls E),
        (nb095AlphaDummy260 x R)), ((nb095AlphaDummy250 D R S_cls E),
        (nb095AlphaDummy252 x R)), ((nb095AlphaDummy249 D R S_cls E),
        (nb095AlphaDummy251 x R)), ((nb095AlphaDummy247 D R S_cls E),
        (nb095AlphaDummy248 x D R)), ((nb095AlphaDummy245 D R S_cls E),
        (nb095AlphaDummy246 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy249 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) from (by
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
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0088 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy287
        D R S_cls E), (nb095AlphaDummy288 x R)), ((nb095AlphaDummy256 D R S_cls E),
        (nb095AlphaDummy258 x R)), ((nb095AlphaDummy255 D R S_cls E),
        (nb095AlphaDummy257 x R)), ((nb095AlphaDummy285 D R S_cls E),
        (nb095AlphaDummy286 x R)), ((nb095AlphaDummy259 D R S_cls E),
        (nb095AlphaDummy260 x R)), ((nb095AlphaDummy250 D R S_cls E),
        (nb095AlphaDummy252 x R)), ((nb095AlphaDummy249 D R S_cls E),
        (nb095AlphaDummy251 x R)), ((nb095AlphaDummy247 D R S_cls E),
        (nb095AlphaDummy248 x D R)), ((nb095AlphaDummy245 D R S_cls E),
        (nb095AlphaDummy246 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy250 D R S_cls E),
                                      (nb095AlphaDummy252 x R)),
                                    ((nb095AlphaDummy249 D R S_cls E),
                                      (nb095AlphaDummy251 x R)),
                                    ((nb095AlphaDummy247 D R S_cls E),
                                      (nb095AlphaDummy248 x D R)),
                                    ((nb095AlphaDummy245 D R S_cls E),
                                      (nb095AlphaDummy246 x D R)),
                                    ((nb095AlphaDummy620 D R S_cls E),
                                      (nb095AlphaDummy622 x D R)),
                                    ((nb095AlphaDummy619 D R S_cls E),
                                      (nb095AlphaDummy621 x D R)),
                                    ((nb095AlphaDummy623 D R S_cls E),
                                      (nb095AlphaDummy624 x D R)),
                                    ((nb095AlphaDummy617 D R S_cls E),
                                      (nb095AlphaDummy618 x D R)),
                                    ((nb095AlphaDummy615 D R S_cls E),
                                      (nb095AlphaDummy616 x D R)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif R (synCid)))
                                  (nb095WppRefl0297 x u D R S_cls f E dv_R_f dv_R_u
                                    dv_R_x)))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
