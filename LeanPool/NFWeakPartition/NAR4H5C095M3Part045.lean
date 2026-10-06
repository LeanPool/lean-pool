/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part045Stage1


/-! NF weak partition development: NAR4H5C095M3Part045. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_wpp_refl_0333`. -/
@[expose]
noncomputable def nb095WppRefl0333 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      ((synCcnv (synCdif S_cls (synCid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0344 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0100`. -/
@[expose]
noncomputable def nb095SplitAlpha0100 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TAlphaWff
      [((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
            (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) (by decide))
          (freshVar_injective (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))).fv ∪ ((synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                            (nb095AlphaDummy338 u S_cls E)),
                          ((nb095AlphaDummy335 D R S_cls E),
                            (nb095AlphaDummy336 u S_cls E)),
                          ((nb095AlphaDummy794 D R S_cls E),
                            (nb095AlphaDummy796 u S_cls E)),
                          ((nb095AlphaDummy793 D R S_cls E),
                            (nb095AlphaDummy795 u S_cls E)),
                          ((nb095AlphaDummy797 D R S_cls E),
                            (nb095AlphaDummy798 u S_cls E)),
                          ((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] E
                        (nb095FocusedRefl0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy343 D R S_cls E) from (by
                                          unfold nb095AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0350 D R S_cls E)
                                                  0)))) (show u ≠ (nb095AlphaDummy344 u) from
                                        (by
                                          unfold nb095AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0351 u) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0346 D R S_cls
                    E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u S_cls E)
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
                  (nb095_support_mem_0345 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy794 D R S_cls E) from (by
          unfold nb095AlphaDummy794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy796 u S_cls E) from (by
          unfold nb095AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy793 D R S_cls E) from (by
          unfold nb095AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy795 u S_cls E) from (by
          unfold nb095AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy791 D R S_cls E) from (by
          unfold nb095AlphaDummy791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy792 u S_cls E) from (by
          unfold nb095AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy789 D R S_cls E) from (by
          unfold nb095AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy790 u S_cls E) from (by
          unfold nb095AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0098 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy340 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy342 u
        S_cls))).fv ∪ ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy340 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy342 u
        S_cls))).fv ∪ ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy794 D R S_cls E),
                                    (nb095AlphaDummy796 u S_cls E)),
                                  ((nb095AlphaDummy793 D R S_cls E),
                                    (nb095AlphaDummy795 u S_cls E)),
                                  ((nb095AlphaDummy797 D R S_cls E),
                                    (nb095AlphaDummy798 u S_cls E)),
                                  ((nb095AlphaDummy791 D R S_cls E),
                                    (nb095AlphaDummy792 u S_cls E)),
                                  ((nb095AlphaDummy789 D R S_cls E),
                                    (nb095AlphaDummy790 u S_cls E)),
                                  ((nb095AlphaDummy004 D R S_cls E),
                                    (nb095AlphaDummy006 x u D R S_cls f E)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif S_cls (synCid)))
                                (nb095WppRefl0333 x u D R S_cls f E dv_S_f dv_S_u
                                  dv_S_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                            (nb095AlphaDummy338 u S_cls E)),
                          ((nb095AlphaDummy335 D R S_cls E),
                            (nb095AlphaDummy336 u S_cls E)),
                          ((nb095AlphaDummy794 D R S_cls E),
                            (nb095AlphaDummy796 u S_cls E)),
                          ((nb095AlphaDummy793 D R S_cls E),
                            (nb095AlphaDummy795 u S_cls E)),
                          ((nb095AlphaDummy797 D R S_cls E),
                            (nb095AlphaDummy798 u S_cls E)),
                          ((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] E
                        (nb095FocusedRefl0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy343 D R S_cls E) from (by
                                          unfold nb095AlphaDummy343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0350 D R S_cls E)
                                                  0)))) (show u ≠ (nb095AlphaDummy344 u) from
                                        (by
                                          unfold nb095AlphaDummy344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0351 u) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy340 D R S_cls E) from (by
          unfold nb095AlphaDummy340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy342 u S_cls) from (by
          unfold nb095AlphaDummy342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy001 D R S_cls E) ≠ (nb095AlphaDummy339 D R S_cls E) from (by
          unfold nb095AlphaDummy339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0346 D R S_cls
                    E)
                  0)))) (show u ≠ (nb095AlphaDummy338 u S_cls E) from (by
          unfold nb095AlphaDummy338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u S_cls E)
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
                  (nb095_support_mem_0345 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy794 D R S_cls E) from (by
          unfold nb095AlphaDummy794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy796 u S_cls E) from (by
          unfold nb095AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy793 D R S_cls E) from (by
          unfold nb095AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy795 u S_cls E) from (by
          unfold nb095AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy791 D R S_cls E) from (by
          unfold nb095AlphaDummy791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy792 u S_cls E) from (by
          unfold nb095AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy789 D R S_cls E) from (by
          unfold nb095AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy790 u S_cls E) from (by
          unfold nb095AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0098 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy340 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy342 u
        S_cls))).fv ∪ ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy340 D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095AlphaDummy342 u
        S_cls))).fv ∪ ((Class.cv (nb095AlphaDummy341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy377 D R S_cls E), (nb095AlphaDummy378 u S_cls)),
        ((nb095AlphaDummy346 D R S_cls E), (nb095AlphaDummy348 u S_cls)),
        ((nb095AlphaDummy345 D R S_cls E), (nb095AlphaDummy347 u S_cls)),
        ((nb095AlphaDummy375 D R S_cls E), (nb095AlphaDummy376 u S_cls)),
        ((nb095AlphaDummy349 D R S_cls E), (nb095AlphaDummy350 u S_cls)),
        ((nb095AlphaDummy340 D R S_cls E), (nb095AlphaDummy342 u S_cls)),
        ((nb095AlphaDummy339 D R S_cls E), (nb095AlphaDummy341 u S_cls)),
        ((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                [((nb095AlphaDummy340 D R S_cls E),
                                    (nb095AlphaDummy342 u S_cls)),
                                  ((nb095AlphaDummy339 D R S_cls E),
                                    (nb095AlphaDummy341 u S_cls)),
                                  ((nb095AlphaDummy337 D R S_cls E),
                                    (nb095AlphaDummy338 u S_cls E)),
                                  ((nb095AlphaDummy335 D R S_cls E),
                                    (nb095AlphaDummy336 u S_cls E)),
                                  ((nb095AlphaDummy794 D R S_cls E),
                                    (nb095AlphaDummy796 u S_cls E)),
                                  ((nb095AlphaDummy793 D R S_cls E),
                                    (nb095AlphaDummy795 u S_cls E)),
                                  ((nb095AlphaDummy797 D R S_cls E),
                                    (nb095AlphaDummy798 u S_cls E)),
                                  ((nb095AlphaDummy791 D R S_cls E),
                                    (nb095AlphaDummy792 u S_cls E)),
                                  ((nb095AlphaDummy789 D R S_cls E),
                                    (nb095AlphaDummy790 u S_cls E)),
                                  ((nb095AlphaDummy004 D R S_cls E),
                                    (nb095AlphaDummy006 x u D R S_cls f E)),
                                  ((nb095AlphaDummy003 D R S_cls E),
                                    (nb095AlphaDummy005 x u D R S_cls f E)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCcnv (synCdif S_cls (synCid)))
                                (nb095WppRefl0333 x u D R S_cls f E dv_S_f dv_S_u
                                  dv_S_x))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                              (nb095AlphaDummy338 u S_cls E)),
                            ((nb095AlphaDummy335 D R S_cls E),
                              (nb095AlphaDummy336 u S_cls E)),
                            ((nb095AlphaDummy794 D R S_cls E),
                              (nb095AlphaDummy796 u S_cls E)),
                            ((nb095AlphaDummy793 D R S_cls E),
                              (nb095AlphaDummy795 u S_cls E)),
                            ((nb095AlphaDummy797 D R S_cls E),
                              (nb095AlphaDummy798 u S_cls E)),
                            ((nb095AlphaDummy791 D R S_cls E),
                              (nb095AlphaDummy792 u S_cls E)),
                            ((nb095AlphaDummy789 D R S_cls E),
                              (nb095AlphaDummy790 u S_cls E)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] E
                          (nb095FocusedRefl0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0348 D R S_cls
                    E)
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
                  (nb095_support_mem_0347 u S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy794 D R S_cls E) from (by
          unfold nb095AlphaDummy794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy796 u S_cls E) from (by
          unfold nb095AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy793 D R S_cls E) from (by
          unfold nb095AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy795 u S_cls E) from (by
          unfold nb095AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy791 D R S_cls E) from (by
          unfold nb095AlphaDummy791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy792 u S_cls E) from (by
          unfold nb095AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy789 D R S_cls E) from (by
          unfold
            nb095AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy790 u S_cls E) from (by
          unfold
            nb095AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0098 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy377
        D R S_cls E), (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy377
        D R S_cls E), (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy340 D R S_cls E),
                                      (nb095AlphaDummy342 u S_cls)),
                                    ((nb095AlphaDummy339 D R S_cls E),
                                      (nb095AlphaDummy341 u S_cls)),
                                    ((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy794 D R S_cls E),
                                      (nb095AlphaDummy796 u S_cls E)),
                                    ((nb095AlphaDummy793 D R S_cls E),
                                      (nb095AlphaDummy795 u S_cls E)),
                                    ((nb095AlphaDummy797 D R S_cls E),
                                      (nb095AlphaDummy798 u S_cls E)),
                                    ((nb095AlphaDummy791 D R S_cls E),
                                      (nb095AlphaDummy792 u S_cls E)),
                                    ((nb095AlphaDummy789 D R S_cls E),
                                      (nb095AlphaDummy790 u S_cls E)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif S_cls (synCid)))
                                  (nb095WppRefl0333 x u D R S_cls f E dv_S_f dv_S_u
                                    dv_S_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfReflOn [((nb095AlphaDummy337 D R S_cls E),
                              (nb095AlphaDummy338 u S_cls E)),
                            ((nb095AlphaDummy335 D R S_cls E),
                              (nb095AlphaDummy336 u S_cls E)),
                            ((nb095AlphaDummy794 D R S_cls E),
                              (nb095AlphaDummy796 u S_cls E)),
                            ((nb095AlphaDummy793 D R S_cls E),
                              (nb095AlphaDummy795 u S_cls E)),
                            ((nb095AlphaDummy797 D R S_cls E),
                              (nb095AlphaDummy798 u S_cls E)),
                            ((nb095AlphaDummy791 D R S_cls E),
                              (nb095AlphaDummy792 u S_cls E)),
                            ((nb095AlphaDummy789 D R S_cls E),
                              (nb095AlphaDummy790 u S_cls E)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)] E
                          (nb095FocusedRefl0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0348 D R S_cls
                    E)
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
                  (nb095_support_mem_0347 u S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy794 D R S_cls E) from (by
          unfold nb095AlphaDummy794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy796 u S_cls E) from (by
          unfold nb095AlphaDummy796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy793 D R S_cls E) from (by
          unfold nb095AlphaDummy793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy795 u S_cls E) from (by
          unfold nb095AlphaDummy795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy791 D R S_cls E) from (by
          unfold nb095AlphaDummy791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy792 u S_cls E) from (by
          unfold nb095AlphaDummy792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy789 D R S_cls E) from (by
          unfold
            nb095AlphaDummy789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy790 u S_cls E) from (by
          unfold
            nb095AlphaDummy790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy004 D R S_cls E) from (by
          unfold
            nb095AlphaDummy004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095AlphaDummy006 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy001 D R S_cls E) ≠
        (nb095AlphaDummy003 D R S_cls E) from (by
          unfold
            nb095AlphaDummy003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095AlphaDummy005 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0098 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy339 D R S_cls E) ≠ (nb095AlphaDummy346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy377
        D R S_cls E), (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy377
        D R S_cls E), (nb095AlphaDummy378 u S_cls)), ((nb095AlphaDummy346 D R S_cls E),
        (nb095AlphaDummy348 u S_cls)), ((nb095AlphaDummy345 D R S_cls E),
        (nb095AlphaDummy347 u S_cls)), ((nb095AlphaDummy375 D R S_cls E),
        (nb095AlphaDummy376 u S_cls)), ((nb095AlphaDummy349 D R S_cls E),
        (nb095AlphaDummy350 u S_cls)), ((nb095AlphaDummy340 D R S_cls E),
        (nb095AlphaDummy342 u S_cls)), ((nb095AlphaDummy339 D R S_cls E),
        (nb095AlphaDummy341 u S_cls)), ((nb095AlphaDummy337 D R S_cls E),
        (nb095AlphaDummy338 u S_cls E)), ((nb095AlphaDummy335 D R S_cls E),
        (nb095AlphaDummy336 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
                                  [((nb095AlphaDummy340 D R S_cls E),
                                      (nb095AlphaDummy342 u S_cls)),
                                    ((nb095AlphaDummy339 D R S_cls E),
                                      (nb095AlphaDummy341 u S_cls)),
                                    ((nb095AlphaDummy337 D R S_cls E),
                                      (nb095AlphaDummy338 u S_cls E)),
                                    ((nb095AlphaDummy335 D R S_cls E),
                                      (nb095AlphaDummy336 u S_cls E)),
                                    ((nb095AlphaDummy794 D R S_cls E),
                                      (nb095AlphaDummy796 u S_cls E)),
                                    ((nb095AlphaDummy793 D R S_cls E),
                                      (nb095AlphaDummy795 u S_cls E)),
                                    ((nb095AlphaDummy797 D R S_cls E),
                                      (nb095AlphaDummy798 u S_cls E)),
                                    ((nb095AlphaDummy791 D R S_cls E),
                                      (nb095AlphaDummy792 u S_cls E)),
                                    ((nb095AlphaDummy789 D R S_cls E),
                                      (nb095AlphaDummy790 u S_cls E)),
                                    ((nb095AlphaDummy004 D R S_cls E),
                                      (nb095AlphaDummy006 x u D R S_cls f E)),
                                    ((nb095AlphaDummy003 D R S_cls E),
                                      (nb095AlphaDummy005 x u D R S_cls f E)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCcnv (synCdif S_cls (synCid)))
                                  (nb095WppRefl0333 x u D R S_cls f E dv_S_f dv_S_u
                                    dv_S_x)))))))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0101`. -/
@[expose]
noncomputable def nb095SplitAlpha0101 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E)) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))
          (Class.cv (nb095AlphaDummy004 D R S_cls E))) (synWbr
          (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E))) (synCin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))
          (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))))
      (Wff.imp (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))
          (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))) (synWbr
          (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
          (synCin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))))
          (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0083 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.neg (nb095SplitAlpha0084 x u D R S_cls f E)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0084 x u D R S_cls f E))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy617 D R S_cls E),
                            (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] R
                        (nb095FocusedRefl0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
                                          unfold nb095AlphaDummy623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy622 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
                                          unfold nb095AlphaDummy624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy621 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
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
        (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
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
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy617 D R S_cls E),
                            (nb095AlphaDummy618 x D R)),
                          ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] R
                        (nb095FocusedRefl0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy623 D R S_cls E) from (by
                                          unfold nb095AlphaDummy623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy622 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
                                          unfold nb095AlphaDummy624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy619 D R S_cls E) ≠ (nb095AlphaDummy623 D R S_cls E) from (by
          unfold nb095AlphaDummy623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy621 x D R) ≠
        (nb095AlphaDummy624 x D R) from (by
          unfold nb095AlphaDummy624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
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
        (nb095AlphaDummy620 D R S_cls E) ≠ (nb095AlphaDummy626 D R S_cls E) from (by
          unfold
            nb095AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy628 x D R) from
        (by
          unfold
            nb095AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy625 D R S_cls E) from (by
          unfold
            nb095AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy627 x D R) from
        (by
          unfold
            nb095AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy655 D R S_cls E) from (by
          unfold
            nb095AlphaDummy655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy656 x D R) from
        (by
          unfold
            nb095AlphaDummy656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy620 D R S_cls E) ≠
        (nb095AlphaDummy629 D R S_cls E) from (by
          unfold
            nb095AlphaDummy629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy622 x D R) ≠ (nb095AlphaDummy630 x D R) from
        (by
          unfold
            nb095AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy619
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪ ((Class.cv
        (nb095AlphaDummy622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy657
        D R S_cls E), (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
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
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x)))))))))))))))
    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb095SplitAlpha0092 x u D R S_cls f E dv_f_u dv_f_x)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0095 x u D R S_cls f E dv_f_u dv_f_x)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095SplitAlpha0095 x u D R S_cls f E dv_f_u dv_f_x))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] S_cls
                        (nb095FocusedRefl0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
                                          unfold nb095AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy796 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
                                          unfold nb095AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy795 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn [((nb095AlphaDummy791 D R S_cls E),
                            (nb095AlphaDummy792 u S_cls E)),
                          ((nb095AlphaDummy789 D R S_cls E),
                            (nb095AlphaDummy790 u S_cls E)),
                          ((nb095AlphaDummy004 D R S_cls E),
                            (nb095AlphaDummy006 x u D R S_cls f E)),
                          ((nb095AlphaDummy003 D R S_cls E),
                            (nb095AlphaDummy005 x u D R S_cls f E)),
                          ((nb095AlphaDummy001 D R S_cls E), u),
                          ((nb095AlphaDummy002 D R S_cls E), x),
                          ((nb095AlphaDummy000 D R S_cls E), f)] S_cls
                        (nb095FocusedRefl0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy797 D R S_cls E) from (by
                                          unfold nb095AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095AlphaDummy796 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
                                          unfold nb095AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy797 D R S_cls E) from (by
          unfold nb095AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095AlphaDummy795 u S_cls E) ≠
        (nb095AlphaDummy798 u S_cls E) from (by
          unfold nb095AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095SplitAlpha0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
          unfold
            nb095AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy799 D R S_cls E) from (by
          unfold
            nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy829 D R S_cls E) from (by
          unfold
            nb095AlphaDummy829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy830
        u S_cls E) from (by
          unfold
            nb095AlphaDummy830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy794 D R S_cls E) ≠
        (nb095AlphaDummy803 D R S_cls E) from (by
          unfold
            nb095AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy804
        u S_cls E) from (by
          unfold
            nb095AlphaDummy804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy793
        D R S_cls E))).fv ∪ ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪ ((Class.cv
        (nb095AlphaDummy796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095SplitAlpha0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed [((nb095AlphaDummy831
        D R S_cls E), (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
        (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095SplitAlpha0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
