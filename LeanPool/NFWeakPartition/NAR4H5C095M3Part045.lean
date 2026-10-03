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

@[expose]
noncomputable def nb095_wpp_refl_0333 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
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

@[expose]
noncomputable def nb095_split_alpha_0100 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TAlphaWff
      [((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
            (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) (by decide))
          (freshVar_injective (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                            (nb095_alpha_dummy_338 u S_cls E)),
                          ((nb095_alpha_dummy_335 D R S_cls E),
                            (nb095_alpha_dummy_336 u S_cls E)),
                          ((nb095_alpha_dummy_794 D R S_cls E),
                            (nb095_alpha_dummy_796 u S_cls E)),
                          ((nb095_alpha_dummy_793 D R S_cls E),
                            (nb095_alpha_dummy_795 u S_cls E)),
                          ((nb095_alpha_dummy_797 D R S_cls E),
                            (nb095_alpha_dummy_798 u S_cls E)),
                          ((nb095_alpha_dummy_791 D R S_cls E),
                            (nb095_alpha_dummy_792 u S_cls E)),
                          ((nb095_alpha_dummy_789 D R S_cls E),
                            (nb095_alpha_dummy_790 u S_cls E)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                        (nb095_focused_refl_0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_343 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0350 D R S_cls E)
                                                  0)))) (show u ≠ (nb095_alpha_dummy_344 u) from
                                        (by
                                          unfold nb095_alpha_dummy_344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0351 u) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_340 D R S_cls E) from (by
          unfold nb095_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_342 u S_cls) from (by
          unfold nb095_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_339 D R S_cls E) from (by
          unfold nb095_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0346 D R S_cls
                    E)
                  0)))) (show u ≠ (nb095_alpha_dummy_338 u S_cls E) from (by
          unfold nb095_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u S_cls E)
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
                  (nb095_support_mem_0345 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_794 D R S_cls E) from (by
          unfold nb095_alpha_dummy_794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_796 u S_cls E) from (by
          unfold nb095_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_793 D R S_cls E) from (by
          unfold nb095_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_795 u S_cls E) from (by
          unfold nb095_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_791 D R S_cls E) from (by
          unfold nb095_alpha_dummy_791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_792 u S_cls E) from (by
          unfold nb095_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_789 D R S_cls E) from (by
          unfold nb095_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_790 u S_cls E) from (by
          unfold nb095_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
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
        (nb095_split_alpha_0098 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_340 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u
        S_cls))).fv ∪ ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_340 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u
        S_cls))).fv ∪ ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_794 D R S_cls E),
                                    (nb095_alpha_dummy_796 u S_cls E)),
                                  ((nb095_alpha_dummy_793 D R S_cls E),
                                    (nb095_alpha_dummy_795 u S_cls E)),
                                  ((nb095_alpha_dummy_797 D R S_cls E),
                                    (nb095_alpha_dummy_798 u S_cls E)),
                                  ((nb095_alpha_dummy_791 D R S_cls E),
                                    (nb095_alpha_dummy_792 u S_cls E)),
                                  ((nb095_alpha_dummy_789 D R S_cls E),
                                    (nb095_alpha_dummy_790 u S_cls E)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                (nb095_wpp_refl_0333 x u D R S_cls f E dv_S_f dv_S_u
                                  dv_S_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                            (nb095_alpha_dummy_338 u S_cls E)),
                          ((nb095_alpha_dummy_335 D R S_cls E),
                            (nb095_alpha_dummy_336 u S_cls E)),
                          ((nb095_alpha_dummy_794 D R S_cls E),
                            (nb095_alpha_dummy_796 u S_cls E)),
                          ((nb095_alpha_dummy_793 D R S_cls E),
                            (nb095_alpha_dummy_795 u S_cls E)),
                          ((nb095_alpha_dummy_797 D R S_cls E),
                            (nb095_alpha_dummy_798 u S_cls E)),
                          ((nb095_alpha_dummy_791 D R S_cls E),
                            (nb095_alpha_dummy_792 u S_cls E)),
                          ((nb095_alpha_dummy_789 D R S_cls E),
                            (nb095_alpha_dummy_790 u S_cls E)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                        (nb095_focused_refl_0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_343 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_343;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0350 D R S_cls E)
                                                  0)))) (show u ≠ (nb095_alpha_dummy_344 u) from
                                        (by
                                          unfold nb095_alpha_dummy_344;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0351 u) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_340 D R S_cls E) from (by
          unfold nb095_alpha_dummy_340;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_342 u S_cls) from (by
          unfold nb095_alpha_dummy_342;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0349 u S_cls) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_001 D R S_cls E) ≠ (nb095_alpha_dummy_339 D R S_cls E) from (by
          unfold nb095_alpha_dummy_339;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0346 D R S_cls
                    E)
                  0)))) (show u ≠ (nb095_alpha_dummy_338 u S_cls E) from (by
          unfold nb095_alpha_dummy_338;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0347 u S_cls E)
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
                  (nb095_support_mem_0345 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_794 D R S_cls E) from (by
          unfold nb095_alpha_dummy_794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_796 u S_cls E) from (by
          unfold nb095_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_793 D R S_cls E) from (by
          unfold nb095_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_795 u S_cls E) from (by
          unfold nb095_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_791 D R S_cls E) from (by
          unfold nb095_alpha_dummy_791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_792 u S_cls E) from (by
          unfold nb095_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_789 D R S_cls E) from (by
          unfold nb095_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_790 u S_cls E) from (by
          unfold nb095_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
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
        (nb095_split_alpha_0098 x u D R S_cls f E))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_340 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u
        S_cls))).fv ∪ ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_340 D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_339 D
        R S_cls E))).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u
        S_cls))).fv ∪ ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0099 x u D R S_cls f E)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                [((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_794 D R S_cls E),
                                    (nb095_alpha_dummy_796 u S_cls E)),
                                  ((nb095_alpha_dummy_793 D R S_cls E),
                                    (nb095_alpha_dummy_795 u S_cls E)),
                                  ((nb095_alpha_dummy_797 D R S_cls E),
                                    (nb095_alpha_dummy_798 u S_cls E)),
                                  ((nb095_alpha_dummy_791 D R S_cls E),
                                    (nb095_alpha_dummy_792 u S_cls E)),
                                  ((nb095_alpha_dummy_789 D R S_cls E),
                                    (nb095_alpha_dummy_790 u S_cls E)),
                                  ((nb095_alpha_dummy_004 D R S_cls E),
                                    (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_003 D R S_cls E),
                                    (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                (nb095_wpp_refl_0333 x u D R S_cls f E dv_S_f dv_S_u
                                  dv_S_x))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                              (nb095_alpha_dummy_338 u S_cls E)),
                            ((nb095_alpha_dummy_335 D R S_cls E),
                              (nb095_alpha_dummy_336 u S_cls E)),
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                          (nb095_focused_refl_0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0348 D R S_cls
                    E)
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
                  (nb095_support_mem_0347 u S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_794 D R S_cls E) from (by
          unfold nb095_alpha_dummy_794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_796 u S_cls E) from (by
          unfold nb095_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_793 D R S_cls E) from (by
          unfold nb095_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_795 u S_cls E) from (by
          unfold nb095_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_791 D R S_cls E) from (by
          unfold nb095_alpha_dummy_791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_792 u S_cls E) from (by
          unfold nb095_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_789 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_790 u S_cls E) from (by
          unfold
            nb095_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0098 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_377
        D R S_cls E), (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_377
        D R S_cls E), (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_340 D R S_cls E),
                                      (nb095_alpha_dummy_342 u S_cls)),
                                    ((nb095_alpha_dummy_339 D R S_cls E),
                                      (nb095_alpha_dummy_341 u S_cls)),
                                    ((nb095_alpha_dummy_337 D R S_cls E),
                                      (nb095_alpha_dummy_338 u S_cls E)),
                                    ((nb095_alpha_dummy_335 D R S_cls E),
                                      (nb095_alpha_dummy_336 u S_cls E)),
                                    ((nb095_alpha_dummy_794 D R S_cls E),
                                      (nb095_alpha_dummy_796 u S_cls E)),
                                    ((nb095_alpha_dummy_793 D R S_cls E),
                                      (nb095_alpha_dummy_795 u S_cls E)),
                                    ((nb095_alpha_dummy_797 D R S_cls E),
                                      (nb095_alpha_dummy_798 u S_cls E)),
                                    ((nb095_alpha_dummy_791 D R S_cls E),
                                      (nb095_alpha_dummy_792 u S_cls E)),
                                    ((nb095_alpha_dummy_789 D R S_cls E),
                                      (nb095_alpha_dummy_790 u S_cls E)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                  (nb095_wpp_refl_0333 x u D R S_cls f E dv_S_f dv_S_u
                                    dv_S_x)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_337 D R S_cls E),
                              (nb095_alpha_dummy_338 u S_cls E)),
                            ((nb095_alpha_dummy_335 D R S_cls E),
                              (nb095_alpha_dummy_336 u S_cls E)),
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)] E
                          (nb095_focused_refl_0010 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show
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
                  (nb095_support_mem_0348 D R S_cls E)
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
                  (nb095_support_mem_0348 D R S_cls
                    E)
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
                  (nb095_support_mem_0347 u S_cls
                    E)
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
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_794 D R S_cls E) from (by
          unfold nb095_alpha_dummy_794;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D R
                    S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_796 u S_cls E) from (by
          unfold nb095_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_793 D R S_cls E) from (by
          unfold nb095_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0892 D
                    R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_795 u S_cls E) from (by
          unfold nb095_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0893 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0890
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0891
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_791 D R S_cls E) from (by
          unfold nb095_alpha_dummy_791;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0888
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_792 u S_cls E) from (by
          unfold nb095_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0889
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_789 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0886
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_790 u S_cls E) from (by
          unfold
            nb095_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0887
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_004 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  1)))) (show u ≠ (nb095_alpha_dummy_006 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0885
                    x u D R S_cls f
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_001 D R S_cls E) ≠
        (nb095_alpha_dummy_003 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0884
                    D R S_cls E)
                  0)))) (show u ≠ (nb095_alpha_dummy_005 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_005;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0098 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_339 D R S_cls E) ≠ (nb095_alpha_dummy_346 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_377
        D R S_cls E), (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                    D R S_cls E)
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
                    D R S_cls
                    E)
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
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0099 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_377
        D R S_cls E), (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                                  [((nb095_alpha_dummy_340 D R S_cls E),
                                      (nb095_alpha_dummy_342 u S_cls)),
                                    ((nb095_alpha_dummy_339 D R S_cls E),
                                      (nb095_alpha_dummy_341 u S_cls)),
                                    ((nb095_alpha_dummy_337 D R S_cls E),
                                      (nb095_alpha_dummy_338 u S_cls E)),
                                    ((nb095_alpha_dummy_335 D R S_cls E),
                                      (nb095_alpha_dummy_336 u S_cls E)),
                                    ((nb095_alpha_dummy_794 D R S_cls E),
                                      (nb095_alpha_dummy_796 u S_cls E)),
                                    ((nb095_alpha_dummy_793 D R S_cls E),
                                      (nb095_alpha_dummy_795 u S_cls E)),
                                    ((nb095_alpha_dummy_797 D R S_cls E),
                                      (nb095_alpha_dummy_798 u S_cls E)),
                                    ((nb095_alpha_dummy_791 D R S_cls E),
                                      (nb095_alpha_dummy_792 u S_cls E)),
                                    ((nb095_alpha_dummy_789 D R S_cls E),
                                      (nb095_alpha_dummy_790 u S_cls E)),
                                    ((nb095_alpha_dummy_004 D R S_cls E),
                                      (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_003 D R S_cls E),
                                      (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                  (nb095_wpp_refl_0333 x u D R S_cls f E dv_S_f dv_S_u
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

@[expose]
noncomputable def nb095_split_alpha_0101 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv)
    (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_f : f ∉ S_cls.fv)
    (dv_S_u : u ∉ S_cls.fv) (dv_S_x : x ∉ S_cls.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x)
    (dv_u_x : u ≠ x) :
    TAlphaWff
      [((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E)) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))
          (Class.cv (nb095_alpha_dummy_004 D R S_cls E))) (syn_wbr
          (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E))) (syn_cin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))
          (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))))
      (Wff.imp (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))
          (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))) (syn_wbr
          (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
          (syn_cin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))))
          (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0083 x u D R S_cls f E)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.neg (nb095_split_alpha_0084 x u D R S_cls f E)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095_split_alpha_0084 x u D R S_cls f E))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_617 D R S_cls E),
                            (nb095_alpha_dummy_618 x D R)),
                          ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] R
                        (nb095_focused_refl_0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_622 x D R) ≠
        (nb095_alpha_dummy_624 x D R) from (by
                                          unfold nb095_alpha_dummy_624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095_alpha_dummy_621 x D R) ≠
        (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from
        (by
          unfold
            nb095_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from
        (by
          unfold
            nb095_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_655 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_656 x D R) from
        (by
          unfold
            nb095_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_629 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_630 x D R) from
        (by
          unfold
            nb095_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_619
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_657
        D R S_cls E), (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
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
        (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from
        (by
          unfold
            nb095_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from
        (by
          unfold
            nb095_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_655 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_656 x D R) from
        (by
          unfold
            nb095_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_629 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_630 x D R) from
        (by
          unfold
            nb095_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_619
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_657
        D R S_cls E), (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
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
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095_split_alpha_0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_617 D R S_cls E),
                            (nb095_alpha_dummy_618 x D R)),
                          ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] R
                        (nb095_focused_refl_0007 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_623 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_623;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0642 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_622 x D R) ≠
        (nb095_alpha_dummy_624 x D R) from (by
                                          unfold nb095_alpha_dummy_624;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0643 x D R) 0)))))
                                    (TAlphaVar.there (Ne.symm (show
        (nb095_alpha_dummy_619 D R S_cls E) ≠ (nb095_alpha_dummy_623 D R S_cls E) from (by
          unfold nb095_alpha_dummy_623;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0640 D R S_cls E)
                  0))))) (Ne.symm (show (nb095_alpha_dummy_621 x D R) ≠
        (nb095_alpha_dummy_624 x D R) from (by
          unfold nb095_alpha_dummy_624;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0641 x D R) 0))))) (TAlphaVar.here _ _ _))))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0085 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from
        (by
          unfold
            nb095_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from
        (by
          unfold
            nb095_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_655 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_656 x D R) from
        (by
          unfold
            nb095_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_629 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_630 x D R) from
        (by
          unfold
            nb095_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_619
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_657
        D R S_cls E), (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
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
        (nb095_alpha_dummy_620 D R S_cls E) ≠ (nb095_alpha_dummy_626 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_628 x D R) from
        (by
          unfold
            nb095_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_625 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0672
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_627 x D R) from
        (by
          unfold
            nb095_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0674
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_655 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0676
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_656 x D R) from
        (by
          unfold
            nb095_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0677
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_620 D R S_cls E) ≠
        (nb095_alpha_dummy_629 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_629;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0673
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_622 x D R) ≠ (nb095_alpha_dummy_630 x D R) from
        (by
          unfold
            nb095_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0675
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_619
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_622 x D R))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0086 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_657
        D R S_cls E), (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
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
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095_split_alpha_0089 x u D R S_cls f E dv_D_f dv_D_u
                                  dv_D_x dv_R_f dv_R_u dv_R_x dv_u_x)))))))))))))))
    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg
                    (nb095_split_alpha_0092 x u D R S_cls f E dv_f_u dv_f_x)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095_split_alpha_0095 x u D R S_cls f E dv_f_u dv_f_x)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.neg
                            (nb095_split_alpha_0095 x u D R S_cls f E dv_f_u dv_f_x))))))))))))
      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_791 D R S_cls E),
                            (nb095_alpha_dummy_792 u S_cls E)),
                          ((nb095_alpha_dummy_789 D R S_cls E),
                            (nb095_alpha_dummy_790 u S_cls E)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] S_cls
                        (nb095_focused_refl_0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_796 u S_cls E) ≠
        (nb095_alpha_dummy_798 u S_cls E) from (by
                                          unfold nb095_alpha_dummy_798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095_alpha_dummy_795 u S_cls E) ≠
        (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_829 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_830
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_803 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_804
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_793
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_831
        D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_829 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_830
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_803 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_804
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_793
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_831
        D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095_split_alpha_0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn [((nb095_alpha_dummy_791 D R S_cls E),
                            (nb095_alpha_dummy_792 u S_cls E)),
                          ((nb095_alpha_dummy_789 D R S_cls E),
                            (nb095_alpha_dummy_790 u S_cls E)),
                          ((nb095_alpha_dummy_004 D R S_cls E),
                            (nb095_alpha_dummy_006 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_003 D R S_cls E),
                            (nb095_alpha_dummy_005 x u D R S_cls f E)),
                          ((nb095_alpha_dummy_001 D R S_cls E), u),
                          ((nb095_alpha_dummy_002 D R S_cls E), x),
                          ((nb095_alpha_dummy_000 D R S_cls E), f)] S_cls
                        (nb095_focused_refl_0009 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                                (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_797 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0844 D R S_cls E)
                                                  0))))) (Ne.symm (show
                                        (nb095_alpha_dummy_796 u S_cls E) ≠
        (nb095_alpha_dummy_798 u S_cls E) from (by
                                          unfold nb095_alpha_dummy_798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0845 u S_cls E)
                                                  0))))) (TAlphaVar.there (Ne.symm (show
        (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_797 D R S_cls E) from (by
          unfold nb095_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0842 D R S_cls E)
                  0))))) (Ne.symm (show (nb095_alpha_dummy_795 u S_cls E) ≠
        (nb095_alpha_dummy_798 u S_cls E) from (by
          unfold nb095_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0843 u S_cls E)
                  0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb095_split_alpha_0096 x u D R S_cls f E)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_829 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_830
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_803 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_804
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_793
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_831
        D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0874
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0876
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_829 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0878
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_830
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_830;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0879
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_794 D R S_cls E) ≠
        (nb095_alpha_dummy_803 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0875
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_804
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0877
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_793
        D R S_cls E))).fv ∪ ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪ ((Class.cv
        (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb095_split_alpha_0097 x u D R S_cls f E))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_831
        D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.neg
                                (nb095_split_alpha_0100 x u D R S_cls f E dv_E_f dv_E_u
                                  dv_E_x dv_S_f dv_S_u dv_S_x))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
