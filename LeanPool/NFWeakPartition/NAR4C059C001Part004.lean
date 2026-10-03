/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C059C001Part004Stage1


/-! NF weak partition development: NAR4C059C001Part004. -/


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
noncomputable def nb059_wpp_refl_0009 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TReflOn
      [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
        ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (R).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0009 R S_cls a dv_R_a)

@[expose]
noncomputable def nb059_split_alpha_0005 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TAlphaWff
      [((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_009 R S_cls))
          (syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))) (Wff.neg
          (Wff.classMem (Class.cv (nb059_alpha_dummy_009 R S_cls))
            (syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_010 R a))
          (syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))) (Wff.neg
          (Wff.classMem (Class.cv (nb059_alpha_dummy_010 R a))
            (syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059_alpha_dummy_000 R S_cls) ≠
                              (nb059_alpha_dummy_014 R S_cls) from (by
                              unfold nb059_alpha_dummy_014;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                      1)))) (show a ≠ (nb059_alpha_dummy_016 R a) from (by
                              unfold nb059_alpha_dummy_016;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0009 R a) 1))))
                          (TAlphaVar.there (show (nb059_alpha_dummy_000 R S_cls) ≠
                                (nb059_alpha_dummy_013 R S_cls) from (by
                                unfold nb059_alpha_dummy_013;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                        0)))) (show a ≠ (nb059_alpha_dummy_015 R a) from (by
                                unfold nb059_alpha_dummy_015;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0009 R a) 0))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_000 R S_cls) ≠
                                  (nb059_alpha_dummy_011 R S_cls) from (by
                                  unfold nb059_alpha_dummy_011;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0006 R S_cls)
                                          0)))) (show a ≠ (nb059_alpha_dummy_012 R a) from (by
                                  unfold nb059_alpha_dummy_012;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0007 R a)
                                          0)))) (TAlphaVar.there (show
                                  (nb059_alpha_dummy_000 R S_cls) ≠
                                    (nb059_alpha_dummy_009 R S_cls) from (by
                                    unfold nb059_alpha_dummy_009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb059_support_mem_0004 R S_cls) 0))))
                                (show a ≠ (nb059_alpha_dummy_010 R a) from (by
                                    unfold nb059_alpha_dummy_010;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb059_support_mem_0005 R a)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠ (nb059_alpha_dummy_018 R S_cls)
        from (by
          unfold nb059_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_020 R a) from (by
          unfold nb059_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R a)
                  1)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_017 R S_cls) from (by
          unfold nb059_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_019 R a) from (by
          unfold nb059_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_023 R S_cls) from (by
          unfold nb059_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_024 R a) from (by
          unfold nb059_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_021 R S_cls) from (by
          unfold nb059_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_022 R a) from (by
          unfold nb059_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059_split_alpha_0001 R S_cls a)))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠ (nb059_alpha_dummy_018 R S_cls)
        from (by
          unfold nb059_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_020 R a) from (by
          unfold nb059_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R a)
                  1)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_017 R S_cls) from (by
          unfold nb059_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_019 R a) from (by
          unfold nb059_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_023 R S_cls) from (by
          unfold nb059_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_024 R a) from (by
          unfold nb059_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_021 R S_cls) from (by
          unfold nb059_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_022 R a) from (by
          unfold nb059_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059_split_alpha_0001 R S_cls a)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb059_split_alpha_0004 R S_cls a))))))))
                      (TAlphaClass.refl_of_reflOn
                        [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                          ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                          ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                          ((nb059_alpha_dummy_000 R S_cls), a),
                          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
                          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                        R (nb059_wpp_refl_0009 R S_cls a dv_R_a)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb059_alpha_dummy_000 R S_cls) ≠ (nb059_alpha_dummy_011 R S_cls) from
                    (by
                      unfold nb059_alpha_dummy_011;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0006 R S_cls) 0))))
                  (show a ≠ (nb059_alpha_dummy_012 R a) from (by
                      unfold nb059_alpha_dummy_012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0007 R a) 0)))) (TAlphaVar.there
                    (show (nb059_alpha_dummy_000 R S_cls) ≠ (nb059_alpha_dummy_009 R S_cls) from
                      (by
                        unfold nb059_alpha_dummy_009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0004 R S_cls) 0))))
                    (show a ≠ (nb059_alpha_dummy_010 R a) from (by
                        unfold nb059_alpha_dummy_010;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0005 R a) 0))))
                    (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059_alpha_dummy_000 R S_cls) ≠
                                (nb059_alpha_dummy_014 R S_cls) from (by
                                unfold nb059_alpha_dummy_014;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                        1)))) (show a ≠ (nb059_alpha_dummy_016 R a) from (by
                                unfold nb059_alpha_dummy_016;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0009 R a) 1))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_000 R S_cls) ≠
                                  (nb059_alpha_dummy_013 R S_cls) from (by
                                  unfold nb059_alpha_dummy_013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                          0)))) (show a ≠ (nb059_alpha_dummy_015 R a) from (by
                                  unfold nb059_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0009 R a)
                                          0)))) (TAlphaVar.there (show
                                  (nb059_alpha_dummy_000 R S_cls) ≠
                                    (nb059_alpha_dummy_011 R S_cls) from (by
                                    unfold nb059_alpha_dummy_011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb059_support_mem_0006 R S_cls) 0))))
                                (show a ≠ (nb059_alpha_dummy_012 R a) from (by
                                    unfold nb059_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb059_support_mem_0007 R a)
                                            0)))) (TAlphaVar.there (show
                                    (nb059_alpha_dummy_000 R S_cls) ≠
                                      (nb059_alpha_dummy_009 R S_cls) from (by
                                      unfold nb059_alpha_dummy_009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb059_support_mem_0004 R S_cls) 0))))
                                  (show a ≠ (nb059_alpha_dummy_010 R a) from (by
                                      unfold nb059_alpha_dummy_010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb059_support_mem_0005 R a)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb059_alpha_dummy_014 R S_cls) ≠ (nb059_alpha_dummy_018 R S_cls) from (by
          unfold nb059_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_020 R a) from (by
          unfold nb059_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  1)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_017 R S_cls) from (by
          unfold nb059_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_019 R a) from (by
          unfold nb059_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_023 R S_cls) from (by
          unfold nb059_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_024 R a) from (by
          unfold nb059_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_021 R S_cls) from (by
          unfold
            nb059_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_022 R a) from (by
          unfold
            nb059_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059_split_alpha_0001 R S_cls a)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb059_alpha_dummy_014 R S_cls) ≠ (nb059_alpha_dummy_018 R S_cls) from (by
          unfold nb059_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_020 R a) from (by
          unfold nb059_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  1)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_017 R S_cls) from (by
          unfold nb059_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_019 R a) from (by
          unfold nb059_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_023 R S_cls) from (by
          unfold nb059_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_024 R a) from (by
          unfold nb059_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059_alpha_dummy_014 R S_cls) ≠
        (nb059_alpha_dummy_021 R S_cls) from (by
          unfold
            nb059_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059_alpha_dummy_016 R a) ≠ (nb059_alpha_dummy_022 R a) from (by
          unfold
            nb059_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059_split_alpha_0001 R S_cls a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb059_split_alpha_0004 R S_cls a))))))))
                        (TAlphaClass.refl_of_reflOn
                          [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                            ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                            ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                            ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                            ((nb059_alpha_dummy_000 R S_cls), a),
                            ((nb059_alpha_dummy_002 R S_cls),
                              (nb059_alpha_dummy_004 R S_cls a)),
                            ((nb059_alpha_dummy_001 R S_cls),
                              (nb059_alpha_dummy_003 R S_cls a))]
                          R (nb059_wpp_refl_0009 R S_cls a dv_R_a)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show
                      (nb059_alpha_dummy_000 R S_cls) ≠ (nb059_alpha_dummy_011 R S_cls) from (by
                        unfold nb059_alpha_dummy_011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0006 R S_cls) 0))))
                    (show a ≠ (nb059_alpha_dummy_012 R a) from (by
                        unfold nb059_alpha_dummy_012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0007 R a) 0))))
                    (TAlphaVar.there (show
                        (nb059_alpha_dummy_000 R S_cls) ≠ (nb059_alpha_dummy_009 R S_cls) from
                        (by
                          unfold nb059_alpha_dummy_009;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0004 R S_cls) 0))))
                      (show a ≠ (nb059_alpha_dummy_010 R a) from (by
                          unfold nb059_alpha_dummy_010;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0005 R a) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

@[expose]
noncomputable def nb059_split_alpha_0006 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
        ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
        ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
        ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
        ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
        ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
        ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_031 R S_cls))
            (syn_cun (Class.cv (nb059_alpha_dummy_032 R S_cls))
              (Class.cv (nb059_alpha_dummy_033 R S_cls))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_034 R a))
            (syn_cun (Class.cv (nb059_alpha_dummy_035 R a))
              (Class.cv (nb059_alpha_dummy_036 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                              (nb059_alpha_dummy_039 R S_cls) from (by
                              unfold nb059_alpha_dummy_039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0024 R S_cls)
                                      0))))
                          (show (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_040 R a) from
                            (by
                              unfold nb059_alpha_dummy_040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))))
                          (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                (nb059_alpha_dummy_037 R S_cls) from (by
                                unfold nb059_alpha_dummy_037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0022 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_038 R a) from (by
                                unfold nb059_alpha_dummy_038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                              (nb059_alpha_dummy_039 R S_cls) from (by
                              unfold nb059_alpha_dummy_039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0028 R S_cls)
                                      0))))
                          (show (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_040 R a) from
                            (by
                              unfold nb059_alpha_dummy_040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))))
                          (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                (nb059_alpha_dummy_037 R S_cls) from (by
                                unfold nb059_alpha_dummy_037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0026 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_038 R a) from (by
                                unfold nb059_alpha_dummy_038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                              (nb059_alpha_dummy_039 R S_cls) from (by
                              unfold nb059_alpha_dummy_039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0024 R S_cls)
                                      0))))
                          (show (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_040 R a) from
                            (by
                              unfold nb059_alpha_dummy_040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))))
                          (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                (nb059_alpha_dummy_037 R S_cls) from (by
                                unfold nb059_alpha_dummy_037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0022 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_038 R a) from (by
                                unfold nb059_alpha_dummy_038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                              (nb059_alpha_dummy_039 R S_cls) from (by
                              unfold nb059_alpha_dummy_039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0028 R S_cls)
                                      0))))
                          (show (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_040 R a) from
                            (by
                              unfold nb059_alpha_dummy_040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))))
                          (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                (nb059_alpha_dummy_037 R S_cls) from (by
                                unfold nb059_alpha_dummy_037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0026 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_038 R a) from (by
                                unfold nb059_alpha_dummy_038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
          ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
          ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
          ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
          ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
          ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
          ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
          ((nb059_alpha_dummy_000 R S_cls), a),
          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                (nb059_alpha_dummy_043 R S_cls) from (by
                                unfold nb059_alpha_dummy_043;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0032 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_044 R a) from (by
                                unfold nb059_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                  (nb059_alpha_dummy_041 R S_cls) from (by
                                  unfold nb059_alpha_dummy_041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0030 R S_cls)
                                          0)))) (show
                                (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_042 R a) from
                                (by
                                  unfold nb059_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0031 R a)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                (nb059_alpha_dummy_043 R S_cls) from (by
                                unfold nb059_alpha_dummy_043;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0032 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_044 R a) from (by
                                unfold nb059_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_032 R S_cls) ≠
                                  (nb059_alpha_dummy_041 R S_cls) from (by
                                  unfold nb059_alpha_dummy_041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0030 R S_cls)
                                          0)))) (show
                                (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_042 R a) from
                                (by
                                  unfold nb059_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0031 R a)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                (nb059_alpha_dummy_045 R S_cls) from (by
                                unfold nb059_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0036 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_046 R a) from (by
                                unfold nb059_alpha_dummy_046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                  (nb059_alpha_dummy_041 R S_cls) from (by
                                  unfold nb059_alpha_dummy_041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0034 R S_cls)
                                          0)))) (show
                                (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_042 R a) from
                                (by
                                  unfold nb059_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0035 R a)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                (nb059_alpha_dummy_045 R S_cls) from (by
                                unfold nb059_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0036 R S_cls)
                                        0)))) (show
                              (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_046 R a) from (by
                                unfold nb059_alpha_dummy_046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))))
                            (TAlphaVar.there (show (nb059_alpha_dummy_033 R S_cls) ≠
                                  (nb059_alpha_dummy_041 R S_cls) from (by
                                  unfold nb059_alpha_dummy_041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0034 R S_cls)
                                          0)))) (show
                                (nb059_alpha_dummy_036 R a) ≠ (nb059_alpha_dummy_042 R a) from
                                (by
                                  unfold nb059_alpha_dummy_042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0035 R a)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
