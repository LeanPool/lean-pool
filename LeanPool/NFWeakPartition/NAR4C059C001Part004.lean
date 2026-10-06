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

/-- Checked nominal proof certificate identified upstream as `nb059_wpp_refl_0009`. -/
@[expose]
noncomputable def nb059WppRefl0009 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TReflOn
      [((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (R).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0009 R S_cls a dv_R_a)

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0005`. -/
@[expose]
noncomputable def nb059SplitAlpha0005 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TAlphaWff
      [((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy009 R S_cls))
          (synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
            (Class.cv (nb059AlphaDummy000 R S_cls)))) (Wff.neg
          (Wff.classMem (Class.cv (nb059AlphaDummy009 R S_cls))
            (synCnin (synCima R (Class.cv (nb059AlphaDummy000 R S_cls)))
              (Class.cv (nb059AlphaDummy000 R S_cls))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy010 R a))
          (synCnin (synCima R (Class.cv a)) (Class.cv a))) (Wff.neg
          (Wff.classMem (Class.cv (nb059AlphaDummy010 R a))
            (synCnin (synCima R (Class.cv a)) (Class.cv a))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059AlphaDummy000 R S_cls) ≠
                              (nb059AlphaDummy014 R S_cls) from (by
                              unfold nb059AlphaDummy014;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                      1)))) (show a ≠ (nb059AlphaDummy016 R a) from (by
                              unfold nb059AlphaDummy016;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0009 R a) 1))))
                          (TAlphaVar.there (show (nb059AlphaDummy000 R S_cls) ≠
                                (nb059AlphaDummy013 R S_cls) from (by
                                unfold nb059AlphaDummy013;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                        0)))) (show a ≠ (nb059AlphaDummy015 R a) from (by
                                unfold nb059AlphaDummy015;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0009 R a) 0))))
                            (TAlphaVar.there (show (nb059AlphaDummy000 R S_cls) ≠
                                  (nb059AlphaDummy011 R S_cls) from (by
                                  unfold nb059AlphaDummy011;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0006 R S_cls)
                                          0)))) (show a ≠ (nb059AlphaDummy012 R a) from (by
                                  unfold nb059AlphaDummy012;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0007 R a)
                                          0)))) (TAlphaVar.there (show
                                  (nb059AlphaDummy000 R S_cls) ≠
                                    (nb059AlphaDummy009 R S_cls) from (by
                                    unfold nb059AlphaDummy009;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb059_support_mem_0004 R S_cls) 0))))
                                (show a ≠ (nb059AlphaDummy010 R a) from (by
                                    unfold nb059AlphaDummy010;
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
        (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠ (nb059AlphaDummy018 R S_cls)
        from (by
          unfold nb059AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy020 R a) from (by
          unfold nb059AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R a)
                  1)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy017 R S_cls) from (by
          unfold nb059AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy019 R a) from (by
          unfold nb059AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy023 R S_cls) from (by
          unfold nb059AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy024 R a) from (by
          unfold nb059AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy021 R S_cls) from (by
          unfold nb059AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy022 R a) from (by
          unfold nb059AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059SplitAlpha0001 R S_cls a)))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠ (nb059AlphaDummy018 R S_cls)
        from (by
          unfold nb059AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy020 R a) from (by
          unfold nb059AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R a)
                  1)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy017 R S_cls) from (by
          unfold nb059AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy019 R a) from (by
          unfold nb059AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy023 R S_cls) from (by
          unfold nb059AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy024 R a) from (by
          unfold nb059AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy021 R S_cls) from (by
          unfold nb059AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy022 R a) from (by
          unfold nb059AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059SplitAlpha0001 R S_cls a)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb059SplitAlpha0004 R S_cls a))))))))
                      (TAlphaClass.reflOfReflOn
                        [((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                          ((nb059AlphaDummy000 R S_cls), a),
                          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
                          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
                        R (nb059WppRefl0009 R S_cls a dv_R_a)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb059AlphaDummy000 R S_cls) ≠ (nb059AlphaDummy011 R S_cls) from
                    (by
                      unfold nb059AlphaDummy011;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0006 R S_cls) 0))))
                  (show a ≠ (nb059AlphaDummy012 R a) from (by
                      unfold nb059AlphaDummy012;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0007 R a) 0)))) (TAlphaVar.there
                    (show (nb059AlphaDummy000 R S_cls) ≠ (nb059AlphaDummy009 R S_cls) from
                      (by
                        unfold nb059AlphaDummy009;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0004 R S_cls) 0))))
                    (show a ≠ (nb059AlphaDummy010 R a) from (by
                        unfold nb059AlphaDummy010;
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
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059AlphaDummy000 R S_cls) ≠
                                (nb059AlphaDummy014 R S_cls) from (by
                                unfold nb059AlphaDummy014;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                        1)))) (show a ≠ (nb059AlphaDummy016 R a) from (by
                                unfold nb059AlphaDummy016;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0009 R a) 1))))
                            (TAlphaVar.there (show (nb059AlphaDummy000 R S_cls) ≠
                                  (nb059AlphaDummy013 R S_cls) from (by
                                  unfold nb059AlphaDummy013;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0008 R S_cls)
                                          0)))) (show a ≠ (nb059AlphaDummy015 R a) from (by
                                  unfold nb059AlphaDummy015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0009 R a)
                                          0)))) (TAlphaVar.there (show
                                  (nb059AlphaDummy000 R S_cls) ≠
                                    (nb059AlphaDummy011 R S_cls) from (by
                                    unfold nb059AlphaDummy011;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb059_support_mem_0006 R S_cls) 0))))
                                (show a ≠ (nb059AlphaDummy012 R a) from (by
                                    unfold nb059AlphaDummy012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb059_support_mem_0007 R a)
                                            0)))) (TAlphaVar.there (show
                                    (nb059AlphaDummy000 R S_cls) ≠
                                      (nb059AlphaDummy009 R S_cls) from (by
                                      unfold nb059AlphaDummy009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb059_support_mem_0004 R S_cls) 0))))
                                  (show a ≠ (nb059AlphaDummy010 R a) from (by
                                      unfold nb059AlphaDummy010;
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
        (nb059AlphaDummy014 R S_cls) ≠ (nb059AlphaDummy018 R S_cls) from (by
          unfold nb059AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy020 R a) from (by
          unfold nb059AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  1)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy017 R S_cls) from (by
          unfold nb059AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy019 R a) from (by
          unfold nb059AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy023 R S_cls) from (by
          unfold nb059AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy024 R a) from (by
          unfold nb059AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy021 R S_cls) from (by
          unfold
            nb059AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy022 R a) from (by
          unfold
            nb059AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059SplitAlpha0001 R S_cls a)))))
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb059AlphaDummy014 R S_cls) ≠ (nb059AlphaDummy018 R S_cls) from (by
          unfold nb059AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010 R
                    S_cls)
                  1)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy020 R a) from (by
          unfold nb059AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012 R
                    a)
                  1)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy017 R S_cls) from (by
          unfold nb059AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0010
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy019 R a) from (by
          unfold nb059AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0012
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy023 R S_cls) from (by
          unfold nb059AlphaDummy023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0014
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy024 R a) from (by
          unfold nb059AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0015
                    R a)
                  0)))) (TAlphaVar.there (show (nb059AlphaDummy014 R S_cls) ≠
        (nb059AlphaDummy021 R S_cls) from (by
          unfold
            nb059AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0011
                    R S_cls)
                  0)))) (show (nb059AlphaDummy016 R a) ≠ (nb059AlphaDummy022 R a) from (by
          unfold
            nb059AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb059_support_mem_0013
                    R a)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb059SplitAlpha0001 R S_cls a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb059SplitAlpha0004 R S_cls a))))))))
                        (TAlphaClass.reflOfReflOn
                          [((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                            ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                            ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                            ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                            ((nb059AlphaDummy000 R S_cls), a),
                            ((nb059AlphaDummy002 R S_cls),
                              (nb059AlphaDummy004 R S_cls a)),
                            ((nb059AlphaDummy001 R S_cls),
                              (nb059AlphaDummy003 R S_cls a))]
                          R (nb059WppRefl0009 R S_cls a dv_R_a)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show
                      (nb059AlphaDummy000 R S_cls) ≠ (nb059AlphaDummy011 R S_cls) from (by
                        unfold nb059AlphaDummy011;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0006 R S_cls) 0))))
                    (show a ≠ (nb059AlphaDummy012 R a) from (by
                        unfold nb059AlphaDummy012;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0007 R a) 0))))
                    (TAlphaVar.there (show
                        (nb059AlphaDummy000 R S_cls) ≠ (nb059AlphaDummy009 R S_cls) from
                        (by
                          unfold nb059AlphaDummy009;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0004 R S_cls) 0))))
                      (show a ≠ (nb059AlphaDummy010 R a) from (by
                          unfold nb059AlphaDummy010;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0005 R a) 0))))
                      (TAlphaVar.here _ _ _)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0006`. -/
@[expose]
noncomputable def nb059SplitAlpha0006 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
        ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
        ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
        ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
        ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
        ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
        ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
        ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
        ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy031 R S_cls))
            (synCun (Class.cv (nb059AlphaDummy032 R S_cls))
              (Class.cv (nb059AlphaDummy033 R S_cls))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy034 R a))
            (synCun (Class.cv (nb059AlphaDummy035 R a))
              (Class.cv (nb059AlphaDummy036 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                              (nb059AlphaDummy039 R S_cls) from (by
                              unfold nb059AlphaDummy039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0024 R S_cls)
                                      0))))
                          (show (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy040 R a) from
                            (by
                              unfold nb059AlphaDummy040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))))
                          (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                (nb059AlphaDummy037 R S_cls) from (by
                                unfold nb059AlphaDummy037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0022 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy038 R a) from (by
                                unfold nb059AlphaDummy038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                              (nb059AlphaDummy039 R S_cls) from (by
                              unfold nb059AlphaDummy039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0028 R S_cls)
                                      0))))
                          (show (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy040 R a) from
                            (by
                              unfold nb059AlphaDummy040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))))
                          (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                (nb059AlphaDummy037 R S_cls) from (by
                                unfold nb059AlphaDummy037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0026 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy038 R a) from (by
                                unfold nb059AlphaDummy038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                              (nb059AlphaDummy039 R S_cls) from (by
                              unfold nb059AlphaDummy039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0024 R S_cls)
                                      0))))
                          (show (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy040 R a) from
                            (by
                              unfold nb059AlphaDummy040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))))
                          (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                (nb059AlphaDummy037 R S_cls) from (by
                                unfold nb059AlphaDummy037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0022 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy038 R a) from (by
                                unfold nb059AlphaDummy038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                              (nb059AlphaDummy039 R S_cls) from (by
                              unfold nb059AlphaDummy039;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0028 R S_cls)
                                      0))))
                          (show (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy040 R a) from
                            (by
                              unfold nb059AlphaDummy040;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))))
                          (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                (nb059AlphaDummy037 R S_cls) from (by
                                unfold nb059AlphaDummy037;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0026 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy038 R a) from (by
                                unfold nb059AlphaDummy038;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
          ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
          ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
          ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
          ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
          ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
          ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
          ((nb059AlphaDummy000 R S_cls), a),
          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                (nb059AlphaDummy043 R S_cls) from (by
                                unfold nb059AlphaDummy043;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0032 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy044 R a) from (by
                                unfold nb059AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))))
                            (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                  (nb059AlphaDummy041 R S_cls) from (by
                                  unfold nb059AlphaDummy041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0030 R S_cls)
                                          0)))) (show
                                (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy042 R a) from
                                (by
                                  unfold nb059AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0031 R a)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                (nb059AlphaDummy043 R S_cls) from (by
                                unfold nb059AlphaDummy043;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0032 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy044 R a) from (by
                                unfold nb059AlphaDummy044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))))
                            (TAlphaVar.there (show (nb059AlphaDummy032 R S_cls) ≠
                                  (nb059AlphaDummy041 R S_cls) from (by
                                  unfold nb059AlphaDummy041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0030 R S_cls)
                                          0)))) (show
                                (nb059AlphaDummy035 R a) ≠ (nb059AlphaDummy042 R a) from
                                (by
                                  unfold nb059AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0031 R a)
                                          0)))) (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                (nb059AlphaDummy045 R S_cls) from (by
                                unfold nb059AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0036 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy046 R a) from (by
                                unfold nb059AlphaDummy046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))))
                            (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                  (nb059AlphaDummy041 R S_cls) from (by
                                  unfold nb059AlphaDummy041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0034 R S_cls)
                                          0)))) (show
                                (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy042 R a) from
                                (by
                                  unfold nb059AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0035 R a)
                                          0)))) (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                (nb059AlphaDummy045 R S_cls) from (by
                                unfold nb059AlphaDummy045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0036 R S_cls)
                                        0)))) (show
                              (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy046 R a) from (by
                                unfold nb059AlphaDummy046;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))))
                            (TAlphaVar.there (show (nb059AlphaDummy033 R S_cls) ≠
                                  (nb059AlphaDummy041 R S_cls) from (by
                                  unfold nb059AlphaDummy041;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0034 R S_cls)
                                          0)))) (show
                                (nb059AlphaDummy036 R a) ≠ (nb059AlphaDummy042 R a) from
                                (by
                                  unfold nb059AlphaDummy042;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0035 R a)
                                          0)))) (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
