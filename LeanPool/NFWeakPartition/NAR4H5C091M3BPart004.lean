/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart003

/-! NF weak partition development: NAR4H5C091M3BPart004. -/


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
noncomputable def nb091_split_alpha_0003 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_071 D R), (nb091_alpha_dummy_072 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_071 D R))
          (Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_071 D R))
            (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_072 D R p))
          (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_072 D R p))
            (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
                (Class.cv (nb091_alpha_dummy_061 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
                      unfold nb091_alpha_dummy_066;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
                  (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
                      unfold nb091_alpha_dummy_068;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
                        unfold nb091_alpha_dummy_065;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
                    (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_067 D R p) from (by
                        unfold nb091_alpha_dummy_067;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_071 D R) from (by
                          unfold nb091_alpha_dummy_071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0052 D R) 0))))
                      (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_072 D R p) from
                        (by
                          unfold nb091_alpha_dummy_072;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0053 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_069 D R) from (by
                            unfold nb091_alpha_dummy_069;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0049 D R) 0)))) (show
                          (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_070 D R p) from (by
                            unfold nb091_alpha_dummy_070;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0051 D R p) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_cin D
                                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                                        (syn_cuni (Class.cv
        (nb091_alpha_dummy_000 D R)))))))).fv ∪ ((syn_cin D
                                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                                        (syn_cuni
        (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) (by decide)) (freshVar_injective
                            (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪
                              ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_060 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_073 D R) from
                            (by
                              unfold nb091_alpha_dummy_073;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0054 D R) 0)))) (show
                            (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_075 D R p) from
                            (by
                              unfold nb091_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                          (TAlphaVar.there (show
                              (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_074 D R) from (by
                                unfold nb091_alpha_dummy_074;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0054 D R) 1)))) (show
                              (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_076 D R p) from
                              (by
                                unfold nb091_alpha_dummy_076;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_066 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_080 D R) from
        (by
          unfold nb091_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R) 1)))) (show (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_083 D R p) from (by
          unfold nb091_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_079 D R) from (by
          unfold nb091_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  0)))) (show (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_082 D R p) from
        (by
          unfold nb091_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_077 D R) from (by
          unfold nb091_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R)
                  0)))) (show (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
        (by
          unfold nb091_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_081 D R), (nb091_alpha_dummy_084 D R p)),
        ((nb091_alpha_dummy_080 D R), (nb091_alpha_dummy_083 D R p)),
        ((nb091_alpha_dummy_079 D R), (nb091_alpha_dummy_082 D R p)),
        ((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
        ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
        ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_071 D R), (nb091_alpha_dummy_072 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_081 D R), (nb091_alpha_dummy_084 D R p)),
        ((nb091_alpha_dummy_080 D R), (nb091_alpha_dummy_083 D R p)),
        ((nb091_alpha_dummy_079 D R), (nb091_alpha_dummy_082 D R p)),
        ((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
        ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
        ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_071 D R), (nb091_alpha_dummy_072 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from
        (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from
        (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081
        D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081
        D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091_alpha_dummy_075 D R p) ≠
                                        (nb091_alpha_dummy_078 D R p) from (by
                                        unfold nb091_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                                    ((nb091_alpha_dummy_073 D R),
                                      (nb091_alpha_dummy_075 D R p)),
                                    ((nb091_alpha_dummy_074 D R),
                                      (nb091_alpha_dummy_076 D R p)),
                                    ((nb091_alpha_dummy_066 D R),
                                      (nb091_alpha_dummy_068 D R p)),
                                    ((nb091_alpha_dummy_065 D R),
                                      (nb091_alpha_dummy_067 D R p)),
                                    ((nb091_alpha_dummy_071 D R),
                                      (nb091_alpha_dummy_072 D R p)),
                                    ((nb091_alpha_dummy_069 D R),
                                      (nb091_alpha_dummy_070 D R p)),
                                    ((nb091_alpha_dummy_060 D R),
                                      (nb091_alpha_dummy_062 D R p)),
                                    ((nb091_alpha_dummy_059 D R),
                                      (nb091_alpha_dummy_061 D R p)),
                                    ((nb091_alpha_dummy_063 D R),
                                      (nb091_alpha_dummy_064 D R p)),
                                    ((nb091_alpha_dummy_057 D R),
                                      (nb091_alpha_dummy_058 D R p)),
                                    ((nb091_alpha_dummy_055 D R),
                                      (nb091_alpha_dummy_056 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_053 D R),
                                      (nb091_alpha_dummy_054 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_077;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                              0)))) (show (nb091_alpha_dummy_075 D R p) ≠
                                      (nb091_alpha_dummy_078 D R p) from (by
                                      unfold nb091_alpha_dummy_078;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb091_support_mem_0057 D R p) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091_alpha_dummy_075 D R p) ≠
                                        (nb091_alpha_dummy_078 D R p) from (by
                                        unfold nb091_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                                    ((nb091_alpha_dummy_073 D R),
                                      (nb091_alpha_dummy_075 D R p)),
                                    ((nb091_alpha_dummy_074 D R),
                                      (nb091_alpha_dummy_076 D R p)),
                                    ((nb091_alpha_dummy_066 D R),
                                      (nb091_alpha_dummy_068 D R p)),
                                    ((nb091_alpha_dummy_065 D R),
                                      (nb091_alpha_dummy_067 D R p)),
                                    ((nb091_alpha_dummy_071 D R),
                                      (nb091_alpha_dummy_072 D R p)),
                                    ((nb091_alpha_dummy_069 D R),
                                      (nb091_alpha_dummy_070 D R p)),
                                    ((nb091_alpha_dummy_060 D R),
                                      (nb091_alpha_dummy_062 D R p)),
                                    ((nb091_alpha_dummy_059 D R),
                                      (nb091_alpha_dummy_061 D R p)),
                                    ((nb091_alpha_dummy_063 D R),
                                      (nb091_alpha_dummy_064 D R p)),
                                    ((nb091_alpha_dummy_057 D R),
                                      (nb091_alpha_dummy_058 D R p)),
                                    ((nb091_alpha_dummy_055 D R),
                                      (nb091_alpha_dummy_056 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_053 D R),
                                      (nb091_alpha_dummy_054 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
                        unfold nb091_alpha_dummy_066;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
                    (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
                        unfold nb091_alpha_dummy_068;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
                          unfold nb091_alpha_dummy_065;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
                      (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_067 D R p) from
                        (by
                          unfold nb091_alpha_dummy_067;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_071 D R) from (by
                            unfold nb091_alpha_dummy_071;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0052 D R) 0)))) (show
                          (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_072 D R p) from (by
                            unfold nb091_alpha_dummy_072;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0053 D R p) 0))))
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_069 D R) from
                            (by
                              unfold nb091_alpha_dummy_069;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0049 D R) 0)))) (show
                            (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_070 D R p) from
                            (by
                              unfold nb091_alpha_dummy_070;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0051 D R p) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                        (syn_cuni (syn_cuni (Class.cv
        (nb091_alpha_dummy_000 D R)))))))).fv ∪ ((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                        (syn_cuni (syn_cuni (Class.cv
        (nb091_alpha_dummy_000 D R)))))))).fv) (by decide)) (freshVar_injective (((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪
                                ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_073 D R) from (by
                                unfold nb091_alpha_dummy_073;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0054 D R) 0)))) (show
                              (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_075 D R p) from
                              (by
                                unfold nb091_alpha_dummy_075;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                        0)))) (TAlphaVar.there (show
                                (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_074 D R) from
                                (by
                                  unfold nb091_alpha_dummy_074;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0054 D R)
                                          1)))) (show (nb091_alpha_dummy_068 D R p) ≠
                                  (nb091_alpha_dummy_076 D R p) from (by
                                  unfold nb091_alpha_dummy_076;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0055 D R p)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_066 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_080 D R) from (by
          unfold nb091_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  1)))) (show (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_083 D R p) from
        (by
          unfold nb091_alpha_dummy_083;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_079 D R) from (by
          unfold nb091_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R)
                  0)))) (show (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_082 D R p) from
        (by
          unfold nb091_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_077 D R) from (by
          unfold nb091_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R)
                  0)))) (show (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
        (by
          unfold nb091_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R
                    p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_081 D R), (nb091_alpha_dummy_084 D R p)),
        ((nb091_alpha_dummy_080 D R), (nb091_alpha_dummy_083 D R p)),
        ((nb091_alpha_dummy_079 D R), (nb091_alpha_dummy_082 D R p)),
        ((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
        ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
        ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_071 D R), (nb091_alpha_dummy_072 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_081 D R), (nb091_alpha_dummy_084 D R p)),
        ((nb091_alpha_dummy_080 D R), (nb091_alpha_dummy_083 D R p)),
        ((nb091_alpha_dummy_079 D R), (nb091_alpha_dummy_082 D R p)),
        ((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
        ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
        ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_071 D R), (nb091_alpha_dummy_072 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from
        (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from
        (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081
        D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081
        D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_077 D R) from (by
                                          unfold nb091_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0056 D R) 0)))) (show
                                        (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_078 D R p) from (by
                                          unfold nb091_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0057 D R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_077 D R),
                                        (nb091_alpha_dummy_078 D R p)),
                                      ((nb091_alpha_dummy_073 D R),
                                        (nb091_alpha_dummy_075 D R p)),
                                      ((nb091_alpha_dummy_074 D R),
                                        (nb091_alpha_dummy_076 D R p)),
                                      ((nb091_alpha_dummy_066 D R),
                                        (nb091_alpha_dummy_068 D R p)),
                                      ((nb091_alpha_dummy_065 D R),
                                        (nb091_alpha_dummy_067 D R p)),
                                      ((nb091_alpha_dummy_071 D R),
                                        (nb091_alpha_dummy_072 D R p)),
                                      ((nb091_alpha_dummy_069 D R),
                                        (nb091_alpha_dummy_070 D R p)),
                                      ((nb091_alpha_dummy_060 D R),
                                        (nb091_alpha_dummy_062 D R p)),
                                      ((nb091_alpha_dummy_059 D R),
                                        (nb091_alpha_dummy_061 D R p)),
                                      ((nb091_alpha_dummy_063 D R),
                                        (nb091_alpha_dummy_064 D R p)),
                                      ((nb091_alpha_dummy_057 D R),
                                        (nb091_alpha_dummy_058 D R p)),
                                      ((nb091_alpha_dummy_055 D R),
                                        (nb091_alpha_dummy_056 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_053 D R),
                                        (nb091_alpha_dummy_054 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_077;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0056 D R) 0)))) (show
                                      (nb091_alpha_dummy_075 D R p) ≠
                                        (nb091_alpha_dummy_078 D R p) from (by
                                        unfold nb091_alpha_dummy_078;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0057 D R p) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_077 D R) from (by
                                          unfold nb091_alpha_dummy_077;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0056 D R) 0)))) (show
                                        (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_078 D R p) from (by
                                          unfold nb091_alpha_dummy_078;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0057 D R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_077 D R),
                                        (nb091_alpha_dummy_078 D R p)),
                                      ((nb091_alpha_dummy_073 D R),
                                        (nb091_alpha_dummy_075 D R p)),
                                      ((nb091_alpha_dummy_074 D R),
                                        (nb091_alpha_dummy_076 D R p)),
                                      ((nb091_alpha_dummy_066 D R),
                                        (nb091_alpha_dummy_068 D R p)),
                                      ((nb091_alpha_dummy_065 D R),
                                        (nb091_alpha_dummy_067 D R p)),
                                      ((nb091_alpha_dummy_071 D R),
                                        (nb091_alpha_dummy_072 D R p)),
                                      ((nb091_alpha_dummy_069 D R),
                                        (nb091_alpha_dummy_070 D R p)),
                                      ((nb091_alpha_dummy_060 D R),
                                        (nb091_alpha_dummy_062 D R p)),
                                      ((nb091_alpha_dummy_059 D R),
                                        (nb091_alpha_dummy_061 D R p)),
                                      ((nb091_alpha_dummy_063 D R),
                                        (nb091_alpha_dummy_064 D R p)),
                                      ((nb091_alpha_dummy_057 D R),
                                        (nb091_alpha_dummy_058 D R p)),
                                      ((nb091_alpha_dummy_055 D R),
                                        (nb091_alpha_dummy_056 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_053 D R),
                                        (nb091_alpha_dummy_054 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb091_split_alpha_0004 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
        ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_099 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_099 D R))
            (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_100 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_100 D R p))
            (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_073 D R) from (by
                      unfold nb091_alpha_dummy_073;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0054 D R) 0))))
                  (show (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_075 D R p) from (by
                      unfold nb091_alpha_dummy_075;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_074 D R) from (by
                        unfold nb091_alpha_dummy_074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0054 D R) 1))))
                    (show (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_076 D R p) from (by
                        unfold nb091_alpha_dummy_076;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0055 D R p) 1))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_099 D R) from (by
                          unfold nb091_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0084 D R) 0))))
                      (show (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_100 D R p) from
                        (by
                          unfold nb091_alpha_dummy_100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0085 D R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_097 D R) from (by
                            unfold nb091_alpha_dummy_097;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0082 D R) 0)))) (show
                          (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_098 D R p) from (by
                            unfold nb091_alpha_dummy_098;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0083 D R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_066 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_068 D R p))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_080 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_080;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0058 D R) 1)))) (show
                                      (nb091_alpha_dummy_075 D R p) ≠
                                        (nb091_alpha_dummy_083 D R p) from (by
                                        unfold nb091_alpha_dummy_083;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0059 D R p) 1))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_079 D R) from (by
                                          unfold nb091_alpha_dummy_079;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0058 D R) 0)))) (show
                                        (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_082 D R p) from (by
                                          unfold nb091_alpha_dummy_082;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0059 D R p) 0))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_077 D R) from (by
          unfold nb091_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R) 0)))) (show (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_078 D R p) from (by
          unfold nb091_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_081 D R),
        (nb091_alpha_dummy_084 D R p)), ((nb091_alpha_dummy_080 D R),
        (nb091_alpha_dummy_083 D R p)), ((nb091_alpha_dummy_079 D R),
        (nb091_alpha_dummy_082 D R p)), ((nb091_alpha_dummy_077 D R),
        (nb091_alpha_dummy_078 D R p)), ((nb091_alpha_dummy_073 D R),
        (nb091_alpha_dummy_075 D R p)), ((nb091_alpha_dummy_074 D R),
        (nb091_alpha_dummy_076 D R p)), ((nb091_alpha_dummy_099 D R),
        (nb091_alpha_dummy_100 D R p)), ((nb091_alpha_dummy_097 D R),
        (nb091_alpha_dummy_098 D R p)), ((nb091_alpha_dummy_066 D R),
        (nb091_alpha_dummy_068 D R p)), ((nb091_alpha_dummy_065 D R),
        (nb091_alpha_dummy_067 D R p)), ((nb091_alpha_dummy_095 D R),
        (nb091_alpha_dummy_096 D R p)), ((nb091_alpha_dummy_069 D R),
        (nb091_alpha_dummy_070 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
                                        ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_087 D R) from (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_087 D R) from (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb091_alpha_dummy_081 D R),
        (nb091_alpha_dummy_084 D R p)), ((nb091_alpha_dummy_080 D R),
        (nb091_alpha_dummy_083 D R p)), ((nb091_alpha_dummy_079 D R),
        (nb091_alpha_dummy_082 D R p)), ((nb091_alpha_dummy_077 D R),
        (nb091_alpha_dummy_078 D R p)), ((nb091_alpha_dummy_073 D R),
        (nb091_alpha_dummy_075 D R p)), ((nb091_alpha_dummy_074 D R),
        (nb091_alpha_dummy_076 D R p)), ((nb091_alpha_dummy_099 D R),
        (nb091_alpha_dummy_100 D R p)), ((nb091_alpha_dummy_097 D R),
        (nb091_alpha_dummy_098 D R p)), ((nb091_alpha_dummy_066 D R),
        (nb091_alpha_dummy_068 D R p)), ((nb091_alpha_dummy_065 D R),
        (nb091_alpha_dummy_067 D R p)), ((nb091_alpha_dummy_095 D R),
        (nb091_alpha_dummy_096 D R p)), ((nb091_alpha_dummy_069 D R),
        (nb091_alpha_dummy_070 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_091 D R) from (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from (by
                                unfold nb091_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
                              (by
                                unfold nb091_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                            ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
                            ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
                            ((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
                            ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
                            ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
                            ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
                            ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
                            ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
                            ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                            ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                            ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                            ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                            ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                            ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                            ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                            ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                            ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                            ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                            ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                            ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                            ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                            ((nb091_alpha_dummy_000 D R), p),
                            ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from
                            (by
                              unfold nb091_alpha_dummy_077;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                            (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
                            (by
                              unfold nb091_alpha_dummy_078;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0057 D R p) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from (by
                                unfold nb091_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
                              (by
                                unfold nb091_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                            ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
                            ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
                            ((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
                            ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
                            ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
                            ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
                            ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
                            ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
                            ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                            ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                            ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                            ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                            ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                            ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                            ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                            ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                            ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                            ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                            ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                            ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                            ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                            ((nb091_alpha_dummy_000 D R), p),
                            ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_073 D R) from (by
                        unfold nb091_alpha_dummy_073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0054 D R) 0))))
                    (show (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_075 D R p) from (by
                        unfold nb091_alpha_dummy_075;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0055 D R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_074 D R) from (by
                          unfold nb091_alpha_dummy_074;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0054 D R) 1))))
                      (show (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_076 D R p) from
                        (by
                          unfold nb091_alpha_dummy_076;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0055 D R p) 1))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_099 D R) from (by
                            unfold nb091_alpha_dummy_099;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0084 D R) 0)))) (show
                          (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_100 D R p) from (by
                            unfold nb091_alpha_dummy_100;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0085 D R p) 0))))
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_066 D R) ≠ (nb091_alpha_dummy_097 D R) from
                            (by
                              unfold nb091_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0082 D R) 0)))) (show
                            (nb091_alpha_dummy_068 D R p) ≠ (nb091_alpha_dummy_098 D R p) from
                            (by
                              unfold nb091_alpha_dummy_098;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0083 D R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_066 D R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_068 D R p))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_080 D R) from (by
                                          unfold nb091_alpha_dummy_080;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0058 D R) 1)))) (show
                                        (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_083 D R p) from (by
                                          unfold nb091_alpha_dummy_083;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0059 D R p) 1))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_073 D R) ≠
        (nb091_alpha_dummy_079 D R) from (by
          unfold nb091_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0058 D R) 0)))) (show (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_082 D R p) from (by
          unfold nb091_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0059 D R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from (by
          unfold nb091_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0056 D R) 0)))) (show (nb091_alpha_dummy_075 D R p) ≠
        (nb091_alpha_dummy_078 D R p) from (by
          unfold nb091_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0057 D R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_081 D R),
        (nb091_alpha_dummy_084 D R p)), ((nb091_alpha_dummy_080 D R),
        (nb091_alpha_dummy_083 D R p)), ((nb091_alpha_dummy_079 D R),
        (nb091_alpha_dummy_082 D R p)), ((nb091_alpha_dummy_077 D R),
        (nb091_alpha_dummy_078 D R p)), ((nb091_alpha_dummy_073 D R),
        (nb091_alpha_dummy_075 D R p)), ((nb091_alpha_dummy_074 D R),
        (nb091_alpha_dummy_076 D R p)), ((nb091_alpha_dummy_099 D R),
        (nb091_alpha_dummy_100 D R p)), ((nb091_alpha_dummy_097 D R),
        (nb091_alpha_dummy_098 D R p)), ((nb091_alpha_dummy_066 D R),
        (nb091_alpha_dummy_068 D R p)), ((nb091_alpha_dummy_065 D R),
        (nb091_alpha_dummy_067 D R p)), ((nb091_alpha_dummy_095 D R),
        (nb091_alpha_dummy_096 D R p)), ((nb091_alpha_dummy_069 D R),
        (nb091_alpha_dummy_070 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_080 D
        R) ≠ (nb091_alpha_dummy_087 D R) from (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0062
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0063
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0060
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0061
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠ (nb091_alpha_dummy_087 D R) from
        (by
          unfold
            nb091_alpha_dummy_087;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0066
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_088 D R p) from
        (by
          unfold
            nb091_alpha_dummy_088;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0067
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_085 D R) from (by
          unfold
            nb091_alpha_dummy_085;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0064
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_086 D R p) from
        (by
          unfold
            nb091_alpha_dummy_086;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0065
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_081 D R), (nb091_alpha_dummy_084 D R p)),
        ((nb091_alpha_dummy_080 D R), (nb091_alpha_dummy_083 D R p)),
        ((nb091_alpha_dummy_079 D R), (nb091_alpha_dummy_082 D R p)),
        ((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
        ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
        ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
        ((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
        ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
        ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
        ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
        ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
        ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_080 D
        R) ≠ (nb091_alpha_dummy_091 D R) from (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠ (nb091_alpha_dummy_091 D R) from
        (by
          unfold
            nb091_alpha_dummy_091;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0070
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_092 D R p) from
        (by
          unfold
            nb091_alpha_dummy_092;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0071
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_080 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0068
                    D R)
                  0)))) (show (nb091_alpha_dummy_083 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0069
                    D R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_073
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081 D
        R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_081 D
        R) ≠ (nb091_alpha_dummy_093 D R) from (by
          unfold
            nb091_alpha_dummy_093;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0074
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_094 D R p) from
        (by
          unfold
            nb091_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0075
                    D R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_081 D R) ≠
        (nb091_alpha_dummy_089 D R) from (by
          unfold
            nb091_alpha_dummy_089;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0072
                    D R)
                  0)))) (show (nb091_alpha_dummy_084 D R p) ≠ (nb091_alpha_dummy_090 D R p) from
        (by
          unfold
            nb091_alpha_dummy_090;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0073
                    D R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from
                                (by
                                  unfold nb091_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                          0)))) (show (nb091_alpha_dummy_075 D R p) ≠
                                  (nb091_alpha_dummy_078 D R p) from (by
                                  unfold nb091_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                              ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
                              ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
                              ((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
                              ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
                              ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
                              ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
                              ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
                              ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
                              ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                              ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                              ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                              ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                              ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                              ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                              ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                              ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                              ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                              ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                              ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                              ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                              ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                              ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
                                (nb091_alpha_dummy_004 D R p))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from (by
                                unfold nb091_alpha_dummy_077;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0056 D R) 0)))) (show
                              (nb091_alpha_dummy_075 D R p) ≠ (nb091_alpha_dummy_078 D R p) from
                              (by
                                unfold nb091_alpha_dummy_078;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091_alpha_dummy_073 D R) ≠ (nb091_alpha_dummy_077 D R) from
                                (by
                                  unfold nb091_alpha_dummy_077;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0056 D R)
                                          0)))) (show (nb091_alpha_dummy_075 D R p) ≠
                                  (nb091_alpha_dummy_078 D R p) from (by
                                  unfold nb091_alpha_dummy_078;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0057 D R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb091_alpha_dummy_077 D R), (nb091_alpha_dummy_078 D R p)),
                              ((nb091_alpha_dummy_073 D R), (nb091_alpha_dummy_075 D R p)),
                              ((nb091_alpha_dummy_074 D R), (nb091_alpha_dummy_076 D R p)),
                              ((nb091_alpha_dummy_099 D R), (nb091_alpha_dummy_100 D R p)),
                              ((nb091_alpha_dummy_097 D R), (nb091_alpha_dummy_098 D R p)),
                              ((nb091_alpha_dummy_066 D R), (nb091_alpha_dummy_068 D R p)),
                              ((nb091_alpha_dummy_065 D R), (nb091_alpha_dummy_067 D R p)),
                              ((nb091_alpha_dummy_095 D R), (nb091_alpha_dummy_096 D R p)),
                              ((nb091_alpha_dummy_069 D R), (nb091_alpha_dummy_070 D R p)),
                              ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                              ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                              ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                              ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                              ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                              ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                              ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                              ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                              ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                              ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                              ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                              ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                              ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                              ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
                                (nb091_alpha_dummy_004 D R p))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb091_focused_notmem_0028 (D : Class) (R : Class) :
    (nb091_alpha_dummy_103 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0029 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_104 D R p) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb091_focused_notmem_0030 (D : Class) (R : Class) :
    (nb091_alpha_dummy_101 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0031 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_102 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0032 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0033 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0034 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0035 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0036 (D : Class) (R : Class) :
    (nb091_alpha_dummy_063 D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
            ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
              (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
      (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091_alpha_dummy_059 D R))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0037 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_064 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
            ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
              (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
      (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091_alpha_dummy_061 D R p))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0038 (D : Class) (R : Class) :
    (nb091_alpha_dummy_057 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0039 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_058 D R p) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0040 (D : Class) (R : Class) :
    (nb091_alpha_dummy_055 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0041 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_056 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0042 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0043 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0044 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0045 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_focused_notmem_0046 (D : Class) (R : Class) :
    (nb091_alpha_dummy_053 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
          ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091_alpha_dummy_047 D R)
      (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0044 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_048 D R)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0042 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0047 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_054 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
          ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_class_cab (nb091_alpha_dummy_049 D R p)
      (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0045 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_050 D R p)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0043 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0048 (D : Class) (R : Class) :
    (nb091_alpha_dummy_051 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R)
                (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                              (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                              (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                    (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
              (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
            (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))]
  rw [fv_class_cab (nb091_alpha_dummy_047 D R)
      (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0044 D R)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_048 D R)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0042 D R)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0049 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_052 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
                (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                    (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
              (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                  (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                    (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                      (syn_csn (syn_c0c)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl
      (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
          (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
          (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
            (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))]
  rw [fv_class_cab (nb091_alpha_dummy_049 D R p)
      (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb091_focused_notmem_0045 D R p)) (h_eq ▸ hu)
  · rw [fv_syn_wrex (nb091_alpha_dummy_050 D R p)
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
        (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb091_focused_notmem_0043 D R p)) (h_eq ▸ hu)
    · rw [fv_syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
      rw [Finset.mem_union]
      left
      rw [fv_syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb091_focused_notmem_0050 (D : Class) (R : Class) :
    (nb091_alpha_dummy_045 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_chnwcutcode R D
            (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0051 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_046 D R p) ∉ D.fv :=
  by
  change freshVar (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) 0 ∉ D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb091_focused_notmem_0052 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0053 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪
          ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0054 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_focused_notmem_0055 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_chwniso D)).fv ∪
          ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_chwniso D]
  exact hu

theorem nb091_compact_envfresh_0016 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TEnvFresh
      [((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091_alpha_dummy_103 D R) (nb091_alpha_dummy_104 D R p)
      (nb091_focused_notmem_0028 D R) (nb091_focused_notmem_0029 D R p)
      (TEnvFresh.consFresh (nb091_alpha_dummy_101 D R) (nb091_alpha_dummy_102 D R p)
        (nb091_focused_notmem_0030 D R) (nb091_focused_notmem_0031 D R p)
        (TEnvFresh.consFresh (nb091_alpha_dummy_060 D R) (nb091_alpha_dummy_062 D R p)
          (nb091_focused_notmem_0032 D R) (nb091_focused_notmem_0033 D R p)
          (TEnvFresh.consFresh (nb091_alpha_dummy_059 D R) (nb091_alpha_dummy_061 D R p)
            (nb091_focused_notmem_0034 D R) (nb091_focused_notmem_0035 D R p)
            (TEnvFresh.consFresh (nb091_alpha_dummy_063 D R) (nb091_alpha_dummy_064 D R p)
              (nb091_focused_notmem_0036 D R) (nb091_focused_notmem_0037 D R p)
              (TEnvFresh.consFresh (nb091_alpha_dummy_057 D R)
                (nb091_alpha_dummy_058 D R p) (nb091_focused_notmem_0038 D R)
                (nb091_focused_notmem_0039 D R p)
                (TEnvFresh.consFresh (nb091_alpha_dummy_055 D R)
                  (nb091_alpha_dummy_056 D R p) (nb091_focused_notmem_0040 D R)
                  (nb091_focused_notmem_0041 D R p)
                  (TEnvFresh.consFresh (nb091_alpha_dummy_048 D R)
                    (nb091_alpha_dummy_050 D R p) (nb091_focused_notmem_0042 D R)
                    (nb091_focused_notmem_0043 D R p)
                    (TEnvFresh.consFresh (nb091_alpha_dummy_047 D R)
                      (nb091_alpha_dummy_049 D R p) (nb091_focused_notmem_0044 D R)
                      (nb091_focused_notmem_0045 D R p)
                      (TEnvFresh.consFresh (nb091_alpha_dummy_053 D R)
                        (nb091_alpha_dummy_054 D R p) (nb091_focused_notmem_0046 D R)
                        (nb091_focused_notmem_0047 D R p)
                        (TEnvFresh.consFresh (nb091_alpha_dummy_051 D R)
                          (nb091_alpha_dummy_052 D R p) (nb091_focused_notmem_0048 D R)
                          (nb091_focused_notmem_0049 D R p)
                          (TEnvFresh.consFresh (nb091_alpha_dummy_045 D R)
                            (nb091_alpha_dummy_046 D R p) (nb091_focused_notmem_0050 D R)
                            (nb091_focused_notmem_0051 D R p)
                            (TEnvFresh.consFresh (nb091_alpha_dummy_042 D R)
                              (nb091_alpha_dummy_044 D R p) (nb091_focused_notmem_0052 D R)
                              (nb091_focused_notmem_0053 D R p)
                              (TEnvFresh.consFresh (nb091_alpha_dummy_041 D R)
                                (nb091_alpha_dummy_043 D R p) (nb091_focused_notmem_0054 D R)
                                (nb091_focused_notmem_0055 D R p)
                                (TEnvFresh.consFresh (nb091_alpha_dummy_001 D R)
                                  (nb091_alpha_dummy_002 D R p) (nb091_focused_notmem_0000 D R)
                                  (nb091_focused_notmem_0001 D R p)
                                  (TEnvFresh.consFresh (nb091_alpha_dummy_000 D R) p
                                    (nb091_focused_notmem_0002 D R) dv_D_p
                                    (TEnvFresh.consFresh (nb091_alpha_dummy_003 D R)
                                      (nb091_alpha_dummy_004 D R p)
                                      (nb091_focused_notmem_0003 D R)
                                      (nb091_focused_notmem_0004 D R p)
                                      (TEnvFresh.nil D.fv))))))))))))))))))

@[expose]
noncomputable def nb091_focused_refl_0001 (D : Class) (R : Class) (p : Var)
    (dv_D_p : p ∉ D.fv) :
    TReflOn
      [((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      D.fv :=
  TEnvFresh.reflOn (nb091_compact_envfresh_0016 D R p dv_D_p)

theorem nb091_compact_fv_empty_0102 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0103 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0104 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0105 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0106 (D : Class) (R : Class) :
    (nb091_alpha_dummy_103 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0107 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_104 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0108 (D : Class) (R : Class) :
    (nb091_alpha_dummy_101 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0109 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_102 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
