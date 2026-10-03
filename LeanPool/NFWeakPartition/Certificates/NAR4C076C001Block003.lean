/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part008`. -/


section

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
noncomputable def nb076_split_alpha_0002 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_m_n : m ≠ n) :
    TAlphaWff
      [((nb076_alpha_dummy_015), (nb076_alpha_dummy_016 g m n a b)),
        ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_015))
          (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_015)) (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (syn_cop (Class.cv (nb076_alpha_dummy_003))
                  (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_016 g m n a b))
          (Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076_alpha_dummy_016 g m n a b))
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg
                          (TAlphaWff.neg (nb076_split_alpha_0000 g m n a b dv_m_n)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠
        (nb076_alpha_dummy_018) from (by
          unfold nb076_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076_alpha_dummy_020 m n) from (by
          unfold nb076_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 0)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_047) from (by
          unfold nb076_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076_alpha_dummy_048 m n) from (by
          unfold nb076_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_021)
        from (by
          unfold nb076_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051) 0)))) (show n ≠ (nb076_alpha_dummy_022 m n) from (by
          unfold nb076_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010)
        from (by
          unfold nb076_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
          unfold nb076_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g m
                    n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009)
        from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_015)
        from (by
          unfold nb076_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076_alpha_dummy_016 g m n a b) from (by
          unfold nb076_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_013)
        from (by
          unfold nb076_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076_alpha_dummy_014 g m n a b) from (by
          unfold nb076_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005)
        from (by
          unfold
            nb076_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
          unfold
            nb076_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv)
        (by decide)) (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076_split_alpha_0001 g m n a b)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠
        (nb076_alpha_dummy_018) from (by
          unfold nb076_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076_alpha_dummy_020 m n) from (by
          unfold nb076_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 0)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_047) from (by
          unfold nb076_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076_alpha_dummy_048 m n) from (by
          unfold nb076_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_021)
        from (by
          unfold nb076_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051) 0)))) (show n ≠ (nb076_alpha_dummy_022 m n) from (by
          unfold nb076_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010)
        from (by
          unfold nb076_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
          unfold nb076_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g m
                    n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009)
        from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_015)
        from (by
          unfold nb076_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076_alpha_dummy_016 g m n a b) from (by
          unfold nb076_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_013)
        from (by
          unfold nb076_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076_alpha_dummy_014 g m n a b) from (by
          unfold nb076_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005)
        from (by
          unfold
            nb076_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
          unfold
            nb076_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv)
        (by decide)) (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076_split_alpha_0001 g m n a b))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((syn_cop (Class.cv (nb076_alpha_dummy_003))
                          (Class.cv (nb076_alpha_dummy_004)))).fv ∪
                      ((Class.cv (nb076_alpha_dummy_005))).fv) (by decide)) (freshVar_injective
                    (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
                      ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_053) from (by
                              unfold nb076_alpha_dummy_053;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0060) 0)))) (show
                            (nb076_alpha_dummy_012 g m n a b) ≠
                              (nb076_alpha_dummy_055 g m n a b) from (by
                              unfold nb076_alpha_dummy_055;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                      0)))) (TAlphaVar.there
                            (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_054) from (by
                                unfold nb076_alpha_dummy_054;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0060) 1)))) (show
                              (nb076_alpha_dummy_012 g m n a b) ≠
                                (nb076_alpha_dummy_056 g m n a b) from (by
                                unfold nb076_alpha_dummy_056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_060) from (by
          unfold nb076_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 1)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_063 g m n a b) from (by
          unfold nb076_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_059)
        from (by
          unfold nb076_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_062 g m n a b) from (by
          unfold nb076_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_067)
        from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_067)
        from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_071)
        from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from (by
                                        unfold nb076_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
                                        (nb076_alpha_dummy_058 g m n a b) from (by
                                        unfold nb076_alpha_dummy_058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)),
                                    ((nb076_alpha_dummy_053),
                                      (nb076_alpha_dummy_055 g m n a b)),
                                    ((nb076_alpha_dummy_054),
                                      (nb076_alpha_dummy_056 g m n a b)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from
                                    (by
                                      unfold nb076_alpha_dummy_057;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0062)
                                              0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
                                      (nb076_alpha_dummy_058 g m n a b) from (by
                                      unfold nb076_alpha_dummy_058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0063 g m n a b) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from (by
                                        unfold nb076_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
                                        (nb076_alpha_dummy_058 g m n a b) from (by
                                        unfold nb076_alpha_dummy_058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)),
                                    ((nb076_alpha_dummy_053),
                                      (nb076_alpha_dummy_055 g m n a b)),
                                    ((nb076_alpha_dummy_054),
                                      (nb076_alpha_dummy_056 g m n a b)),
                                    ((nb076_alpha_dummy_010),
                                      (nb076_alpha_dummy_012 g m n a b)),
                                    ((nb076_alpha_dummy_009),
                                      (nb076_alpha_dummy_011 g m n a b)),
                                    ((nb076_alpha_dummy_015),
                                      (nb076_alpha_dummy_016 g m n a b)),
                                    ((nb076_alpha_dummy_013),
                                      (nb076_alpha_dummy_014 g m n a b)),
                                    ((nb076_alpha_dummy_005),
                                      (nb076_alpha_dummy_006 g m n a b)),
                                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                                    ((nb076_alpha_dummy_007),
                                      (nb076_alpha_dummy_008 g m n a b))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb076_split_alpha_0000 g m n a b dv_m_n)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_018) from (by
          unfold nb076_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076_alpha_dummy_020 m n) from (by
          unfold nb076_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_047)
        from (by
          unfold nb076_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076_alpha_dummy_048 m n) from (by
          unfold nb076_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_021)
        from (by
          unfold nb076_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051)
                  0)))) (show n ≠ (nb076_alpha_dummy_022 m n) from (by
          unfold nb076_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010)
        from (by
          unfold nb076_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
          unfold nb076_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009)
        from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_015)
        from (by
          unfold nb076_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076_alpha_dummy_016 g m n a b) from (by
          unfold nb076_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_013)
        from (by
          unfold
            nb076_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076_alpha_dummy_014 g m n a b) from (by
          unfold
            nb076_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005)
        from (by
          unfold
            nb076_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
          unfold
            nb076_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_003))).fv ∪
        ((Class.cv (nb076_alpha_dummy_004))).fv) (by decide)) (freshVar_injective
        (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076_split_alpha_0001 g m n a b)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_018) from (by
          unfold nb076_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076_alpha_dummy_020 m n) from (by
          unfold nb076_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_047)
        from (by
          unfold nb076_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076_alpha_dummy_048 m n) from (by
          unfold nb076_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_021)
        from (by
          unfold nb076_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051)
                  0)))) (show n ≠ (nb076_alpha_dummy_022 m n) from (by
          unfold nb076_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010)
        from (by
          unfold nb076_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
          unfold nb076_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009)
        from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_015)
        from (by
          unfold nb076_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076_alpha_dummy_016 g m n a b) from (by
          unfold nb076_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_013)
        from (by
          unfold
            nb076_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076_alpha_dummy_014 g m n a b) from (by
          unfold
            nb076_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_005)
        from (by
          unfold
            nb076_alpha_dummy_005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076_alpha_dummy_006 g m n a b) from (by
          unfold
            nb076_alpha_dummy_006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_003))).fv ∪
        ((Class.cv (nb076_alpha_dummy_004))).fv) (by decide)) (freshVar_injective
        (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076_split_alpha_0001 g m n a b))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((syn_cop (Class.cv (nb076_alpha_dummy_003))
                            (Class.cv (nb076_alpha_dummy_004)))).fv ∪
                        ((Class.cv (nb076_alpha_dummy_005))).fv) (by decide))
                    (freshVar_injective (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
                        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_053) from (by
                                unfold nb076_alpha_dummy_053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0060) 0)))) (show
                              (nb076_alpha_dummy_012 g m n a b) ≠
                                (nb076_alpha_dummy_055 g m n a b) from (by
                                unfold nb076_alpha_dummy_055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_054) from (by
                                  unfold nb076_alpha_dummy_054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0060) 1)))) (show
                                (nb076_alpha_dummy_012 g m n a b) ≠
                                  (nb076_alpha_dummy_056 g m n a b) from (by
                                  unfold nb076_alpha_dummy_056;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0061 g m n a b) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_060) from (by
          unfold nb076_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 1)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_063 g m n a b) from (by
          unfold nb076_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a
                    b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_059)
        from (by
          unfold nb076_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_062 g m n a b) from (by
          unfold nb076_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n
                    a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m
                    n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_067)
        from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_067)
        from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_015),
        (nb076_alpha_dummy_016 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_071)
        from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070
        g m n a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from
                                        (by
                                          unfold nb076_alpha_dummy_057;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0062)
                                                  0)))) (show
                                        (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
                                          unfold nb076_alpha_dummy_058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0063 g m n a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_057),
                                        (nb076_alpha_dummy_058 g m n a b)),
                                      ((nb076_alpha_dummy_053),
                                        (nb076_alpha_dummy_055 g m n a b)),
                                      ((nb076_alpha_dummy_054),
                                        (nb076_alpha_dummy_056 g m n a b)),
                                      ((nb076_alpha_dummy_010),
                                        (nb076_alpha_dummy_012 g m n a b)),
                                      ((nb076_alpha_dummy_009),
                                        (nb076_alpha_dummy_011 g m n a b)),
                                      ((nb076_alpha_dummy_015),
                                        (nb076_alpha_dummy_016 g m n a b)),
                                      ((nb076_alpha_dummy_013),
                                        (nb076_alpha_dummy_014 g m n a b)),
                                      ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from (by
                                        unfold nb076_alpha_dummy_057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
                                        (nb076_alpha_dummy_058 g m n a b) from (by
                                        unfold nb076_alpha_dummy_058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from
                                        (by
                                          unfold nb076_alpha_dummy_057;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0062)
                                                  0)))) (show
                                        (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
                                          unfold nb076_alpha_dummy_058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0063 g m n a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb076_alpha_dummy_057),
                                        (nb076_alpha_dummy_058 g m n a b)),
                                      ((nb076_alpha_dummy_053),
                                        (nb076_alpha_dummy_055 g m n a b)),
                                      ((nb076_alpha_dummy_054),
                                        (nb076_alpha_dummy_056 g m n a b)),
                                      ((nb076_alpha_dummy_010),
                                        (nb076_alpha_dummy_012 g m n a b)),
                                      ((nb076_alpha_dummy_009),
                                        (nb076_alpha_dummy_011 g m n a b)),
                                      ((nb076_alpha_dummy_015),
                                        (nb076_alpha_dummy_016 g m n a b)),
                                      ((nb076_alpha_dummy_013),
                                        (nb076_alpha_dummy_014 g m n a b)),
                                      ((nb076_alpha_dummy_005),
                                        (nb076_alpha_dummy_006 g m n a b)),
                                      ((nb076_alpha_dummy_004), n),
                                      ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
                                        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part009`. -/


section

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
noncomputable def nb076_split_alpha_0003 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)),
        ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)),
        ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)),
        ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
        ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_010))
          (Class.cv (nb076_alpha_dummy_005))) (Wff.neg
          (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
            (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_012 g m n a b))
          (Class.cv (nb076_alpha_dummy_006 g m n a b))) (Wff.neg
          (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
            (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_010) from (by
              unfold nb076_alpha_dummy_010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
          (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_012 g m n a b) from (by
              unfold nb076_alpha_dummy_012;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
          (TAlphaVar.there (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_009) from (by
                unfold nb076_alpha_dummy_009;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
            (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_011 g m n a b) from (by
                unfold nb076_alpha_dummy_011;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0)))) (TAlphaVar.there
              (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_075) from (by
                  unfold nb076_alpha_dummy_075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0086) 0))))
              (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_076 g m n a b) from
                (by
                  unfold nb076_alpha_dummy_076;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb076_support_mem_0087 g m n a b) 0))))
              (TAlphaVar.there (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_013) from (by
                    unfold nb076_alpha_dummy_013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0083) 0)))) (show
                  (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_014 g m n a b) from (by
                    unfold nb076_alpha_dummy_014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb076_support_mem_0085 g m n a b) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb076_alpha_dummy_003))
                    (Class.cv (nb076_alpha_dummy_004)))).fv ∪
                ((Class.cv (nb076_alpha_dummy_005))).fv) (by decide)) (freshVar_injective
              (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
                ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_053) from (by
                                        unfold nb076_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0060)
                                                0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
                                        (nb076_alpha_dummy_055 g m n a b) from (by
                                        unfold nb076_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0061 g m n a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_054) from
                                        (by
                                          unfold nb076_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0060)
                                                  1)))) (show
                                        (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_056 g m n a b) from (by
                                          unfold nb076_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0061 g m n a b) 1))))
                                      (TAlphaVar.there (show (nb076_alpha_dummy_010) ≠
        (nb076_alpha_dummy_079) from (by
          unfold nb076_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0090) 0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_080 g m n a b) from (by
          unfold nb076_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0091 g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_077)
        from (by
          unfold nb076_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0088) 0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_078 g m n a b) from (by
          unfold nb076_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0089 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb076_alpha_dummy_010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_060) from (by
          unfold nb076_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  1)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_063 g m n a
        b) from (by
          unfold nb076_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_059)
        from (by
          unfold nb076_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_062 g m n a
        b) from (by
          unfold nb076_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold
            nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_058 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n
        a b))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055
        g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_053) from (by
                                        unfold nb076_alpha_dummy_053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0060)
                                                0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
                                        (nb076_alpha_dummy_055 g m n a b) from (by
                                        unfold nb076_alpha_dummy_055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0061 g m n a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_054) from
                                        (by
                                          unfold nb076_alpha_dummy_054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0060)
                                                  1)))) (show
                                        (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_056 g m n a b) from (by
                                          unfold nb076_alpha_dummy_056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0061 g m n a b) 1))))
                                      (TAlphaVar.there (show (nb076_alpha_dummy_010) ≠
        (nb076_alpha_dummy_079) from (by
          unfold nb076_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0090) 0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_080 g m n a b) from (by
          unfold nb076_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0091 g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_010) ≠ (nb076_alpha_dummy_077)
        from (by
          unfold nb076_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0088) 0)))) (show (nb076_alpha_dummy_012 g m n a b) ≠
        (nb076_alpha_dummy_078 g m n a b) from (by
          unfold nb076_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0089 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb076_alpha_dummy_010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_060) from (by
          unfold nb076_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  1)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_063 g m n a
        b) from (by
          unfold nb076_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  1)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_059)
        from (by
          unfold nb076_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_062 g m n a
        b) from (by
          unfold nb076_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold
            nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_058 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a
        b))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_067) from (by
          unfold
            nb076_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_068 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_065)
        from (by
          unfold
            nb076_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_066 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_061), (nb076_alpha_dummy_064 g m n a b)), ((nb076_alpha_dummy_060),
        (nb076_alpha_dummy_063 g m n a b)), ((nb076_alpha_dummy_059),
        (nb076_alpha_dummy_062 g m n a b)), ((nb076_alpha_dummy_057),
        (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n
        a b))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055
        g m n a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠
        (nb076_alpha_dummy_071) from (by
          unfold
            nb076_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_072 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠
        (nb076_alpha_dummy_073) from (by
          unfold
            nb076_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_074 g m n a
        b) from (by
          unfold
            nb076_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076_alpha_dummy_061) ≠ (nb076_alpha_dummy_069)
        from (by
          unfold
            nb076_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076_alpha_dummy_064 g m n a b) ≠ (nb076_alpha_dummy_070 g m n
        a b) from (by
          unfold
            nb076_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057) from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_057)
        from (by
          unfold nb076_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076_alpha_dummy_055 g m n a b) ≠
        (nb076_alpha_dummy_058 g m n a b) from (by
          unfold nb076_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb076_alpha_dummy_057), (nb076_alpha_dummy_058 g m n a b)), ((nb076_alpha_dummy_053),
        (nb076_alpha_dummy_055 g m n a b)), ((nb076_alpha_dummy_054),
        (nb076_alpha_dummy_056 g m n a b)), ((nb076_alpha_dummy_079),
        (nb076_alpha_dummy_080 g m n a b)), ((nb076_alpha_dummy_077),
        (nb076_alpha_dummy_078 g m n a b)), ((nb076_alpha_dummy_010),
        (nb076_alpha_dummy_012 g m n a b)), ((nb076_alpha_dummy_009),
        (nb076_alpha_dummy_011 g m n a b)), ((nb076_alpha_dummy_075),
        (nb076_alpha_dummy_076 g m n a b)), ((nb076_alpha_dummy_013),
        (nb076_alpha_dummy_014 g m n a b)), ((nb076_alpha_dummy_005),
        (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n),
        ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007),
        (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb076_alpha_dummy_077), (nb076_alpha_dummy_078 g m n a b)),
                    ((nb076_alpha_dummy_010), (nb076_alpha_dummy_012 g m n a b)),
                    ((nb076_alpha_dummy_009), (nb076_alpha_dummy_011 g m n a b)),
                    ((nb076_alpha_dummy_075), (nb076_alpha_dummy_076 g m n a b)),
                    ((nb076_alpha_dummy_013), (nb076_alpha_dummy_014 g m n a b)),
                    ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
                    ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
                    ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb076_wpp_notmem_0198 : (nb076_alpha_dummy_005) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_005, fv_syn_cncs] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0199 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_006, fv_syn_cncs] using
    (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0200 : (nb076_alpha_dummy_004) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_004, fv_syn_cncs] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0201 (n : Var) : n ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0202 : (nb076_alpha_dummy_003) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_003, fv_syn_cncs] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0203 (m : Var) : m ∉ ((syn_cncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0204 : (nb076_alpha_dummy_007) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_007, fv_syn_cncs] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0205 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_008 g m n a b) ∉ ((syn_cncs)).fv := by
  simpa only [nb076_alpha_dummy_008, fv_syn_cncs] using
    (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TEnvFresh
      [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      ((syn_cncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b)
      (nb076_wpp_notmem_0198) (nb076_wpp_notmem_0199 g m n a b)
      (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0200)
        (nb076_wpp_notmem_0201 n)
        (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0202)
          (nb076_wpp_notmem_0203 m)
          (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b)
            (nb076_wpp_notmem_0204) (nb076_wpp_notmem_0205 g m n a b)
            (TEnvFresh.nil ((syn_cncs)).fv)))))

@[expose]
noncomputable def nb076_wpp_refl_0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TReflOn
      [((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)),
        ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m),
        ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))]
      ((syn_cncs)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0014 g m n a b)

theorem nb076_compact_fv_empty_0080 : (nb076_alpha_dummy_002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0081 (g : Var) : g ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0082 : (nb076_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0083 (b : Var) : b ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0084 : (nb076_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0085 (a : Var) : a ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
