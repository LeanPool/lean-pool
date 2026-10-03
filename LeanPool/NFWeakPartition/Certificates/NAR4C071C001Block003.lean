/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C071C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C071C001Part005`. -/


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
noncomputable def nb071_split_alpha_0005 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)),
        ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_061))
          (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb071_alpha_dummy_061))
            (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_062 x))
          (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb071_alpha_dummy_062 x))
            (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071_alpha_dummy_065) ≠ (nb071_alpha_dummy_069) from
                                        (by
                                          unfold nb071_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0054)
                                                  0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_070 x) from (by
                                          unfold nb071_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0055 x) 0))))
                                      (TAlphaVar.there (show (nb071_alpha_dummy_065) ≠
        (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_069) from
                                        (by
                                          unfold nb071_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0068)
                                                  0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_070 x) from (by
                                          unfold nb071_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0069 x) 0))))
                                      (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠
        (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_065) from (by
          unfold nb071_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_066 x) from (by
          unfold nb071_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_063) from (by
          unfold nb071_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_064 x) from (by
          unfold nb071_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_061) from (by
          unfold nb071_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_062 x) from (by
          unfold nb071_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_059) from (by
          unfold nb071_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_060 x) from (by
          unfold nb071_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_056)
        from (by
          unfold nb071_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_058 x) from (by
          unfold nb071_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_055)
        from (by
          unfold nb071_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_057 x) from (by
          unfold nb071_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb071_alpha_dummy_065) ≠ (nb071_alpha_dummy_069) from
                                        (by
                                          unfold nb071_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0054)
                                                  0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_070 x) from (by
                                          unfold nb071_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0055 x) 0))))
                                      (TAlphaVar.there (show (nb071_alpha_dummy_065) ≠
        (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_069) from
                                        (by
                                          unfold nb071_alpha_dummy_069;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0068)
                                                  0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_070 x) from (by
                                          unfold nb071_alpha_dummy_070;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0069 x) 0))))
                                      (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠
        (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_065) from (by
          unfold nb071_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_066 x) from (by
          unfold nb071_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_063) from (by
          unfold nb071_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_064 x) from (by
          unfold nb071_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_061) from (by
          unfold nb071_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_062 x) from (by
          unfold nb071_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_059) from (by
          unfold nb071_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_060 x) from (by
          unfold nb071_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_056)
        from (by
          unfold nb071_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_058 x) from (by
          unfold nb071_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_055)
        from (by
          unfold nb071_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_057 x) from (by
          unfold nb071_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_closed [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)),
                  ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)),
                  ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)),
                  ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                  ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                  ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                  ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                  ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                  ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                  ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                  ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                  ((nb071_alpha_dummy_000), x),
                  ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                (syn_c1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb071_alpha_dummy_065) ≠
        (nb071_alpha_dummy_069) from (by
          unfold nb071_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0054) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_070 x) from (by
          unfold nb071_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0055 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_065) ≠ (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_069) from (by
          unfold nb071_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0068) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_070 x) from (by
          unfold nb071_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0069 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_065) from (by
          unfold nb071_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_066 x) from (by
          unfold nb071_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_063) from (by
          unfold nb071_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_064 x) from (by
          unfold nb071_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_061) from (by
          unfold nb071_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_062 x) from (by
          unfold nb071_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_059)
        from (by
          unfold nb071_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_060 x) from (by
          unfold nb071_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_056)
        from (by
          unfold nb071_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_058 x) from (by
          unfold nb071_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_055)
        from (by
          unfold nb071_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_057 x) from (by
          unfold nb071_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb071_alpha_dummy_065) ≠
        (nb071_alpha_dummy_069) from (by
          unfold nb071_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0054) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_070 x) from (by
          unfold nb071_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0055 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_065) ≠ (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0052) 0)))) (show (nb071_alpha_dummy_066 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0053 x) 0)))) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_069) from (by
          unfold nb071_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0068) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_070 x) from (by
          unfold nb071_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0069 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_067) from (by
          unfold nb071_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0066) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_068 x) from (by
          unfold nb071_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0067 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_065) from (by
          unfold nb071_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0064) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_066 x) from (by
          unfold nb071_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0065 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_063) from (by
          unfold nb071_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0062) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_064 x) from (by
          unfold nb071_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0063 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_061) from (by
          unfold nb071_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0060) 0)))) (show (nb071_alpha_dummy_044 x) ≠
        (nb071_alpha_dummy_062 x) from (by
          unfold nb071_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0061 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_059)
        from (by
          unfold nb071_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0058)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_060 x) from (by
          unfold nb071_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0059 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_056)
        from (by
          unfold nb071_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  1)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_058 x) from (by
          unfold nb071_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057 x)
                  1)))) (TAlphaVar.there (show (nb071_alpha_dummy_042) ≠ (nb071_alpha_dummy_055)
        from (by
          unfold nb071_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0056)
                  0)))) (show (nb071_alpha_dummy_044 x) ≠ (nb071_alpha_dummy_057 x) from (by
          unfold nb071_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0057
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)),
                    ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)),
                    ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)),
                    ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                    ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                    ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                    ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                    ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                    ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                    ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                    ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                    ((nb071_alpha_dummy_000), x),
                    ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                  (syn_c1c) (by simp only [fv_syn_c1c])))))))))

@[expose]
noncomputable def nb071_split_alpha_0006 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
        ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
        ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
        ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
        ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
        ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
        ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
        ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
        ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
        ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_085))
            (syn_cun (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_088 x))
            (syn_cun (Class.cv (nb071_alpha_dummy_089 x))
              (Class.cv (nb071_alpha_dummy_090 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
          ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
          ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
          ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
          ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
          ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
          ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
          ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
          ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
          ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
          ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
          ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
          ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
          ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
          ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
          ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
          ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x),
          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_097) from (by
                                unfold nb071_alpha_dummy_097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_098 x) from (by
                                unfold nb071_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_097) from (by
                                unfold nb071_alpha_dummy_097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_098 x) from (by
                                unfold nb071_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_099) from (by
                                unfold nb071_alpha_dummy_099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_100 x) from (by
                                unfold nb071_alpha_dummy_100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_099) from (by
                                unfold nb071_alpha_dummy_099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_100 x) from (by
                                unfold nb071_alpha_dummy_100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb071_split_alpha_0007 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
        ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
        ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
        ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
        ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
        ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_079))
          (Class.cv (nb071_alpha_dummy_072))) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_080))
            (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))
              (syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))
              (Class.cv (nb071_alpha_dummy_079))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_081 x))
          (Class.cv (nb071_alpha_dummy_074 x))) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_082 x))
            (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))
              (syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))
              (Class.cv (nb071_alpha_dummy_081 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_079) from (by
              unfold nb071_alpha_dummy_079;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 0))))
          (show (nb071_alpha_dummy_074 x) ≠ (nb071_alpha_dummy_081 x) from (by
              unfold nb071_alpha_dummy_081;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 0))))
          (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_080) from (by
                unfold nb071_alpha_dummy_080;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 1))))
            (show (nb071_alpha_dummy_074 x) ≠ (nb071_alpha_dummy_082 x) from (by
                unfold nb071_alpha_dummy_082;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_072))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_074 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_086) from (by
                                  unfold nb071_alpha_dummy_086;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0080) 1))))
                              (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_089 x) from
                                (by
                                  unfold nb071_alpha_dummy_089;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0081 x) 1))))
                              (TAlphaVar.there
                                (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_085) from (by
                                    unfold nb071_alpha_dummy_085;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0080) 0)))) (show
                                  (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_088 x) from (by
                                    unfold nb071_alpha_dummy_088;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0081 x)
                                            0)))) (TAlphaVar.there
                                  (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from
                                    (by
                                      unfold nb071_alpha_dummy_083;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0078)
                                              0)))) (show
                                    (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from
                                    (by
                                      unfold nb071_alpha_dummy_084;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb071_support_mem_0079 x)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
                                  ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
                                  ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
                                  ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                                  ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                                  ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                                  ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                                  ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                                  ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
                                  ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                                  ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                                  ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                                  ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                                  ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                                  ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                                  ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                                  ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                                  ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                                  ((nb071_alpha_dummy_000), x),
                                  ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb071_split_alpha_0006 x)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from (by
                          unfold nb071_alpha_dummy_083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                      (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                          unfold nb071_alpha_dummy_084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                      ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                      ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                      ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                      ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                      ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
                      ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                      ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                      ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                      ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                      ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                      ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                      ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                      ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                      ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                      ((nb071_alpha_dummy_000), x),
                      ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from
                      (by
                        unfold nb071_alpha_dummy_083;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                    (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                        unfold nb071_alpha_dummy_084;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from (by
                          unfold nb071_alpha_dummy_083;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                      (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                          unfold nb071_alpha_dummy_084;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                      ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                      ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                      ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                      ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                      ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)),
                      ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                      ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                      ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                      ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                      ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                      ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                      ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                      ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                      ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                      ((nb071_alpha_dummy_000), x),
                      ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part006`. -/


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
noncomputable def nb071_split_alpha_0008 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
        ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
        ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
        ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
        ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
        ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
        ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
        ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
        ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
        ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
        ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
        ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_085))
            (syn_cun (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_088 x))
            (syn_cun (Class.cv (nb071_alpha_dummy_089 x))
              (Class.cv (nb071_alpha_dummy_090 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0084) 0))))
                          (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0085 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0082) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0083 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_093) from (by
                              unfold nb071_alpha_dummy_093;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0088) 0))))
                          (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_094 x) from (by
                              unfold nb071_alpha_dummy_094;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0089 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_091) from (by
                                unfold nb071_alpha_dummy_091;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0086) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_092 x) from (by
                                unfold nb071_alpha_dummy_092;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0087 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
          ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
          ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
          ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
          ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
          ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
          ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
          ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
          ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
          ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
          ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
          ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
          ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
          ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
          ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
          ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
          ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
          ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
          ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x),
          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_097) from (by
                                unfold nb071_alpha_dummy_097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_098 x) from (by
                                unfold nb071_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_097) from (by
                                unfold nb071_alpha_dummy_097;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0092) 0))))
                            (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_098 x) from (by
                                unfold nb071_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0093 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0090) 0))))
                              (show (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0091 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_099) from (by
                                unfold nb071_alpha_dummy_099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_100 x) from (by
                                unfold nb071_alpha_dummy_100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_099) from (by
                                unfold nb071_alpha_dummy_099;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0096) 0))))
                            (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_100 x) from (by
                                unfold nb071_alpha_dummy_100;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0097 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_087) ≠ (nb071_alpha_dummy_095) from (by
                                  unfold nb071_alpha_dummy_095;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0094) 0))))
                              (show (nb071_alpha_dummy_090 x) ≠ (nb071_alpha_dummy_096 x) from
                                (by
                                  unfold nb071_alpha_dummy_096;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0095 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb071_split_alpha_0009 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
        ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
        ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
        ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
        ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
        ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
        ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
        ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.classEq (Class.cv (nb071_alpha_dummy_080))
        (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))
          (syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))
          (Class.cv (nb071_alpha_dummy_079))))
      (Wff.classEq (Class.cv (nb071_alpha_dummy_082 x))
        (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))
          (syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))
          (Class.cv (nb071_alpha_dummy_081 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb071_alpha_dummy_072))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb071_alpha_dummy_074 x))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_086) from (by
                              unfold nb071_alpha_dummy_086;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0080) 1))))
                          (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_089 x) from (by
                              unfold nb071_alpha_dummy_089;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0081 x) 1))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_085) from (by
                                unfold nb071_alpha_dummy_085;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0080) 0))))
                            (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_088 x) from (by
                                unfold nb071_alpha_dummy_088;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0081 x) 0))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from (by
                                  unfold nb071_alpha_dummy_083;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                              (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from
                                (by
                                  unfold nb071_alpha_dummy_084;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)),
                              ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)),
                              ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)),
                              ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                              ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                              ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                              ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
                              ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
                              ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                              ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                              ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
                              ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                              ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                              ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                              ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                              ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                              ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                              ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                              ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                              ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                              ((nb071_alpha_dummy_000), x),
                              ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb071_split_alpha_0008 x)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from (by
                      unfold nb071_alpha_dummy_083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                  (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                      unfold nb071_alpha_dummy_084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                  ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                  ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                  ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
                  ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
                  ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                  ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                  ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
                  ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                  ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                  ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                  ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                  ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                  ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                  ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                  ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                  ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                  ((nb071_alpha_dummy_000), x),
                  ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from (by
                    unfold nb071_alpha_dummy_083;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                    unfold nb071_alpha_dummy_084;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_083) from
                    (by
                      unfold nb071_alpha_dummy_083;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0))))
                  (show (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_084 x) from (by
                      unfold nb071_alpha_dummy_084;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)),
                  ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)),
                  ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)),
                  ((nb071_alpha_dummy_105), (nb071_alpha_dummy_106 x)),
                  ((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
                  ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                  ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                  ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
                  ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                  ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                  ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                  ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                  ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                  ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                  ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                  ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                  ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                  ((nb071_alpha_dummy_000), x),
                  ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb071_split_alpha_0010 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
        ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
        ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_101))
          (Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb071_alpha_dummy_101))
            (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_102 x))
          (Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb071_alpha_dummy_102 x))
            (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_072) from
                    (by
                      unfold nb071_alpha_dummy_072;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
                  (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_074 x) from (by
                      unfold nb071_alpha_dummy_074;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
                  (TAlphaVar.there (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_071) from
                      (by
                        unfold nb071_alpha_dummy_071;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
                    (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_073 x) from (by
                        unfold nb071_alpha_dummy_073;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0100 x) 0)))) (TAlphaVar.there
                      (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_101) from (by
                          unfold nb071_alpha_dummy_101;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0102) 0))))
                      (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_102 x) from (by
                          unfold nb071_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0103 x) 0))))
                      (TAlphaVar.there
                        (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_075) from (by
                            unfold nb071_alpha_dummy_075;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0099) 0))))
                        (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_076 x) from (by
                            unfold nb071_alpha_dummy_076;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0101 x) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                  (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv)
                            (by decide)) (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                  (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb071_alpha_dummy_056))).fv ∪
                      ((Class.cv (nb071_alpha_dummy_055))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪
                      ((Class.cv (nb071_alpha_dummy_057 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠
        (nb071_alpha_dummy_079) from (by
          unfold nb071_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_081 x) from (by
          unfold nb071_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_080) from (by
          unfold nb071_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_082 x) from (by
          unfold nb071_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_105) from (by
          unfold nb071_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_106 x) from (by
          unfold nb071_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_103) from (by
          unfold nb071_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_104 x) from (by
          unfold nb071_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071_split_alpha_0009 x)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠
        (nb071_alpha_dummy_079) from (by
          unfold nb071_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_081 x) from (by
          unfold nb071_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_080) from (by
          unfold nb071_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_082 x) from (by
          unfold nb071_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_105) from (by
          unfold nb071_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_106 x) from (by
          unfold nb071_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_103) from (by
          unfold nb071_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_104 x) from (by
          unfold nb071_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071_split_alpha_0009 x)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
                          ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                          ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                          ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
                          ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                          ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                          ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                          ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                          ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                          ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                          ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                          ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                          ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                          ((nb071_alpha_dummy_000), x),
                          ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_072) from
                      (by
                        unfold nb071_alpha_dummy_072;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
                    (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_074 x) from (by
                        unfold nb071_alpha_dummy_074;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0100 x) 1)))) (TAlphaVar.there
                      (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_071) from (by
                          unfold nb071_alpha_dummy_071;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0098) 0))))
                      (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_073 x) from (by
                          unfold nb071_alpha_dummy_073;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
                      (TAlphaVar.there
                        (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_101) from (by
                            unfold nb071_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0102) 0))))
                        (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_102 x) from (by
                            unfold nb071_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0103 x) 0))))
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_075) from (by
                              unfold nb071_alpha_dummy_075;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0099) 0))))
                          (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_076 x) from (by
                              unfold nb071_alpha_dummy_076;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0101 x) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                    (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv)
                              (by decide)) (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn
                                    (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb071_alpha_dummy_056))).fv ∪
                        ((Class.cv (nb071_alpha_dummy_055))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪
                        ((Class.cv (nb071_alpha_dummy_057 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_079) from (by
          unfold nb071_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_081 x) from (by
          unfold nb071_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_080) from (by
          unfold nb071_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_082 x) from (by
          unfold nb071_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_105) from (by
          unfold nb071_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_106 x) from (by
          unfold nb071_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_103)
        from (by
          unfold nb071_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104)
                  0)))) (show (nb071_alpha_dummy_074 x) ≠ (nb071_alpha_dummy_104 x) from (by
          unfold nb071_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071_split_alpha_0009 x)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_079) from (by
          unfold nb071_alpha_dummy_079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_081 x) from (by
          unfold nb071_alpha_dummy_081;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_080) from (by
          unfold nb071_alpha_dummy_080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0076) 1)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_082 x) from (by
          unfold nb071_alpha_dummy_082;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0077 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_105) from (by
          unfold nb071_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0106) 0)))) (show (nb071_alpha_dummy_074 x) ≠
        (nb071_alpha_dummy_106 x) from (by
          unfold nb071_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0107 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_072) ≠ (nb071_alpha_dummy_103)
        from (by
          unfold nb071_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0104)
                  0)))) (show (nb071_alpha_dummy_074 x) ≠ (nb071_alpha_dummy_104 x) from (by
          unfold nb071_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0105 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb071_split_alpha_0009 x)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb071_alpha_dummy_103), (nb071_alpha_dummy_104 x)),
                            ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)),
                            ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)),
                            ((nb071_alpha_dummy_101), (nb071_alpha_dummy_102 x)),
                            ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)),
                            ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                            ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                            ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                            ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                            ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                            ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                            ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                            ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                            ((nb071_alpha_dummy_000), x),
                            ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb071_wpp_notmem_0264 : (nb071_alpha_dummy_056) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_056, fv_syn_cen] using (nb071_compact_fv_empty_0046)

theorem nb071_wpp_notmem_0265 (x : Var) : (nb071_alpha_dummy_058 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_058, fv_syn_cen] using (nb071_compact_fv_empty_0047 x)

theorem nb071_wpp_notmem_0266 : (nb071_alpha_dummy_055) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_055, fv_syn_cen] using (nb071_compact_fv_empty_0048)

theorem nb071_wpp_notmem_0267 (x : Var) : (nb071_alpha_dummy_057 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_057, fv_syn_cen] using (nb071_compact_fv_empty_0049 x)

theorem nb071_wpp_notmem_0268 : (nb071_alpha_dummy_042) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_042, fv_syn_cen] using (nb071_compact_fv_empty_0050)

theorem nb071_wpp_notmem_0269 (x : Var) : (nb071_alpha_dummy_044 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_044, fv_syn_cen] using (nb071_compact_fv_empty_0051 x)

theorem nb071_wpp_notmem_0270 : (nb071_alpha_dummy_041) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_cen] using (nb071_compact_fv_empty_0032)

theorem nb071_wpp_notmem_0271 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_043, fv_syn_cen] using (nb071_compact_fv_empty_0033 x)

theorem nb071_wpp_notmem_0272 : (nb071_alpha_dummy_045) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_cen] using (nb071_compact_fv_empty_0034)

theorem nb071_wpp_notmem_0273 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_046, fv_syn_cen] using (nb071_compact_fv_empty_0035 x)

theorem nb071_wpp_notmem_0274 : (nb071_alpha_dummy_048) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_cen] using (nb071_compact_fv_empty_0036)

theorem nb071_wpp_notmem_0275 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_050, fv_syn_cen] using (nb071_compact_fv_empty_0037 x)

theorem nb071_wpp_notmem_0276 : (nb071_alpha_dummy_047) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_cen] using (nb071_compact_fv_empty_0038)

theorem nb071_wpp_notmem_0277 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_049, fv_syn_cen] using (nb071_compact_fv_empty_0039 x)

theorem nb071_wpp_notmem_0278 : (nb071_alpha_dummy_001) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_001, fv_syn_cen] using (nb071_compact_fv_empty_0020)

theorem nb071_wpp_notmem_0279 (x : Var) : (nb071_alpha_dummy_002 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_002, fv_syn_cen] using (nb071_compact_fv_empty_0021 x)

theorem nb071_wpp_notmem_0280 : (nb071_alpha_dummy_000) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_000, fv_syn_cen] using (nb071_compact_fv_empty_0022)

theorem nb071_wpp_notmem_0281 (x : Var) : x ∉ ((syn_cen)).fv := by
  simpa only [fv_syn_cen] using (nb071_compact_fv_empty_0023 x)

theorem nb071_wpp_notmem_0282 : (nb071_alpha_dummy_003) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_003, fv_syn_cen] using (nb071_compact_fv_empty_0024)

theorem nb071_wpp_notmem_0283 (x : Var) : (nb071_alpha_dummy_004 x) ∉ ((syn_cen)).fv := by
  simpa only [nb071_alpha_dummy_004, fv_syn_cen] using (nb071_compact_fv_empty_0025 x)

theorem nb071_compact_envfresh_0017 (x : Var) :
    TEnvFresh
      [((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      ((syn_cen)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb071_alpha_dummy_056) (nb071_alpha_dummy_058 x)
      (nb071_wpp_notmem_0264) (nb071_wpp_notmem_0265 x)
      (TEnvFresh.consFresh (nb071_alpha_dummy_055) (nb071_alpha_dummy_057 x)
        (nb071_wpp_notmem_0266) (nb071_wpp_notmem_0267 x)
        (TEnvFresh.consFresh (nb071_alpha_dummy_042) (nb071_alpha_dummy_044 x)
          (nb071_wpp_notmem_0268) (nb071_wpp_notmem_0269 x)
          (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x)
            (nb071_wpp_notmem_0270) (nb071_wpp_notmem_0271 x)
            (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x)
              (nb071_wpp_notmem_0272) (nb071_wpp_notmem_0273 x)
              (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x)
                (nb071_wpp_notmem_0274) (nb071_wpp_notmem_0275 x)
                (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x)
                  (nb071_wpp_notmem_0276) (nb071_wpp_notmem_0277 x)
                  (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x)
                    (nb071_wpp_notmem_0278) (nb071_wpp_notmem_0279 x)
                    (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0280)
                      (nb071_wpp_notmem_0281 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003)
                        (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0282)
                        (nb071_wpp_notmem_0283 x) (TEnvFresh.nil ((syn_cen)).fv)))))))))))

@[expose]
noncomputable def nb071_wpp_refl_0017 (x : Var) :
    TReflOn
      [((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
        ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
        ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      ((syn_cen)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0017 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
