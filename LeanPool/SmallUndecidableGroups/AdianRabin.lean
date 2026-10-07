/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.Family
public import LeanPool.SmallUndecidableGroups.AdianRabin.Gordon.Family

/-!
# Two explicit Adian--Rabin constructions

This file is the statement-level interface for the two constructions
formalized in this project.  The Miller--Tancer construction is generic in
the number of generators and relators, subject to the normal-weight-one
hypothesis.  Gordon's Lemma 2.1 is generic in the host presentation and its
abelian-order data.
-/

@[expose] public section

namespace Undecidability.AdianRabin

/-- The compressed Miller--Tancer construction produces an Adian--Rabin
family with one additional generator and two additional relators when the
normal generator is a displayed presentation generator. -/
theorem exists_miller_tancer_family
    (P : FP n m) (k : Fin n)
    (hP : ¬ ComputablePred P.wordProblem)
    (hk : P.NormallyGenerates (Word.generator k)) :
    ∃ A : ℕ → FP (n + 1) (m + 2),
      FP.IsAdianRabinFamily A :=
  ⟨MillerTancer.Compressed.family P k,
    MillerTancer.Compressed.family_isAdianRabin P k hP hk⟩

/-- Gordon's Lemma 2.1 produces a two-generator Adian--Rabin family with
one more relator than the host presentation. -/
theorem exists_gordon_family
    (P : FP n m) (condition : Gordon.Condition21 P)
    (hP : ¬ ComputablePred P.wordProblem) :
    ∃ A : ℕ → FP 2 (m + 1),
      FP.IsAdianRabinFamily A :=
  Gordon.lemma_2_1 P condition hP

end Undecidability.AdianRabin
