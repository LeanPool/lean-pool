/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Splitting of the first fundamental sequence

For a tower `R → S → T` with `H¹(L_{T⁄S}) = 0` and `Ω[T⁄S]` projective over `T`, the first
fundamental sequence `0 → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0` is split exact.

## Main statements

* `KaehlerDifferential.exists_retraction_mapBaseChange`: the map
  `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` has a `T`-linear retraction.
-/

public section

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct KaehlerDifferential

private lemma mapBaseChange_injective_of_subsingleton [Subsingleton (Algebra.H1Cotangent S T)] :
    Function.Injective (mapBaseChange R S T) :=
  (LinearMap.injective_iff_eq_zero_of_exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)).2
    (Subsingleton.elim _ _)

/-- The first fundamental sequence `0 → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0` is split exact
when `H¹(L_{T⁄S}) = 0` and `Ω[T⁄S]` is projective, e.g. when `T` is a formally smooth `S`-algebra
([Matsumura, Theorem 25.1][matsumura1987]). -/
lemma KaehlerDifferential.exists_retraction_mapBaseChange
    [Subsingleton (Algebra.H1Cotangent S T)] [Module.Projective T Ω[T⁄S]] :
    ∃ l : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R], l ∘ₗ mapBaseChange R S T = LinearMap.id :=
  ((exact_mapBaseChange_map R S T).split_tfae (mapBaseChange_injective_of_subsingleton R S T)
    (map_surjective R S T)).out 1 2 |>.mp <|
    Module.projective_lifting_property _ _ (map_surjective R S T)
