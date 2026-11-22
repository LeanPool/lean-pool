/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Summands and isomorphisms in the additive envelope `Mat_ 𝒞`

An object of `Mat_ 𝒞` is the direct sum of its entries, so it is determined up to isomorphism by
its entries up to reindexing: it is isomorphic to its reindexing along a bijection, to any
object with entrywise equal entries, and, with a single index, to the single object given by
its entry.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]

/-- The summand of a `Mat_` object on the indices satisfying `p`. -/
def subObj (M : Mat_ 𝒞) (p : M.ι → Bool) : Mat_ 𝒞 where
  ι := {i : M.ι // p i}
  X i := M.X i.1

open Classical in
/-- The inclusion of a summand. -/
noncomputable def subIncl (M : Mat_ 𝒞) (p : M.ι → Bool) : subObj M p ⟶ M :=
  fun i j => if h : i.1 = j then eqToHom (congrArg M.X h) else 0

open Classical in
/-- The projection onto a summand. -/
noncomputable def subProj (M : Mat_ 𝒞) (p : M.ι → Bool) : M ⟶ subObj M p :=
  fun i j => if h : i = j.1 then eqToHom (congrArg M.X h) else 0

/-- Objects of `Mat_ 𝒞` with entrywise equal entries along a bijection of indices are
isomorphic. -/
noncomputable def Mat_.isoOfEntries (M N : Mat_ 𝒞) (e : M.ι ≃ N.ι)
    (h : ∀ i, M.X i = N.X (e i)) : M ≅ N :=
  Mat_.isoBiproductEmbedding M ≪≫
    biproduct.whiskerEquiv e (fun i => eqToIso (congrArg (Mat_.embedding 𝒞).obj (h i)).symm) ≪≫
    (Mat_.isoBiproductEmbedding N).symm

/-- Every object of `Mat_ 𝒞` is isomorphic to one indexed by `Fin n`. -/
noncomputable def Mat_.isoReindex (M : Mat_ 𝒞) {n : ℕ} (e : M.ι ≃ Fin n) :
    M ≅ (⟨Fin n, fun j => M.X (e.symm j)⟩ : Mat_ 𝒞) :=
  Mat_.isoOfEntries M _ e fun i => by simp

/-- A `Mat_` object with a single index is the corresponding single object. -/
noncomputable def Mat_.isoSingleOfUnique (M : Mat_ 𝒞) [Unique M.ι] :
    M ≅ (Mat_.embedding 𝒞).obj (M.X default) :=
  Mat_.isoBiproductEmbedding M ≪≫ biproductUniqueIso _

end ExtriangulatedRealization
