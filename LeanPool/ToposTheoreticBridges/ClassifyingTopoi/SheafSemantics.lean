/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.LocallyFiltering
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.PullbackElements
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.InverseImage
public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Presheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local Kripke–Joyal semantics in sheaf topoi

Let `M` be a structure in a sheaf topos `Sh(D, K)` and `P` the underlying structure in presheaves,
with fiber structures on the sections `P(d)`. If `M` is a model of a sequent `φ ⊢ ψ`, every tuple
of sections at `d` satisfying `φ` in the fiber satisfies `ψ` locally: after restriction along the
morphisms of a `K`-covering sieve of `d`
(`LeanPool.ClassifyingTopoi.CatStructure.IsModel.locally_realize`). Sheafification `a` maps the
interpretations in `P` to those in `M` (`CatStructure.interp_map`), and a factorization of
`a(m)` through `a(n)`, for a monomorphism `n`, is a local factorization of `m` through `n`
(`LeanPool.ClassifyingTopoi.locally_exists_app_eq_of_factorization`).

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VI.7 (Kripke–Joyal semantics for
  sheaves).
* P. T. Johnstone, *Sketches of an Elephant*, D1.2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite GrothendieckTopology

namespace LeanPool.ClassifyingTopoi

attribute [local instance high] Sheaf.instHasColimitsOfShape

/-- In a pullback square whose right side `g` is a monomorphism and whose bottom side `f` factors
through `g`, the left side is an isomorphism. -/
theorem isIso_fst_of_isPullback_of_factors {𝒞 : Type*} [Category 𝒞] {P X Y Z : 𝒞}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Mono g]
    (k : X ⟶ Y) (hk : k ≫ g = f) : IsIso fst := by
  refine ⟨h.lift (𝟙 _) k (by simp [hk]), h.hom_ext ?_ ?_, h.lift_fst _ _ _⟩
  · simp
  · rw [← cancel_mono g, Category.assoc, Category.assoc, h.lift_snd_assoc, hk, Category.id_comp,
      h.w]

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}

/-- If, after sheafification, `m : A ⟶ X` factors through a monomorphism `n : B ⟶ X`, then every
section of `A` is mapped by `m`, locally, into the image of `n`. -/
theorem locally_exists_app_eq_of_factorization {A B X : Dᵒᵖ ⥤ Type u} (m : A ⟶ X) (n : B ⟶ X)
    [Mono n] (k : (presheafToSheaf K (Type u)).obj A ⟶ (presheafToSheaf K (Type u)).obj B)
    (hk : k ≫ (presheafToSheaf K (Type u)).map n = (presheafToSheaf K (Type u)).map m) (d : D)
    (x : A.obj (op d)) :
    Locally K d fun _ g => ∃ y, n.app _ y = X.map g.op (m.app _ x) := by
  let a := presheafToSheaf K (Type u)
  have : IsIso (a.map (pullback.fst m n)) :=
    isIso_fst_of_isPullback_of_factors ((IsPullback.of_hasPullback m n).map a) k hk
  have hW : K.W (pullback.fst m n) := (K.W_iff _).2 this
  obtain ⟨_, hs⟩ := (K.W_iff_isLocallyBijective _).1 hW
  refine ⟨_, hs.imageSieve_mem x, fun d' g ⟨t, ht⟩ => ⟨(pullback.snd m n).app _ t, ?_⟩⟩
  rw [← pullback_condition_app, ht, NatTrans.naturality_apply]

namespace CatStructure

variable {L : FirstOrder.Language.{u, u}}

/-- **Local Kripke–Joyal semantics.** If a structure `M` in `Sh(D, K)` is a model of a sequent
`φ ⊢ ψ` of `T`, every tuple of sections at `d` of the underlying presheaf satisfying `φ` in the
fiber structure satisfies `ψ` locally on `d`. -/
theorem IsModel.locally_realize {T : GeometricTheory.{u} L} {M : CatStructure L (Sheaf K (Type u))}
    (hM : M.IsModel T) {σ : Sequent.{u} L} (hσ : σ ∈ T) (d : D)
    (x : Fin σ.n → (M.map (sheafToPresheaf K (Type u))).carrier.obj (op d))
    (hx : letI := (M.map (sheafToPresheaf K (Type u))).fiberStr (op d); σ.lhs.Realize x) :
    Locally K d fun d' g =>
      letI := (M.map (sheafToPresheaf K (Type u))).fiberStr (op d')
      σ.rhs.Realize fun i => (M.map (sheafToPresheaf K (Type u))).carrier.map g.op (x i) := by
  let P := M.map (sheafToPresheaf K (Type u))
  let a := presheafToSheaf K (Type u)
  have hP := ((isomorphic_map_sheafToPresheaf_map_presheafToSheaf M).isModel_iff).1 hM σ hσ
  rw [interp_map P a, interp_map P a] at hP
  obtain ⟨k, hk⟩ : ∃ k, k ≫ a.map (P.interp σ.rhs).arrow = a.map (P.interp σ.lhs).arrow := by
    refine ⟨Subobject.ofMkLEMk _ _ hP, ?_⟩
    rw [← cancel_mono (piComparison a fun _ : Fin σ.n => P.carrier), Category.assoc,
      Subobject.ofMkLEMk_comp]
  obtain ⟨w, hw⟩ := (Syntactic.mem_range_interp_app_iff P σ.lhs (op d)
    ((Syntactic.secEquiv P.carrier σ.n (op d)).symm x)).2 (by rwa [Equiv.apply_symm_apply])
  refine (locally_exists_app_eq_of_factorization _ _ k hk d w).mono fun d' g ⟨y, hy⟩ => ?_
  have := (Syntactic.mem_range_interp_app_iff P σ.rhs (op d') _).1 ⟨y, hy⟩
  rwa [hw, Syntactic.secEquiv_map, Equiv.apply_symm_apply] at this

end CatStructure

end LeanPool.ClassifyingTopoi
