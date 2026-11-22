/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Singles

/-!
# Triangulated embeddings force surjective projections (Theorem 3.1, (1) ⇒ (2))

Let `(F, η) : C(D) → T` be a triangulated embedding. The interval conflations
`A i → P i → Y` go to distinguished triangles with connecting morphisms `δ_i = η(ε_i)`, and
`(a_{ji})_* ε_j = ε_i` gives `δ_j ≫ (F a_{ji})⟦1⟧ = δ_i`. For `u ∈ D_i`, the composite
`X → A i → P i` vanishes, so `(F u)⟦1⟧ = v ≫ δ_i` for some `v : FX⟦1⟧ → FY`. The morphisms
`v ≫ δ_j` come from a compatible family `(u_j)` with `u_i = u`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Pretriangulated Statement IntervalLabel

universe u v' u'

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- Generalization of the necessity direction of Theorem 3.1 to any linearly ordered index,
arbitrary transition maps, and pretriangulated targets. An embedding of `C(D)` forces every
projection `lim D → D_i` to be surjective. The paper uses a nonempty ordinal, surjective
transition maps, and a triangulated target. -/
theorem projectionsSurjective_of_embedding {T : Type u'} [Category.{v'} T] [Preadditive T]
    [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    (Φ : ExtriangulatedFunctor (cdData D) T) (hΦ : Φ.IsTriangulatedEmbedding) :
    ProjectionsSurjective D := by
  obtain ⟨hfull, hfaith⟩ := hΦ
  let _ := Φ.additive
  intro i x
  let F := Φ.F
  have hdist : ∀ j : I, Triangle.mk (F.map (sMap D (bMap j))) (F.map (sMap D (cMap j)))
      (Φ.η (epsClass D j)) ∈ distTriang T :=
    fun j => Φ.distinguished (realizes_epsClass D j)
  have hpush : ∀ {h j : I} (hhj : h ≤ j),
      Φ.η (epsClass D j) ≫ (F.map (sMap D (aMap hhj)))⟦(1 : ℤ)⟧' = Φ.η (epsClass D h) := by
    intro h j hhj
    rw [← push_epsClass D hhj]
    exact (Φ.η_push _ _).symm
  have hu : (F.map (xHom D x))⟦(1 : ℤ)⟧' ≫ (-(F.map (sMap D (bMap i)))⟦(1 : ℤ)⟧') = 0 := by
    rw [Preadditive.comp_neg, ← Functor.map_comp, ← F.map_comp, xHom_comp_bMap, F.map_zero,
      Functor.map_zero, neg_zero]
  obtain ⟨v, hv⟩ : ∃ v : (F.obj (sX D))⟦(1 : ℤ)⟧ ⟶ F.obj (sI D Y),
      (F.map (xHom D x))⟦(1 : ℤ)⟧' = v ≫ Φ.η (epsClass D i) :=
    Triangle.coyoneda_exact₃ _ (rot_of_distTriang _ (hdist i)) ((F.map (xHom D x))⟦(1 : ℤ)⟧') hu
  have hlift : ∀ j : I, ∃ d : D.obj (op j),
      (F.map (xHom D d))⟦(1 : ℤ)⟧' = v ≫ Φ.η (epsClass D j) := by
    intro j
    obtain ⟨w, hw⟩ := (shiftFunctor T (1 : ℤ)).map_surjective (v ≫ Φ.η (epsClass D j))
    obtain ⟨f, hf⟩ := F.map_surjective w
    obtain ⟨d, rfl⟩ := xHom_surjective D f
    exact ⟨d, by rw [hf, hw]⟩
  choose y hy using hlift
  refine ⟨y, fun {j j'} hjj' => ?_, ?_⟩
  · apply xHom_injective D
    apply F.map_injective
    apply (shiftFunctor T (1 : ℤ)).map_injective
    rw [← xHom_comp_aMap, F.map_comp, Functor.map_comp, hy, Category.assoc, hpush, hy]
  · apply xHom_injective D
    apply F.map_injective
    apply (shiftFunctor T (1 : ℤ)).map_injective
    rw [hy]
    exact hv.symm

/-- Generalized necessity direction of Theorem B for linearly ordered indices, arbitrary
transition maps, and triangulated targets in all universes. -/
theorem theoremB_necessity : TheoremBNecessity.{u, v', u'} := by
  intro k _ I _ D hD
  obtain ⟨T, _, _, _, _, _, _, _, Φ, hΦ⟩ := hD
  exact projectionsSurjective_of_embedding D Φ hΦ

end ExtriangulatedRealization
