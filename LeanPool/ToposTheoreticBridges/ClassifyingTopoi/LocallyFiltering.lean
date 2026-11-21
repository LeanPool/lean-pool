/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Tensor
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Locally filtering functors

Let `(D, K)` be a small site. A functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` is *locally filtering* for `K`
when its categories of elements are cofiltered locally on `D`: for every object `d` of `D`,

* there is, locally on `d`, an object `c` with an element of `F(c)`;
* two elements `x₁ : F(c₁)(d)`, `x₂ : F(c₂)(d)` come, locally on `d`, from one element of
  `F(e)` along a span `c₁ ← e → c₂`;
* an element `x : F(c)(d)` equalized by two morphisms `u v : c ⟶ c'` comes, locally on `d`,
  from an element of `F(e)` along a morphism `w : e ⟶ c` with `w ≫ u = w ≫ v`.

"Locally on `d`" means: after restriction along every morphism of some `K`-covering sieve of
`d` (`LeanPool.ClassifyingTopoi.Locally`). These are the Kripke–Joyal translations of the
statement that the category of elements of `F ⋙ a_K`, an internal category of `Sh(D, K)`, is
cofiltered: `F ⋙ a_K` is flat in the internal sense of the topos `Sh(D, K)`.

The key consequence is that equality in the tensor products `P ⊗_C F(-)(d)` is locally that of a
filtered colimit: two triples with the same class have, locally, a common refinement
(`LeanPool.ClassifyingTopoi.IsLocallyFiltering.locally_of_tensorι_eq`).

## Main definitions

* `LeanPool.ClassifyingTopoi.Locally`: a property holding locally on an object of a site;
* `LeanPool.ClassifyingTopoi.IsLocallyFiltering`: locally filtering functors.

## Main results

* `LeanPool.ClassifyingTopoi.IsLocallyFiltering.merge`: two elements over a common object merge
  locally into one element;
* `LeanPool.ClassifyingTopoi.IsLocallyFiltering.locally_of_tensorι_eq`: two triples with the
  same class in `P ⊗_C F(-)(d)` have locally a common refinement.

## References

* S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*, VII.8 (Definition 1 of filtering
  functors) and VII.9 (Lemma 2, the version over a site).
* P. T. Johnstone, *Sketches of an Elephant*, B3.2.1 and C2.3.9.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace LeanPool.ClassifyingTopoi

section Locally

variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)

/-- A property `Q` of the morphisms into `d` holds locally when it holds on a `K`-covering
sieve of `d`. -/
def Locally (d : D) (Q : ∀ ⦃d' : D⦄, (d' ⟶ d) → Prop) : Prop :=
  ∃ S ∈ K d, ∀ ⦃d' : D⦄ (g : d' ⟶ d), S g → Q g

variable {K} {d : D} {Q Q' : ∀ ⦃d' : D⦄, (d' ⟶ d) → Prop}

namespace Locally

/-- A property holding on every morphism holds locally. -/
theorem of_forall (h : ∀ ⦃d' : D⦄ (g : d' ⟶ d), Q g) : Locally K d Q :=
  ⟨⊤, K.top_mem d, fun _ g _ => h g⟩

/-- A local property implies locally every weaker property. -/
theorem mono (h : Locally K d Q) (hQ : ∀ ⦃d' : D⦄ (g : d' ⟶ d), Q g → Q' g) :
    Locally K d Q' :=
  let ⟨S, hS, h⟩ := h
  ⟨S, hS, fun _ g hg => hQ g (h g hg)⟩

/-- Two local properties hold locally together. -/
theorem and (h : Locally K d Q) (h' : Locally K d Q') : Locally K d fun _ g => Q g ∧ Q' g :=
  let ⟨S, hS, h⟩ := h
  let ⟨S', hS', h'⟩ := h'
  ⟨S ⊓ S', K.intersection_covering hS hS', fun _ g hg => ⟨h g hg.1, h' g hg.2⟩⟩

/-- Local properties are local: if `Q` holds locally and, wherever `Q g` holds, `Q'` holds
locally on the source of `g` (after composition with `g`), then `Q'` holds locally. -/
theorem bind (h : Locally K d Q)
    (h' : ∀ ⦃d' : D⦄ (g : d' ⟶ d), Q g → Locally K d' fun _ k => Q' (k ≫ g)) :
    Locally K d Q' := by
  obtain ⟨S, hS, hQ⟩ := h
  choose R hR hR' using fun (d' : D) (g : d' ⟶ d) (hg : S g) => h' g (hQ g hg)
  refine ⟨Sieve.bind S (fun _ g hg => R _ g hg), K.bind_covering hS (fun _ g hg => hR _ g hg),
    ?_⟩
  rintro d'' _ ⟨d', k, g, hg, hk, rfl⟩
  exact hR' d' g hg k hk

end Locally

end Locally

section Filtering

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (K : GrothendieckTopology D) (F : C ⥤ (Dᵒᵖ ⥤ Type u))

/-- A functor `F : C ⥤ (Dᵒᵖ ⥤ Type u)` is locally filtering for `K` when its categories of
elements are cofiltered locally on `D`: nonempty, with cones over pairs of objects, and with
equalizing cones over parallel pairs, each after restriction to some `K`-covering sieve. -/
structure IsLocallyFiltering : Prop where
  /-- Locally there is an element. -/
  nonempty (d : D) : Locally K d fun d' _ => ∃ c : C, Nonempty ((F.obj c).obj (op d'))
  /-- Two elements come locally from one element along a span. -/
  span (d : D) {c₁ c₂ : C} (x₁ : (F.obj c₁).obj (op d)) (x₂ : (F.obj c₂).obj (op d)) :
    Locally K d fun d' g => ∃ (e : C) (u : e ⟶ c₁) (v : e ⟶ c₂) (y : (F.obj e).obj (op d')),
      (F.map u).app _ y = (F.obj c₁).map g.op x₁ ∧ (F.map v).app _ y = (F.obj c₂).map g.op x₂
  /-- An element equalized by two morphisms comes locally from an equalizing morphism. -/
  equalize (d : D) {c c' : C} (u v : c ⟶ c') (x : (F.obj c).obj (op d))
    (h : (F.map u).app _ x = (F.map v).app _ x) :
    Locally K d fun d' g => ∃ (e : C) (w : e ⟶ c) (y : (F.obj e).obj (op d')),
      w ≫ u = w ≫ v ∧ (F.map w).app _ y = (F.obj c).map g.op x

variable {K F}

/-- Restriction along a composite. -/
theorem map_op_comp_apply {c : C} {d d' d'' : D} (k : d'' ⟶ d') (g : d' ⟶ d)
    (x : (F.obj c).obj (op d)) :
    (F.obj c).map (k ≫ g).op x = (F.obj c).map k.op ((F.obj c).map g.op x) := by
  rw [op_comp, Functor.map_comp, types_comp_apply]

/-- The maps `F(u)` commute with restriction. -/
theorem map_app_map_op {c c' : C} (u : c ⟶ c') {d d' : D} (g : d' ⟶ d)
    (x : (F.obj c).obj (op d)) :
    (F.map u).app _ ((F.obj c).map g.op x) = (F.obj c').map g.op ((F.map u).app _ x) :=
  NatTrans.naturality_apply (F.map u) g.op x

/-- `F` applied to a composite. -/
theorem map_comp_app_apply {c c' c'' : C} (u : c ⟶ c') (v : c' ⟶ c'') {d : Dᵒᵖ}
    (x : (F.obj c).obj d) :
    (F.map (u ≫ v)).app d x = (F.map v).app d ((F.map u).app d x) := by
  rw [Functor.map_comp, NatTrans.comp_app, types_comp_apply]

/-- **Merging.** Two elements `b : F(e)(d)` and `b' : F(e')(d)` with the same image in `F(c)`
along `u : e ⟶ c` and `u' : e' ⟶ c` come locally from one element along a commutative square. -/
theorem IsLocallyFiltering.merge (hF : IsLocallyFiltering K F) {d : D} {e e' c : C}
    (b : (F.obj e).obj (op d)) (b' : (F.obj e').obj (op d)) (u : e ⟶ c) (u' : e' ⟶ c)
    (h : (F.map u).app _ b = (F.map u').app _ b') :
    Locally K d fun d' g => ∃ (e'' : C) (w : e'' ⟶ e) (w' : e'' ⟶ e')
      (b'' : (F.obj e'').obj (op d')), w ≫ u = w' ≫ u' ∧
        (F.map w).app _ b'' = (F.obj e).map g.op b ∧
          (F.map w').app _ b'' = (F.obj e').map g.op b' := by
  refine (hF.span d b b').bind fun d' g ⟨e₀, w₀, w₀', y, hy, hy'⟩ => ?_
  have hyu : (F.map (w₀ ≫ u)).app _ y = (F.map (w₀' ≫ u')).app _ y := by
    rw [map_comp_app_apply, map_comp_app_apply, hy, hy', map_app_map_op, map_app_map_op, h]
  refine (hF.equalize d' _ _ y hyu).mono fun d'' k ⟨e'', z, y', hz, hy''⟩ =>
    ⟨e'', z ≫ w₀, z ≫ w₀', y', by simpa using hz, ?_, ?_⟩
  · rw [map_comp_app_apply, hy'', map_app_map_op, hy, map_op_comp_apply]
  · rw [map_comp_app_apply, hy'', map_app_map_op, hy', map_op_comp_apply]

variable (P : Cᵒᵖ ⥤ Type u)

/-- Two pairs of an element of `F(-)(d)` and of `P` have locally a common refinement. -/
def CommonRefinement {d : D} {c₁ c₂ : C} (a₁ : (F.obj c₁).obj (op d))
    (a₂ : (F.obj c₂).obj (op d)) (p₁ : P.obj (op c₁)) (p₂ : P.obj (op c₂)) : Prop :=
  Locally K d fun d' g => ∃ (e : C) (u : e ⟶ c₁) (v : e ⟶ c₂) (b : (F.obj e).obj (op d')),
    (F.map u).app _ b = (F.obj c₁).map g.op a₁ ∧ (F.map v).app _ b = (F.obj c₂).map g.op a₂ ∧
      P.map u.op p₁ = P.map v.op p₂

omit [SmallCategory D] in
theorem map_op_comp_apply' {c c' c'' : C} (u : c ⟶ c') (v : c' ⟶ c'') (p : P.obj (op c'')) :
    P.map (u ≫ v).op p = P.map u.op (P.map v.op p) := by
  rw [op_comp, Functor.map_comp, types_comp_apply]

theorem IsLocallyFiltering.commonRefinement_trans (hF : IsLocallyFiltering K F) {d : D}
    {c₁ c₂ c₃ : C} {a₁ : (F.obj c₁).obj (op d)} {a₂ : (F.obj c₂).obj (op d)}
    {a₃ : (F.obj c₃).obj (op d)} {p₁ : P.obj (op c₁)} {p₂ : P.obj (op c₂)} {p₃ : P.obj (op c₃)}
    (h₁₂ : CommonRefinement (K := K) (F := F) P a₁ a₂ p₁ p₂)
    (h₂₃ : CommonRefinement (K := K) (F := F) P a₂ a₃ p₂ p₃) :
    CommonRefinement (K := K) (F := F) P a₁ a₃ p₁ p₃ := by
  refine (h₁₂.and h₂₃).bind fun d' g ⟨⟨e, u, v, b, hu, hv, hp⟩, ⟨e', u', v', b', hu', hv', hp'⟩⟩ =>
    ?_
  refine (hF.merge b b' v u' (hv.trans hu'.symm)).mono
    fun d'' k ⟨e'', w, w', b'', hww, hw, hw'⟩ => ⟨e'', w ≫ u, w' ≫ v', b'', ?_, ?_, ?_⟩
  · rw [map_comp_app_apply, hw, map_app_map_op, hu, map_op_comp_apply]
  · rw [map_comp_app_apply, hw', map_app_map_op, hv', map_op_comp_apply]
  · rw [map_op_comp_apply', hp, ← map_op_comp_apply', hww, map_op_comp_apply', hp',
      ← map_op_comp_apply']

/-- Two common refinements, for two presheaves `P` and `Q` and the same pair of elements of `F`,
merge locally into one common refinement for both. -/
theorem IsLocallyFiltering.commonRefinement_and (hF : IsLocallyFiltering K F)
    {Q : Cᵒᵖ ⥤ Type u} {d : D} {c₁ c₂ : C} {a₁ : (F.obj c₁).obj (op d)}
    {a₂ : (F.obj c₂).obj (op d)} {p₁ : P.obj (op c₁)} {p₂ : P.obj (op c₂)}
    {q₁ : Q.obj (op c₁)} {q₂ : Q.obj (op c₂)}
    (hP : CommonRefinement (K := K) (F := F) P a₁ a₂ p₁ p₂)
    (hQ : CommonRefinement (K := K) (F := F) Q a₁ a₂ q₁ q₂) :
    Locally K d fun d' g => ∃ (e : C) (u : e ⟶ c₁) (v : e ⟶ c₂) (b : (F.obj e).obj (op d')),
      (F.map u).app _ b = (F.obj c₁).map g.op a₁ ∧ (F.map v).app _ b = (F.obj c₂).map g.op a₂ ∧
        P.map u.op p₁ = P.map v.op p₂ ∧ Q.map u.op q₁ = Q.map v.op q₂ := by
  refine (hP.and hQ).bind fun d' g ⟨⟨e, u, v, b, hu, hv, hp⟩, ⟨e', u', v', b', hu', hv', hq⟩⟩ =>
    ?_
  refine (hF.merge b b' u u' (hu.trans hu'.symm)).bind
    fun d₂ k ⟨e₂, w, w', b₂, hww, hw, hw'⟩ => ?_
  have hb : (F.map (w ≫ v)).app _ b₂ = (F.map (w' ≫ v')).app _ b₂ := by
    rw [map_comp_app_apply, map_comp_app_apply, hw, hw', map_app_map_op, map_app_map_op, hv,
      hv']
  refine (hF.equalize d₂ _ _ b₂ hb).mono fun d₃ l ⟨e₃, z, b₃, hz, hzb⟩ =>
    ⟨e₃, z ≫ w ≫ u, z ≫ w ≫ v, b₃, ?_, ?_, ?_, ?_⟩
  · simp only [map_comp_app_apply, hzb, map_app_map_op, hw, hu, map_op_comp_apply]
  · simp only [map_comp_app_apply, hzb, map_app_map_op, hw, hv, map_op_comp_apply]
  · simp only [map_op_comp_apply', hp]
  · rw [hww, show Q.map (z ≫ w' ≫ u').op q₁ = Q.map (z ≫ w' ≫ v').op q₂ by
      simp only [map_op_comp_apply', hq], ← hz]

/-- **Local straightening.** In a locally filtering functor, two triples with the same class in
the tensor product `P ⊗_C F(-)(d)` have locally a common refinement: an element `b : F(e)` with
morphisms `u : e ⟶ c₁`, `v : e ⟶ c₂` sending `b` to the restrictions of `a₁` and `a₂`, along
which `p₁` and `p₂` agree. -/
theorem IsLocallyFiltering.locally_of_tensorι_eq (hF : IsLocallyFiltering K F) {d : D}
    {c₁ c₂ : C} {a₁ : (F.obj c₁).obj (op d)} {a₂ : (F.obj c₂).obj (op d)}
    {p₁ : P.obj (op c₁)} {p₂ : P.obj (op c₂)}
    (h : extι P (op d) c₁ a₁ p₁ = extι P (op d) c₂ a₂ p₂) :
    CommonRefinement (K := K) (F := F) P a₁ a₂ p₁ p₂ := by
  let A := F.flip.obj (op d)
  suffices key : ∀ z z' : Σ j : A.Elementsᵒᵖ, P.obj (op j.unop.obj),
      Relation.EqvGen ((Functor.Elements.π A).op ⋙ P).ColimitTypeRel z z' →
        CommonRefinement (K := K) (F := F) P z.1.unop.val z'.1.unop.val z.2 z'.2 from
    key _ _ (eqvGen_of_tensorι_eq A P h)
  intro z z' hz
  induction hz with
  | rel z z' hr =>
    obtain ⟨f, hf⟩ := hr
    rw [hf]
    refine Locally.of_forall fun d' g =>
      ⟨z'.1.unop.obj, f.unop.hom, 𝟙 _, (F.obj z'.1.unop.obj).map g.op z'.1.unop.val, ?_, ?_, ?_⟩
    · rw [map_app_map_op]
      exact congrArg _ f.unop.map_val
    · simp
    · simp
  | refl z =>
    exact Locally.of_forall fun d' g =>
      ⟨z.1.unop.obj, 𝟙 _, 𝟙 _, (F.obj z.1.unop.obj).map g.op z.1.unop.val, by simp, by simp,
        rfl⟩
  | symm z z' _ ih =>
    exact ih.mono fun d' g ⟨e, u, v, b, hu, hv, hp⟩ => ⟨e, v, u, b, hv, hu, hp.symm⟩
  | trans z z' z'' _ _ ih ih' => exact hF.commonRefinement_trans P ih ih'

end Filtering

end LeanPool.ClassifyingTopoi
