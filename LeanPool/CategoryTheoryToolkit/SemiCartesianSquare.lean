/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Semi-cartesian squares in an abelian category

A commutative square
```
 a ──α₁──▶ a₁
 │α₂       │β₁
 ▼         ▼
 a₂ ──β₂─▶ b
```
of an abelian category is *semi-cartesian* when the map `μ` from the pushout of `(α₁, α₂)` to
`b` is a monomorphism and the map `ν` from `a` to the pullback of `(β₁, β₂)` is an epimorphism.
The proofs chase elements up to refinements, through `CommSq.exact_shortComplex_iff`, which turns
the exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b` (Mathlib's `CommSq.shortComplex`) into a statement on pairs of
morphisms.

## Main statements

* `CommSq.fromPushout`, `CommSq.toPullback`, `CommSq.IsSemiCartesian`;
* `CommSq.mono_fromPushout_iff_exact`, `CommSq.epi_toPullback_iff_exact`,
  `CommSq.mono_fromPushout_iff_epi_toPullback`, `CommSq.isSemiCartesian_iff_exact`,
  `CommSq.isSemiCartesian_iff_mono`, `CommSq.isSemiCartesian_iff_epi`: the two conditions are
  equivalent, and equivalent to the exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b`;
* `IsPushout.isSemiCartesian`, `IsPullback.isSemiCartesian`, `CommSq.IsSemiCartesian.flip`;
* `CommSq.IsSemiCartesian.isPullback_of_mono`, `CommSq.IsSemiCartesian.isPushout_of_epi`;
* `CommSq.isSemiCartesian_of_isPushout_of_isPullback`, `CommSq.IsSemiCartesian.left_of_comp`,
  `CommSq.IsSemiCartesian.right_of_comp`, `CommSq.IsSemiCartesian.isPushout_isPullback_of_comp`,
  `CommSq.isSemiCartesian_iff_exists_factorisation`: composites of a cocartesian and a cartesian
  square;
* `CommSq.isSemiCartesian_iff_exact_kernel_cokernel`: semi-cartesian iff
  `ker α₁ ⟶ a₂ ⟶ b` and `a ⟶ a₁ ⟶ coker β₂` are exact.
-/

@[expose] public section

namespace CategoryTheory.CommSq

open Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {a a₁ a₂ b : C} {α₁ : a ⟶ a₁} {α₂ : a ⟶ a₂} {β₁ : a₁ ⟶ b} {β₂ : a₂ ⟶ b}

/-- The map `μ` from the pushout of `(α₁, α₂)` to `b` induced by a commutative square. -/
noncomputable abbrev fromPushout (sq : CommSq α₁ α₂ β₁ β₂) : pushout α₁ α₂ ⟶ b :=
  pushout.desc β₁ β₂ sq.w

/-- The map `ν` from `a` to the pullback of `(β₁, β₂)` induced by a commutative square. -/
noncomputable abbrev toPullback (sq : CommSq α₁ α₂ β₁ β₂) : a ⟶ pullback β₁ β₂ :=
  pullback.lift α₁ α₂ sq.w

/-- A commutative square is semi-cartesian when the map from the pushout to `b` is a monomorphism
and the map from `a` to the pullback is an epimorphism (each condition implies the other,
`CommSq.mono_fromPushout_iff_epi_toPullback`). -/
def IsSemiCartesian (sq : CommSq α₁ α₂ β₁ β₂) : Prop :=
  Mono (fromPushout sq) ∧ Epi (toPullback sq)

/-- The exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b` in terms of morphisms: whenever `x₁ ≫ β₁ + x₂ ≫ β₂ = 0`, the
pair `(x₁, x₂)` comes, after an epimorphism `π`, from some `y : T' ⟶ a` as `(y ≫ α₁, -(y ≫ α₂))`. -/
theorem exact_shortComplex_iff (sq : CommSq α₁ α₂ β₁ β₂) :
    sq.shortComplex.Exact ↔
      ∀ ⦃T : C⦄ (x₁ : T ⟶ a₁) (x₂ : T ⟶ a₂), x₁ ≫ β₁ + x₂ ≫ β₂ = 0 →
        ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ a),
          π ≫ x₁ = y ≫ α₁ ∧ π ≫ x₂ = -(y ≫ α₂) := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  change (∀ ⦃A : C⦄ (x : A ⟶ a₁ ⊞ a₂) (_ : x ≫ biprod.desc β₁ β₂ = 0),
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ a), π ≫ x = y ≫ biprod.lift α₁ (-α₂))
      ↔ _
  constructor
  · intro h T x₁ x₂ hx
    obtain ⟨T', π, hπ, y, fac⟩ := h (biprod.lift x₁ x₂) (by simpa using hx)
    exact ⟨T', π, hπ, y, by simpa using fac =≫ biprod.fst, by simpa using fac =≫ biprod.snd⟩
  · intro h T x hx
    obtain ⟨T', π, hπ, y, h₁, h₂⟩ := h (x ≫ biprod.fst) (x ≫ biprod.snd) (by
      simpa [biprod.desc_eq] using hx)
    exact ⟨T', π, hπ, y, by ext <;> simp [h₁, h₂]⟩

variable (sq : CommSq α₁ α₂ β₁ β₂)

/-- The map from the pushout to `b` is a monomorphism if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
theorem mono_fromPushout_iff_exact : Mono (fromPushout sq) ↔ sq.shortComplex.Exact := by
  have hpo := IsPushout.of_hasPushout α₁ α₂
  constructor
  · intro hμ
    rw [exact_shortComplex_iff]
    intro T x₁ x₂ hx
    refine (exact_shortComplex_iff hpo.toCommSq).1 hpo.exact_shortComplex x₁ x₂ ?_
    rw [← cancel_mono (fromPushout sq)]
    simpa using hx
  · intro hex
    rw [mono_iff_cancel_zero]
    intro T z hz
    obtain ⟨T₁, π, _, x₁, x₂, eq⟩ := hpo.hom_eq_add_up_to_refinements z
    obtain ⟨T₂, π', _, y, h₁, h₂⟩ := (exact_shortComplex_iff sq).1 hex x₁ x₂ (by
      have := π ≫= hz
      rw [← Category.assoc, eq] at this
      simpa using this)
    have : (π' ≫ π) ≫ z = (π' ≫ π) ≫ 0 := by
      rw [Category.assoc, eq, comp_add, reassoc_of% h₁, reassoc_of% h₂]
      simp [pushout.condition]
    exact (cancel_epi _).1 this

/-- The map from `a` to the pullback is an epimorphism if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
theorem epi_toPullback_iff_exact : Epi (toPullback sq) ↔ sq.shortComplex.Exact := by
  constructor
  · intro hν
    rw [exact_shortComplex_iff]
    intro T x₁ x₂ hx
    have hw : x₁ ≫ β₁ = (-x₂) ≫ β₂ := by
      rw [neg_comp, eq_neg_iff_add_eq_zero, hx]
    obtain ⟨T', π, hπ, y, fac⟩ :=
      surjective_up_to_refinements_of_epi (toPullback sq) (pullback.lift x₁ (-x₂) hw)
    refine ⟨T', π, hπ, y, by simpa using fac =≫ pullback.fst _ _, ?_⟩
    have := fac =≫ pullback.snd _ _
    simp only [Category.assoc, pullback.lift_snd, comp_neg] at this
    rw [← this, neg_neg]
  · intro hex
    rw [epi_iff_surjective_up_to_refinements]
    intro T w
    obtain ⟨T', π, hπ, y, h₁, h₂⟩ := (exact_shortComplex_iff sq).1 hex (w ≫ pullback.fst _ _)
      (-(w ≫ pullback.snd _ _)) (by simp [pullback.condition])
    refine ⟨T', π, hπ, y, ?_⟩
    apply pullback.hom_ext
    · simpa using h₁
    · simpa using h₂

/-- The map from the pushout to `b` is a monomorphism if and only if the map from `a` to the
pullback is an epimorphism. -/
theorem mono_fromPushout_iff_epi_toPullback :
    Mono (fromPushout sq) ↔ Epi (toPullback sq) :=
  (mono_fromPushout_iff_exact sq).trans (epi_toPullback_iff_exact sq).symm

/-- A square is semi-cartesian if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
theorem isSemiCartesian_iff_exact : IsSemiCartesian sq ↔ sq.shortComplex.Exact :=
  ⟨fun h ↦ (mono_fromPushout_iff_exact sq).1 h.1,
    fun h ↦ ⟨(mono_fromPushout_iff_exact sq).2 h, (epi_toPullback_iff_exact sq).2 h⟩⟩

/-- A square is semi-cartesian if and only if the map from the pushout to `b` is mono. -/
theorem isSemiCartesian_iff_mono : IsSemiCartesian sq ↔ Mono (fromPushout sq) :=
  (isSemiCartesian_iff_exact sq).trans (mono_fromPushout_iff_exact sq).symm

/-- A square is semi-cartesian if and only if the map from `a` to the pullback is epi. -/
theorem isSemiCartesian_iff_epi : IsSemiCartesian sq ↔ Epi (toPullback sq) :=
  (isSemiCartesian_iff_exact sq).trans (epi_toPullback_iff_exact sq).symm

variable {sq}

/-- A semi-cartesian square, read as a pair of morphisms. -/
theorem IsSemiCartesian.exists_lift (hs : IsSemiCartesian sq) {T : C} (x₁ : T ⟶ a₁)
    (x₂ : T ⟶ a₂) (hx : x₁ ≫ β₁ + x₂ ≫ β₂ = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ a),
      π ≫ x₁ = y ≫ α₁ ∧ π ≫ x₂ = -(y ≫ α₂) :=
  (exact_shortComplex_iff sq).1 ((isSemiCartesian_iff_exact sq).1 hs) x₁ x₂ hx

/-- A semi-cartesian square from the condition on pairs of morphisms. -/
theorem IsSemiCartesian.of_lift
    (h : ∀ ⦃T : C⦄ (x₁ : T ⟶ a₁) (x₂ : T ⟶ a₂), x₁ ≫ β₁ + x₂ ≫ β₂ = 0 →
      ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ a),
        π ≫ x₁ = y ≫ α₁ ∧ π ≫ x₂ = -(y ≫ α₂)) :
    IsSemiCartesian sq :=
  (isSemiCartesian_iff_exact sq).2 ((exact_shortComplex_iff sq).2 h)

/-- A cocartesian square is semi-cartesian. -/
theorem _root_.CategoryTheory.IsPushout.isSemiCartesian (h : IsPushout α₁ α₂ β₁ β₂) :
    IsSemiCartesian h.toCommSq :=
  (isSemiCartesian_iff_exact _).2 h.exact_shortComplex

/-- A cartesian square is semi-cartesian. -/
theorem _root_.CategoryTheory.IsPullback.isSemiCartesian (h : IsPullback α₁ α₂ β₁ β₂) :
    IsSemiCartesian h.toCommSq :=
  IsSemiCartesian.of_lift fun T x₁ x₂ hx ↦
    ⟨T, 𝟙 T, inferInstance, h.lift x₁ (-x₂) (by rw [neg_comp, eq_neg_iff_add_eq_zero, hx]),
      by simp, by simp⟩

/-- The symmetric square (exchanging `a₁` and `a₂`) of a semi-cartesian square is semi-cartesian. -/
theorem IsSemiCartesian.flip (hs : IsSemiCartesian sq) : IsSemiCartesian sq.flip :=
  IsSemiCartesian.of_lift fun T x₂ x₁ hx ↦ by
    obtain ⟨T', π, hπ, y, h₁, h₂⟩ := hs.exists_lift x₁ x₂ (by rw [add_comm]; exact hx)
    exact ⟨T', π, hπ, -y, by simpa using h₂, by simpa using h₁⟩

/-- A semi-cartesian square in which `α₁` is a monomorphism is cartesian, and `β₂` is then a
monomorphism. -/
theorem IsSemiCartesian.isPullback_of_mono (hs : IsSemiCartesian sq) [Mono α₁] :
    IsPullback α₁ α₂ β₁ β₂ ∧ Mono β₂ := by
  have : Mono (toPullback sq) := mono_of_mono_fac (pullback.lift_fst _ _ _)
  have : Epi (toPullback sq) := hs.2
  have : IsIso (toPullback sq) := isIso_of_mono_of_epi _
  have hp : IsPullback α₁ α₂ β₁ β₂ :=
    IsPullback.of_iso_pullback sq (asIso (toPullback sq)) (by simp) (by simp)
  refine ⟨hp, mono_of_cancel_zero _ fun {T} ζ hζ ↦ ?_⟩
  have h0 : hp.lift 0 ζ (by simp [hζ]) = 0 :=
    zero_of_comp_mono α₁ (by simp)
  simpa [h0] using (hp.lift_snd 0 ζ (by simp [hζ])).symm

/-- A semi-cartesian square in which `β₂` is an epimorphism is cocartesian, and `α₁` is then an
epimorphism. -/
theorem IsSemiCartesian.isPushout_of_epi (hs : IsSemiCartesian sq) [Epi β₂] :
    IsPushout α₁ α₂ β₁ β₂ ∧ Epi α₁ := by
  have : Epi (fromPushout sq) := epi_of_epi_fac (pushout.inr_desc _ _ _)
  have : Mono (fromPushout sq) := hs.1
  have : IsIso (fromPushout sq) := isIso_of_mono_of_epi _
  have hp : IsPushout α₁ α₂ β₁ β₂ :=
    IsPushout.of_iso_pushout sq (asIso (fromPushout sq)).symm
      (by simp [IsIso.comp_inv_eq]) (by simp [IsIso.comp_inv_eq])
  refine ⟨hp, epi_of_cancel_zero _ fun {T} z hz ↦ ?_⟩
  have h0 : hp.desc z 0 (by simp [hz]) = 0 :=
    zero_of_epi_comp β₂ (by simp)
  simpa [h0] using (hp.inl_desc z 0 (by simp [hz])).symm

/-- A cocartesian square followed by a cartesian square is semi-cartesian: if the square factors
as a pushout square `(α₁, u₀, u₁, α')` followed by a pullback square `(α', v₀, v₁, β₂)`, with
`α₂ = u₀ ≫ v₀` and `β₁ = u₁ ≫ v₁`, it is semi-cartesian. -/
theorem isSemiCartesian_of_isPushout_of_isPullback {p₀ p₁ : C} {α' : p₀ ⟶ p₁} {u₀ : a ⟶ p₀}
    {u₁ : a₁ ⟶ p₁} {v₀ : p₀ ⟶ a₂} {v₁ : p₁ ⟶ b} (h₁ : IsPushout α₁ u₀ u₁ α')
    (h₂ : IsPullback α' v₀ v₁ β₂) (e₀ : u₀ ≫ v₀ = α₂) (e₁ : u₁ ≫ v₁ = β₁) :
    IsSemiCartesian sq := by
  subst e₀ e₁
  refine IsSemiCartesian.of_lift fun T x₁ x₂ hx ↦ ?_
  have hw : (x₁ ≫ u₁) ≫ v₁ = (-x₂) ≫ β₂ := by
    rw [neg_comp, eq_neg_iff_add_eq_zero, Category.assoc, hx]
  obtain ⟨T', π, hπ, y, f₁, f₂⟩ := (exact_shortComplex_iff h₁.toCommSq).1 h₁.exact_shortComplex x₁
    (-h₂.lift _ _ hw) (by simp)
  refine ⟨T', π, hπ, y, f₁, ?_⟩
  have f₂' : π ≫ h₂.lift _ _ hw = y ≫ u₀ := by simpa using f₂
  have := f₂' =≫ v₀
  simp only [Category.assoc, IsPullback.lift_snd, comp_neg] at this
  rw [← neg_neg (π ≫ x₂), this]

section Factorisation

variable {p₀ p₁ : C} {α' : p₀ ⟶ p₁} {u₀ : a ⟶ p₀} {u₁ : a₁ ⟶ p₁} {v₀ : p₀ ⟶ a₂}
  {v₁ : p₁ ⟶ b}

/-- If a semi-cartesian square factors as `(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)`
and `v₀` is a monomorphism, then the first square is semi-cartesian. -/
theorem IsSemiCartesian.left_of_comp (s₁ : CommSq α₁ u₀ u₁ α') (s₂ : CommSq α' v₀ v₁ β₂)
    (e₀ : u₀ ≫ v₀ = α₂) (e₁ : u₁ ≫ v₁ = β₁) (hs : IsSemiCartesian sq) [Mono v₀] :
    IsSemiCartesian s₁ := by
  subst e₀ e₁
  refine IsSemiCartesian.of_lift fun T x₁ q hx ↦ ?_
  obtain ⟨T', π, hπ, y, h₁, h₂⟩ := hs.exists_lift x₁ (q ≫ v₀) (by
    simpa [s₂.w] using hx =≫ v₁)
  refine ⟨T', π, hπ, y, h₁, ?_⟩
  rw [← cancel_mono v₀]
  simpa using h₂

/-- If a semi-cartesian square factors as `(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)`
and `u₁` is an epimorphism, then the second square is semi-cartesian. -/
theorem IsSemiCartesian.right_of_comp (s₁ : CommSq α₁ u₀ u₁ α') (s₂ : CommSq α' v₀ v₁ β₂)
    (e₀ : u₀ ≫ v₀ = α₂) (e₁ : u₁ ≫ v₁ = β₁) (hs : IsSemiCartesian sq) [Epi u₁] :
    IsSemiCartesian s₂ := by
  subst e₀ e₁
  refine IsSemiCartesian.of_lift fun T q x₂ hx ↦ ?_
  obtain ⟨T₁, π₁, hπ₁, x₁, hq⟩ := surjective_up_to_refinements_of_epi u₁ q
  obtain ⟨T₂, π₂, hπ₂, y, h₁, h₂⟩ := hs.exists_lift x₁ (π₁ ≫ x₂) (by
    simpa [reassoc_of% hq] using π₁ ≫= hx)
  refine ⟨T₂, π₂ ≫ π₁, epi_comp _ _, y ≫ u₀, ?_, by simpa using h₂⟩
  simp only [Category.assoc]
  rw [hq, reassoc_of% h₁, s₁.w]

/-- If a semi-cartesian square factors as `(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)`
with `u₁` epi and `v₀` mono, the first square is cocartesian and the second cartesian. -/
theorem IsSemiCartesian.isPushout_isPullback_of_comp (s₁ : CommSq α₁ u₀ u₁ α')
    (s₂ : CommSq α' v₀ v₁ β₂) (e₀ : u₀ ≫ v₀ = α₂) (e₁ : u₁ ≫ v₁ = β₁)
    (hs : IsSemiCartesian sq) [Epi u₁] [Mono v₀] :
    IsPushout α₁ u₀ u₁ α' ∧ IsPullback α' v₀ v₁ β₂ :=
  ⟨(hs.left_of_comp s₁ s₂ e₀ e₁).flip.isPushout_of_epi.1.flip,
    (hs.right_of_comp s₁ s₂ e₀ e₁).flip.isPullback_of_mono.1.flip⟩

end Factorisation

variable (sq) in
/-- A commutative square is semi-cartesian if and only if it factors, in the arrow category, as
a pushout square `(α₁, u₀, u₁, α')` followed by a pullback square `(α', v₀, v₁, β₂)`, with
`α₂ = u₀ ≫ v₀` and `β₁ = u₁ ≫ v₁`. For the necessity, the pushout square of `(α₁, α₂)`
followed by the square `(pushout.inr, 𝟙, μ, β₂)` will do. -/
theorem isSemiCartesian_iff_exists_factorisation :
    IsSemiCartesian sq ↔
      ∃ (p₀ p₁ : C) (α' : p₀ ⟶ p₁) (u₀ : a ⟶ p₀) (u₁ : a₁ ⟶ p₁) (v₀ : p₀ ⟶ a₂) (v₁ : p₁ ⟶ b),
        IsPushout α₁ u₀ u₁ α' ∧ IsPullback α' v₀ v₁ β₂ ∧ u₀ ≫ v₀ = α₂ ∧ u₁ ≫ v₁ = β₁ := by
  constructor
  · intro hs
    have : Mono (fromPushout sq) := hs.1
    refine ⟨a₂, pushout α₁ α₂, pushout.inr _ _, α₂, pushout.inl _ _, 𝟙 a₂, fromPushout sq,
      IsPushout.of_hasPushout α₁ α₂, ?_, Category.comp_id _, pushout.inl_desc _ _ _⟩
    exact IsPullback.of_vert_isIso_mono ⟨by simp⟩
  · rintro ⟨p₀, p₁, α', u₀, u₁, v₀, v₁, h₁, h₂, e₀, e₁⟩
    exact isSemiCartesian_of_isPushout_of_isPullback h₁ h₂ e₀ e₁

/-- `α₁ ≫ β₁ ≫ cokernel.π β₂ = 0` for a commutative square. -/
theorem comp_cokernel_π_eq_zero (sq : CommSq α₁ α₂ β₁ β₂) :
    α₁ ≫ β₁ ≫ cokernel.π β₂ = 0 := by
  rw [← Category.assoc, sq.w, Category.assoc, cokernel.condition, comp_zero]

/-- `kernel.ι α₁ ≫ α₂ ≫ β₂ = 0` for a commutative square. -/
theorem kernel_ι_comp_eq_zero (sq : CommSq α₁ α₂ β₁ β₂) :
    (kernel.ι α₁ ≫ α₂) ≫ β₂ = 0 := by
  rw [Category.assoc, ← sq.w, kernel.condition_assoc, zero_comp]

variable (sq) in
/-- A commutative square is semi-cartesian if and only if the sequences `ker α₁ ⟶ a₂ ⟶ b`
(maps `kernel.ι α₁ ≫ α₂` and `β₂`) and `a ⟶ a₁ ⟶ coker β₂` (maps `α₁` and `β₁ ≫ cokernel.π β₂`)
are exact. -/
theorem isSemiCartesian_iff_exact_kernel_cokernel :
    IsSemiCartesian sq ↔
      (ShortComplex.mk _ _ (kernel_ι_comp_eq_zero sq)).Exact ∧
        (ShortComplex.mk _ _ (comp_cokernel_π_eq_zero sq)).Exact := by
  have hcok : (ShortComplex.mk _ _ (cokernel.condition β₂)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel β₂)
  constructor
  · intro hs
    constructor
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro T x₂ hx₂
      obtain ⟨T', π, hπ, y, h₁, h₂⟩ := hs.exists_lift 0 x₂ (by simpa using hx₂)
      refine ⟨T', π, hπ, -kernel.lift α₁ y (by simpa using h₁.symm), ?_⟩
      simpa using h₂
    · rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro T x₁ hx₁
      obtain ⟨T₁, π, hπ, z, hz⟩ := hcok.exact_up_to_refinements (x₁ ≫ β₁) (by simpa using hx₁)
      obtain ⟨T₂, π', hπ', y, h₁, -⟩ := hs.exists_lift (π ≫ x₁) (-z) (by simp [hz])
      exact ⟨T₂, π' ≫ π, epi_comp _ _, y, by simpa using h₁⟩
  · rintro ⟨hker, hcoker⟩
    refine IsSemiCartesian.of_lift fun T x₁ x₂ hx ↦ ?_
    have hx' : x₁ ≫ β₁ = -(x₂ ≫ β₂) := eq_neg_of_add_eq_zero_left hx
    obtain ⟨T₁, π, hπ, y, hy⟩ := hcoker.exact_up_to_refinements x₁ (by simp [reassoc_of% hx'])
    have hw : (π ≫ x₂ + y ≫ α₂) ≫ β₂ = 0 := by
      have := π ≫= hx
      rw [comp_add, ← Category.assoc, hy] at this
      simpa [← sq.w, add_comm] using this
    obtain ⟨T₂, π', hπ', k, hk⟩ := hker.exact_up_to_refinements _ hw
    refine ⟨T₂, π' ≫ π, epi_comp _ _, π' ≫ y - k ≫ kernel.ι α₁, ?_, ?_⟩
    · simp [hy]
    · have hk' : π' ≫ π ≫ x₂ = k ≫ kernel.ι α₁ ≫ α₂ - π' ≫ y ≫ α₂ := by
        rw [eq_sub_iff_add_eq, ← comp_add]
        simpa using hk
      simp [hk', sub_comp]

end CategoryTheory.CommSq
