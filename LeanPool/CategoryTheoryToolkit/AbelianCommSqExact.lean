/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Pullbacks, pushouts and exact sequences in abelian categories

For a commutative square `CommSq t l r b` of an abelian category, Mathlib has the exactness of
the sequences `X₁ → X₂ ⊞ X₃ → X₄` attached to a pullback (`IsPullback.exact_shortComplex'`) and
to a pushout (`IsPushout.exact_shortComplex`). This file proves the converses and their
consequences.

## Main statements

* `Limits.biprod.negRightIso`, `CommSq.shortComplex'IsoShortComplex`: the two short complexes of
  a commutative square differ by the sign automorphism of the biproduct;
* `CommSq.isPullback_iff_exact`, `CommSq.isPushout_iff_exact`: a square is a pullback (pushout)
  iff `0 → X₁ → X₂ ⊞ X₃ → X₄` (`X₁ → X₂ ⊞ X₃ → X₄ → 0`) is exact;
* `IsPullback.isPushout_of_epi_bottom` (Stacks 08N4), `IsPullback.isPushout_of_epi_right` and
  `IsPushout.isPullback_of_mono_top`, `IsPushout.isPullback_of_mono_left`: a pullback square
  with an epimorphism opposite is a pushout, and dually;
* `ShortComplex.exact_of_isPullback_of_epi`: a row mapped by an epimorphism on the left and a
  cartesian square on the right into an exact row is exact.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- The automorphism of `A ⊞ B` that is the identity on `A` and `-1` on `B`. -/
@[simps]
noncomputable def Limits.biprod.negRightIso (A B : C) : A ⊞ B ≅ A ⊞ B where
  hom := biprod.map (𝟙 A) (-𝟙 B)
  inv := biprod.map (𝟙 A) (-𝟙 B)

/-- The two short complexes attached to a commutative square, the pullback one
`X₁ → X₂ ⊞ X₃ → X₄` with maps `(t, l)` and `r - b` and the pushout one with maps `(t, -l)` and
`r + b`, are isomorphic through the sign automorphism of the biproduct. -/
@[simps!]
noncomputable def CommSq.shortComplex'IsoShortComplex (sq : CommSq t l r b) :
    sq.shortComplex' ≅ sq.shortComplex :=
  ShortComplex.isoMk (Iso.refl _) (biprod.negRightIso X₂ X₃) (Iso.refl _)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; apply biprod.hom_ext <;> simp)
    (by dsimp [CommSq.shortComplex, CommSq.shortComplex']; apply biprod.hom_ext' <;> simp)

/-- A commutative square whose sequence `0 → X₁ → X₂ ⊞ X₃ → X₄` is exact is a pullback. -/
theorem CommSq.isPullback_of_exact (sq : CommSq t l r b) (h : sq.shortComplex'.Exact)
    [Mono sq.shortComplex'.f] : IsPullback t l r b :=
  ⟨sq, ⟨sq.isLimitEquivIsLimitKernelFork.symm h.fIsKernel⟩⟩

/-- A commutative square is a pullback iff `0 → X₁ → X₂ ⊞ X₃ → X₄` is exact. -/
theorem CommSq.isPullback_iff_exact (sq : CommSq t l r b) :
    IsPullback t l r b ↔ sq.shortComplex'.Exact ∧ Mono sq.shortComplex'.f :=
  ⟨fun h ↦ ⟨h.exact_shortComplex', h.mono_shortComplex'_f⟩,
    fun ⟨h, _⟩ ↦ sq.isPullback_of_exact h⟩

/-- A commutative square whose sequence `X₁ → X₂ ⊞ X₃ → X₄ → 0` is exact is a pushout. -/
theorem CommSq.isPushout_of_exact (sq : CommSq t l r b) (h : sq.shortComplex.Exact)
    [Epi sq.shortComplex.g] : IsPushout t l r b :=
  ⟨sq, ⟨sq.isColimitEquivIsColimitCokernelCofork.symm h.gIsCokernel⟩⟩

/-- A commutative square is a pushout iff `X₁ → X₂ ⊞ X₃ → X₄ → 0` is exact. -/
theorem CommSq.isPushout_iff_exact (sq : CommSq t l r b) :
    IsPushout t l r b ↔ sq.shortComplex.Exact ∧ Epi sq.shortComplex.g :=
  ⟨fun h ↦ ⟨h.exact_shortComplex, h.epi_shortComplex_g⟩,
    fun ⟨h, _⟩ ↦ sq.isPushout_of_exact h⟩

/-- A pullback square in which `b` is an epimorphism is a pushout square (Stacks 08N4). -/
theorem IsPullback.isPushout_of_epi_bottom (h : IsPullback t l r b) [Epi b] :
    IsPushout t l r b := by
  have hg : Epi h.toCommSq.shortComplex.g :=
    @epi_of_epi_fac _ _ _ _ _ biprod.inr _ b ‹_› (biprod.inr_desc _ _)
  exact h.toCommSq.isPushout_of_exact
    ((ShortComplex.exact_iff_of_iso h.toCommSq.shortComplex'IsoShortComplex).1
      h.exact_shortComplex')

/-- A pullback square in which `r` is an epimorphism is a pushout square. -/
theorem IsPullback.isPushout_of_epi_right (h : IsPullback t l r b) [Epi r] :
    IsPushout t l r b :=
  h.flip.isPushout_of_epi_bottom.flip

/-- A pushout square in which `l` is a monomorphism is a pullback square. -/
theorem IsPushout.isPullback_of_mono_left (h : IsPushout t l r b) [Mono l] :
    IsPullback t l r b := by
  have hf : Mono h.toCommSq.shortComplex'.f :=
    @mono_of_mono_fac _ _ _ _ _ _ _ l ‹_› (biprod.lift_snd _ _)
  exact h.toCommSq.isPullback_of_exact
    ((ShortComplex.exact_iff_of_iso h.toCommSq.shortComplex'IsoShortComplex).2
      h.exact_shortComplex)

/-- A pushout square in which `t` is a monomorphism is a pullback square. -/
theorem IsPushout.isPullback_of_mono_top (h : IsPushout t l r b) [Mono t] :
    IsPullback t l r b :=
  h.flip.isPullback_of_mono_left.flip

/-- In a commutative diagram
```
 a₀ ──φ₀──▶ b₀ ──ξ₀──▶ c₀
 │α         │β         │γ
 ▼          ▼          ▼
 a₁ ──φ₁──▶ b₁ ──ξ₁──▶ c₁
```
with `α` epi, the right square cartesian, `φ₀ ≫ ξ₀ = 0` and the bottom row exact, the top row
is exact. -/
theorem ShortComplex.exact_of_isPullback_of_epi {a₀ b₀ c₀ a₁ b₁ c₁ : C} {φ₀ : a₀ ⟶ b₀}
    {ξ₀ : b₀ ⟶ c₀} {φ₁ : a₁ ⟶ b₁} {ξ₁ : b₁ ⟶ c₁} {α : a₀ ⟶ a₁} {β : b₀ ⟶ b₁} {γ : c₀ ⟶ c₁}
    (wl : φ₀ ≫ β = α ≫ φ₁) (hI : IsPullback ξ₀ β γ ξ₁) [Epi α] (h₀ : φ₀ ≫ ξ₀ = 0)
    (h₁ : φ₁ ≫ ξ₁ = 0) (hex : (ShortComplex.mk φ₁ ξ₁ h₁).Exact) :
    (ShortComplex.mk φ₀ ξ₀ h₀).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  dsimp at x hx ⊢
  have hxβ : (x ≫ β) ≫ ξ₁ = 0 := by
    rw [Category.assoc, ← hI.w, ← Category.assoc, hx, zero_comp]
  obtain ⟨A₁, π₁, _, y, hy⟩ := hex.exact_up_to_refinements (x ≫ β) hxβ
  obtain ⟨A₂, π₂, _, z, hz⟩ := surjective_up_to_refinements_of_epi α y
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z, ?_⟩
  dsimp at hy ⊢
  apply hI.hom_ext
  · simp [hx, h₀]
  · simp only [Category.assoc]
    rw [hy, reassoc_of% hz, wl]

end CategoryTheory
