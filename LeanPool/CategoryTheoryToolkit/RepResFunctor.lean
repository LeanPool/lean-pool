/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Restriction of representations: full iff surjective, an equivalence iff bijective

Mathlib proves that restriction `Rep.resFunctor f` along a group homomorphism `f : H →* G` is
faithful, and full when `f` is surjective (`Rep.full_res`). This file proves the converses, for
a nontrivial commutative ring `k`.

## Main statements

* `Rep.full_resFunctor_iff`: restriction is full iff `f` is surjective. The test object is the
  permutation representation `k[G ⧸ f(H)]`, whose projection onto the line of the base coset
  commutes with `H` but not with `G`;
* `Rep.injective_of_essSurj_resFunctor`: if restriction is essentially surjective, `f` is
  injective (test on the regular representation `k[H]`);
* `Rep.isEquivalence_resFunctor_iff`: restriction is an equivalence iff `f` is bijective.

The auxiliary test objects live in the namespace `Rep.ResFunctor`. The representations live in
the universe `max u v₁ v₂` (`k : Type u`, `G : Type v₁`, `H : Type v₂`), large enough to hold the
test objects; `ULift` moves them there.
-/

@[expose] public section

open CategoryTheory

universe u v₁ v₂

namespace Rep

variable {k : Type u} [CommRing k] {G : Type v₁} {H : Type v₂} [Group G] [Group H]

namespace ResFunctor

/-- The permutation representation `k[G ⧸ f(H)]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev cosetRep (f : H →* G) : Rep.{max u v₁ v₂} k G :=
  Rep.ofMulAction k G (ULift.{v₂} (G ⧸ f.range))

/-- The base coset `f(H)` as a point of `ULift (G ⧸ f(H))`. -/
abbrev baseCoset (f : H →* G) : ULift.{v₂} (G ⧸ f.range) := ⟨(1 : G)⟩

lemma smul_baseCoset (f : H →* G) (g : G) :
    g • baseCoset f = baseCoset f ↔ g ∈ f.range := by
  change (ULift.up ((g • ((1 : G) : G ⧸ f.range))) = ULift.up _) ↔ _
  rw [ULift.up_inj, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- The projection of `k[G ⧸ f(H)]` onto the line spanned by the base coset. -/
noncomputable def proj (f : H →* G) : (cosetRep (k := k) f).V →ₗ[k] (cosetRep (k := k) f).V :=
  (MonoidAlgebra.lsingle (baseCoset f)) ∘ₗ
    (Finsupp.lapply (baseCoset f)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

lemma proj_apply (f : H →* G) (x : (cosetRep (k := k) f).V) :
    proj f x = MonoidAlgebra.single (baseCoset f) (x.coeff (baseCoset f)) := rfl

/-- The projection onto the base coset commutes with the action of `H`. -/
lemma proj_comm (f : H →* G) (h : H) (x : (cosetRep (k := k) f).V) :
    proj f ((cosetRep (k := k) f).ρ (f h) x) = (cosetRep (k := k) f).ρ (f h) (proj f x) := by
  have h1 : f h • baseCoset f = baseCoset f := (smul_baseCoset f _).2 ⟨h, rfl⟩
  have h2 : (f h)⁻¹ • baseCoset f = baseCoset f := (smul_baseCoset f _).2 ⟨h⁻¹, by simp⟩
  rw [proj_apply, proj_apply, Representation.coeff_ofMulAction, h2,
    Representation.ofMulAction_single, h1]

/-- The projection onto the base coset, as an endomorphism of the restriction to `H`. -/
noncomputable def projHom (f : H →* G) :
    (Rep.resFunctor f).obj (cosetRep (k := k) f) ⟶ (Rep.resFunctor f).obj (cosetRep (k := k) f) :=
  Rep.ofHom ⟨proj f, fun h ↦ LinearMap.ext fun x ↦ proj_comm f h x⟩

/-- The regular representation `k[H]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev regRep (H : Type v₂) [Group H] : Rep.{max u v₁ v₂} k H :=
  Rep.ofMulAction k H (ULift.{v₁} H)

end ResFunctor

open ResFunctor

/-- If restriction along `f` is full, then `f` is surjective: the projection of `k[G ⧸ f(H)]`
onto the base coset is `H`-linear, and it is `G`-linear only if `f(H) = G`. -/
theorem surjective_of_full_resFunctor [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full] : Function.Surjective f := by
  obtain ⟨ψ, hψ⟩ := (Rep.resFunctor (k := k) f).map_surjective (projHom f)
  have hψx (x) : ψ.hom x = proj f x := by
    rw [← Rep.resMap_hom_apply f ψ x]
    exact congrArg (fun φ ↦ φ.hom x) hψ
  intro g
  have hc := Rep.hom_comm_apply ψ g (MonoidAlgebra.single (baseCoset f) 1)
  rw [hψx, hψx, proj_apply, proj_apply, Representation.ofMulAction_single] at hc
  by_contra hg
  have hne : g • baseCoset f ≠ baseCoset f := fun h ↦ hg ((smul_baseCoset f g).1 h)
  rw [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne.symm] at hc
  rw [MonoidAlgebra.single_zero, Representation.ofMulAction_single] at hc
  exact one_ne_zero (MonoidAlgebra.single_eq_zero.1 hc.symm)

/-- **Restriction is full iff the homomorphism is surjective.** The direction `←` is
`Rep.full_res`. -/
theorem full_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full ↔ Function.Surjective f :=
  ⟨fun _ ↦ surjective_of_full_resFunctor (k := k) f, Rep.full_res f⟩

/-- If every representation of `H` is, up to isomorphism, restricted from `G`, then `f` is
injective: the kernel of `f` acts trivially on a restriction, but faithfully on `k[H]`. -/
theorem injective_of_essSurj_resFunctor [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj] : Function.Injective f := by
  refine (injective_iff_map_eq_one f).2 fun h hh ↦ ?_
  set F := Rep.resFunctor.{max u v₁ v₂} (k := k) f
  let R : Rep.{max u v₁ v₂} k H := regRep.{u, v₁} H
  let e := F.objObjPreimageIso R
  let s : R.V := MonoidAlgebra.single ⟨1⟩ 1
  have hc := Rep.hom_comm_apply e.hom h (e.inv.hom s)
  have h1 : (F.obj (F.objPreimage R)).ρ h = LinearMap.id := by
    change (F.objPreimage _).ρ (f h) = _
    rw [hh, map_one]
    rfl
  rw [h1, LinearMap.id_apply, Rep.hom_inv_apply, Representation.ofMulAction_single] at hc
  have := congrArg ULift.down ((MonoidAlgebra.single_left_inj one_ne_zero).1 hc)
  simpa using this.symm

/-- For a bijective `f`, every representation of `H` is restricted from `G`: transport it along
the inverse isomorphism. -/
theorem essSurj_resFunctor_of_bijective (f : H →* G) (hf : Function.Bijective f) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj where
  mem_essImage Y := by
    let e := MulEquiv.ofBijective f hf
    refine ⟨Rep.of (Y.ρ.comp e.symm.toMonoidHom), ⟨Rep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl k Y.V) fun h ↦ ?_)⟩⟩
    ext y
    change Y.ρ (e.symm (e h)) y = Y.ρ h y
    rw [MulEquiv.symm_apply_apply]

/-- **Restriction is an equivalence iff the homomorphism is bijective.** -/
theorem isEquivalence_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).IsEquivalence ↔ Function.Bijective f := by
  refine ⟨fun _ ↦ ⟨injective_of_essSurj_resFunctor (k := k) f,
    surjective_of_full_resFunctor (k := k) f⟩, fun hf ↦ ?_⟩
  have := Rep.full_res (k := k) f hf.2
  have := essSurj_resFunctor_of_bijective (k := k) f hf
  exact { }

end Rep
