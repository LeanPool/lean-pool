/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Cancellation
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneTransitivity

/-!
# Witt cancellation over LG rings (`GN 6.5`, `GPR 11.27`)

The capstone of Layer 0. `QuadraticForm/PlaneTransitivity.lean` cancels **one** hyperbolic plane;
this file passes from there to `QuadraticForm.dualProd R N` for an arbitrary finitely generated
projective `N`, and then to `GN 6.5` by way of the reduction in `QuadraticForm/Cancellation.lean`.

## The route

1. `dualProd R (Fin 0 → R)` is the form on a trivial module, so it can simply be dropped
   (`QuadraticMap.IsometryEquiv.prodOfSubsingletonLeft`).
2. `dualProd R R ≅ plane R` (`QuadraticForm.isometryEquivPlane`) and
   `dualProd R (M × N) ≅ dualProd R M ⊥ dualProd R N`
   (mathlib's `QuadraticForm.dualProdProdIsometry`). Together with
   `Fin (n+1) → R ≃ₗ R × (Fin n → R)` these turn `dualProd R (Fin n → R)` into `n` planes, so
   `n` applications of `QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing`
   cancel it — `QuadraticForm.cancel_dualProd_fin`.
3. A finitely generated projective `N` is a direct summand of some `Rⁿ`
   (`QuadraticForm.exists_linearEquiv_prod_submodule`). Adding `dualProd R N'` for a complement `N'`
   to both sides of `dualProd R N ⊥ q₁ ≅ dualProd R N ⊥ q₂` turns it into the free case —
   `QuadraticForm.cancel_dualProd`. Note `N'` needs no hypotheses whatever: it is only ever fed
   to `dualProd`, which is defined for every module.
4. `QuadraticForm.cancel` is `GN 6.5`, obtained from `cancel_dualProd` and
   `QuadraticForm.isometryEquiv_prod_dualProd_of_isometryEquiv_prod`.

Note where the hypotheses are consumed. Non-singularity is asked of `q₂` only, since the plane
cancellation of step 2 needs the *second* summand non-singular at each stage; `GN 6.5` also lists
`q₁`, which is redundant (it follows from the others — see `QuadraticForm/Cancellation.lean`).
Regularity — as opposed to non-singularity — is used exactly once, on `q₃`, in the reduction of
step 4, and `GN`'s counterexample (see `QuadraticForm/Cancellation.lean`) shows it cannot be
dropped there.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, 6.5.
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.27.
* I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de Campinas,
  1988, II.6.4.
-/

@[expose] public section

universe u v v₁ v₂ v₃

namespace QuadraticMap.IsometryEquiv

variable {R : Type u} [CommRing R] {M₁ : Type v₁} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type v₂} [AddCommGroup M₂] [Module R M₂]

/-- A summand on a trivial module can be dropped from an orthogonal sum. -/
noncomputable def prodOfSubsingletonLeft (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    [Subsingleton M₁] : (Q₁.prod Q₂).IsometryEquiv Q₂ where
  __ := LinearEquiv.ofBijective (LinearMap.snd R M₁ M₂)
    ⟨fun x y h ↦ Prod.ext (Subsingleton.elim _ _) h, fun y ↦ ⟨(0, y), rfl⟩⟩
  map_app' x := by
    have h : Q₁ x.1 = 0 := by rw [Subsingleton.elim x.1 0, map_zero]
    rw [QuadraticMap.prod_apply, h, zero_add]
    rfl

end QuadraticMap.IsometryEquiv

namespace QuadraticForm

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v₁} [AddCommGroup N] [Module R N]

/-! ### The hyperbolic form of `Rⁿ` -/

/-- **`dualProd R R` is the hyperbolic plane.** Evaluation at `1` identifies `R*` with `R`. -/
noncomputable def isometryEquivPlane : (dualProd R R).IsometryEquiv (plane R) where
  __ := (LinearMap.ringLmapEquivSelf R R R).prodCongr (LinearEquiv.refl R R)
  map_app' x := by
    change x.1 1 * x.2 = x.1 x.2
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- Splitting off the first coordinate: `dualProd R (Rⁿ⁺¹) ≅ plane ⊥ dualProd R (Rⁿ)`. -/
noncomputable def isometryEquivDualProdFinSucc (R : Type u) [CommRing R] (k : ℕ) :
    (dualProd R (Fin (k + 1) → R)).IsometryEquiv
      ((plane R).prod (dualProd R (Fin k → R))) :=
  (dualProdIsometry (Fin.consLinearEquiv R (fun _ : Fin (k + 1) ↦ R)).symm).trans
    ((dualProdProdIsometry (M := R) (N := Fin k → R)).trans
      (QuadraticMap.IsometryEquiv.prod isometryEquivPlane (QuadraticMap.IsometryEquiv.refl _)))

/-! ### Cancelling a hyperbolic form -/

variable {M₁ : Type v₁} [AddCommGroup M₁] [Module R M₁] {M₂ : Type v₂}
  [AddCommGroup M₂]
  [Module R M₂]

/-- **Cancellation of `dualProd R (Rⁿ)` over an LG ring**, by induction on `n`: strip off one
plane at a time with `isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing`.

At the `k`-th stage the form being cancelled against is `dualProd R (Rᵏ) ⊥ q₂`, non-singular by
`GN (C.8.3)` since the hyperbolic summand is *regular*; that is why the hyperbolic form is kept on
the left. Nothing is assumed about `q₁`. -/
theorem cancel_dualProd_fin (hLG : IsLGRing R) [Module.Finite R M₂] [Module.Projective R M₂]
    {q₁ : QuadraticForm R M₁} {q₂ : QuadraticForm R M₂}
    (h₂ : q₂.IsGPRNonsingular.{u, v₂, u})
    (n : ℕ) (h : Nonempty (((dualProd R (Fin n → R)).prod q₁).IsometryEquiv
      ((dualProd R (Fin n → R)).prod q₂))) :
    Nonempty (q₁.IsometryEquiv q₂) := by
  induction n with
  | zero =>
    have : Subsingleton (Module.Dual R (Fin 0 → R)) :=
      ⟨fun f g ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    obtain ⟨e⟩ := h
    exact ⟨(((QuadraticMap.IsometryEquiv.prodOfSubsingletonLeft _ q₁).symm.trans e).trans
      (QuadraticMap.IsometryEquiv.prodOfSubsingletonLeft _ q₂))⟩
  | succ k ih =>
    obtain ⟨e⟩ := h
    set Hk := dualProd R (Fin k → R) with hHk
    -- reassociate `H(Rᵏ⁺¹) ⊥ q` as `plane ⊥ (H(Rᵏ) ⊥ q)`
    let step₁ : (((plane R).prod (Hk.prod q₁))).IsometryEquiv
        (((dualProd R (Fin (k + 1) → R)).prod q₁)) :=
      (QuadraticMap.IsometryEquiv.prodAssoc (plane R) Hk q₁).symm.trans
        (QuadraticMap.IsometryEquiv.prod (isometryEquivDualProdFinSucc R k).symm
          (QuadraticMap.IsometryEquiv.refl q₁))
    let step₂ : (((plane R).prod (Hk.prod q₂))).IsometryEquiv
        (((dualProd R (Fin (k + 1) → R)).prod q₂)) :=
      (QuadraticMap.IsometryEquiv.prodAssoc (plane R) Hk q₂).symm.trans
        (QuadraticMap.IsometryEquiv.prod (isometryEquivDualProdFinSucc R k).symm
          (QuadraticMap.IsometryEquiv.refl q₂))
    have e' : ((plane R).prod (Hk.prod q₁)).IsometryEquiv ((plane R).prod (Hk.prod q₂)) :=
      (step₁.trans e).trans step₂.symm
    refine ih (isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing
      (q₁ := Hk.prod q₁) (q₂ := Hk.prod q₂) hLG ?_ ⟨e'⟩)
    exact (isGPRRegular_dualProd R (Fin k → R)).prod_isGPRNonsingular h₂

/-- **A finitely generated projective module is a direct summand of `Rⁿ`.** The complement is
produced as a submodule of `Rⁿ`, so that no auxiliary type has to be introduced. -/
theorem exists_linearEquiv_prod_submodule (N : Type v₁) [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    ∃ (n : ℕ) (N' : Submodule R (Fin n → R)),
      Nonempty ((N × N') ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R N
  obtain ⟨i, hi⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hsec : ∀ x : N, π (i x) = x := fun x ↦ DFunLike.congr_fun hi x
  have hinj : Function.Injective i := fun a b hab ↦ by rw [← hsec a, ← hsec b, hab]
  set p : (Fin n → R) →ₗ[R] LinearMap.range i :=
    (i.comp π).codRestrict (LinearMap.range i)
      (fun x ↦ LinearMap.mem_range_self i (π x)) with hp
  have hproj : ∀ y : LinearMap.range i, p y = y := by
    rintro ⟨-, z, rfl⟩
    exact Subtype.ext (congrArg i (hsec z))
  refine ⟨n, LinearMap.ker p, ⟨?_⟩⟩
  exact ((LinearEquiv.ofInjective i hinj).prodCongr (LinearEquiv.refl R (LinearMap.ker p))).trans
    (Submodule.prodEquivOfIsCompl _ _ (LinearMap.isCompl_of_proj hproj))

/-- **Cancellation of a hyperbolic form over an LG ring.** For `N` finitely generated projective
and `q₂` non-singular, `dualProd R N ⊥ q₁ ≅ dualProd R N ⊥ q₂` implies `q₁ ≅ q₂`.

Choose a complement `N'` with `N × N' ≅ Rⁿ` and add `dualProd R N'` to both sides: since
`dualProd R (N × N') ≅ dualProd R N ⊥ dualProd R N'`, this turns the hypothesis into one
about `dualProd R (Rⁿ)`, which `cancel_dualProd_fin` handles. `N'` carries no hypotheses —
it is only ever fed to `dualProd`, which every module has. -/
theorem cancel_dualProd (hLG : IsLGRing R) {N : Type v₃} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] [Module.Finite R M₂] [Module.Projective R M₂]
    {q₁ : QuadraticForm R M₁} {q₂ : QuadraticForm R M₂}
    (h₂ : q₂.IsGPRNonsingular.{u, v₂, u})
    (h : Nonempty (((dualProd R N).prod q₁).IsometryEquiv ((dualProd R N).prod q₂))) :
    Nonempty (q₁.IsometryEquiv q₂) := by
  obtain ⟨n, N', ⟨eN⟩⟩ := exists_linearEquiv_prod_submodule (R := R) N
  obtain ⟨e⟩ := h
  -- `H(Rⁿ) ⊥ q ≅ H(N') ⊥ (H(N) ⊥ q)`, so `e` can be applied inside
  let swap₁ : ((dualProd R (Fin n → R)).prod q₁).IsometryEquiv
      ((dualProd R N').prod ((dualProd R N).prod q₁)) :=
    ((QuadraticMap.IsometryEquiv.prod (dualProdIsometry eN.symm)
      (QuadraticMap.IsometryEquiv.refl q₁)).trans
      ((QuadraticMap.IsometryEquiv.prod (dualProdProdIsometry (M := N) (N := N'))
        (QuadraticMap.IsometryEquiv.refl q₁)).trans
        ((QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.prodComm _ _)
          (QuadraticMap.IsometryEquiv.refl q₁)).trans
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _))))
  let swap₂ : ((dualProd R (Fin n → R)).prod q₂).IsometryEquiv
      ((dualProd R N').prod ((dualProd R N).prod q₂)) :=
    ((QuadraticMap.IsometryEquiv.prod (dualProdIsometry eN.symm)
      (QuadraticMap.IsometryEquiv.refl q₂)).trans
      ((QuadraticMap.IsometryEquiv.prod (dualProdProdIsometry (M := N) (N := N'))
        (QuadraticMap.IsometryEquiv.refl q₂)).trans
        ((QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.prodComm _ _)
          (QuadraticMap.IsometryEquiv.refl q₂)).trans
          (QuadraticMap.IsometryEquiv.prodAssoc _ _ _))))
  refine cancel_dualProd_fin hLG h₂ n ⟨swap₁.trans (((QuadraticMap.IsometryEquiv.prod
    (QuadraticMap.IsometryEquiv.refl (dualProd R N')) e)).trans swap₂.symm)⟩

/-- **Witt cancellation over an LG ring** (`GN 6.5`; cf. `GPR 11.27`). If `q₃` is **regular** and
`q₂` is non-singular, then `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃` implies `q₁ ≅ q₂`.

Adding `-q₃` turns `q₃` into a hyperbolic form
(`QuadraticForm.isometryEquiv_prod_dualProd_of_isometryEquiv_prod`), which `cancel_dualProd`
cancels. Regularity of `q₃` is consumed in that first step and nowhere else; it cannot be weakened
to non-singularity (`EKM`, p. 49 — see `QuadraticForm/Cancellation.lean`).

`GN` also lists `q₁` non-singular. It is not carried here because it is implied: `q₂ ⊥ q₃` is
non-singular, hence so is `q₁ ⊥ q₃`, hence so is `q₁`
(`QuadraticForm.IsGPRNonsingular.of_prod_left`). -/
theorem cancel (hLG : IsLGRing R) {M₃ : Type v₃} [AddCommGroup M₃] [Module R M₃]
    [Module.Finite R M₃] [Module.Projective R M₃]
    [Module.Finite R M₂] [Module.Projective R M₂]
    {q₁ : QuadraticForm R M₁} {q₂ : QuadraticForm R M₂} {q₃ : QuadraticForm R M₃}
    (h₂ : q₂.IsGPRNonsingular.{u, v₂, u}) (h₃ : q₃.IsGPRRegular)
    (h : Nonempty ((q₁.prod q₃).IsometryEquiv (q₂.prod q₃))) :
    Nonempty (q₁.IsometryEquiv q₂) := by
  obtain ⟨e⟩ := isometryEquiv_prod_dualProd_of_isometryEquiv_prod h₃ h
  exact cancel_dualProd hLG h₂
    ⟨((QuadraticMap.IsometryEquiv.prodComm _ _).trans e).trans
      (QuadraticMap.IsometryEquiv.prodComm _ _)⟩

end QuadraticForm
