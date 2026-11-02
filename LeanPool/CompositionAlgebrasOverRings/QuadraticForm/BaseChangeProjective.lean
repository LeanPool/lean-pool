/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of quadratic maps along `R → A`, without inverting `2`

Mathlib's `QuadraticForm.baseChange` is built as a special case of the *tensor product* of two
quadratic forms, which is constructed by passing to associated symmetric bilinear forms and
therefore carries an `Invertible (2 : R)` hypothesis.  That hypothesis is an artefact of the
construction: base change of a quadratic form exists over an arbitrary commutative ring.
Uniqueness is already unconditional in mathlib (`baseChange_ext`); only existence needs work.

This file supplies the missing existence, for `M` a finitely generated projective `R`-module,
by the classical device of choosing a (not necessarily symmetric) *bilinear representative*
`B` with `B x x = Q x`, base changing `B` (which is unconditional, `LinearMap.BilinMap.baseChange`)
and taking the diagonal.  The choice of `B` is non-canonical, but the result is independent of it
by `baseChange_ext`.

## Main definitions

* `QuadraticMap.HasBilinRepr R M N`: every quadratic map `M → N` is of the form `x ↦ B x x`.
* `QuadraticMap.bilinRepr Q`: a chosen bilinear representative of `Q`, for `M` f.g. projective.
* `QuadraticMap.baseChange A Q : QuadraticMap A (A ⊗[R] M) (A ⊗[R] N)`.
* `QuadraticForm.baseChangeOfProjective A Q : QuadraticForm A (A ⊗[R] M)`.

## Main results

* `QuadraticMap.exists_bilinMap`: for `M` finitely generated projective, `toQuadraticMap` is
  surjective, i.e. every quadratic map is `x ↦ B x x` for some bilinear `B`.
* `QuadraticMap.baseChange_tmul`, `QuadraticForm.baseChangeOfProjective_tmul`: the defining
  property `Q_A (a ⊗ₜ m) = (a * a) ⊗ₜ Q m` (resp. `Q m • (a * a)`).
* `QuadraticMap.baseChange_eq_of_toQuadraticMap_eq`: independence of the chosen representative.
* `QuadraticMap.polarBilin_baseChange`, `QuadraticForm.polarBilin_baseChangeOfProjective`:
  the polar form of the base change is the base change of the polar form — with *no* hypothesis
  on `2`, unlike `QuadraticForm.polarBilin_baseChange`.
* `QuadraticForm.baseChangeOfProjective_eq_baseChange`: agreement with mathlib's
  `QuadraticForm.baseChange` when `2` is invertible.
* `QuadraticMap.IsometryEquiv.baseChangeOfProjective`: base change of an isometry.
* `QuadraticForm.anisotropic_baseChangeOfProjective_iff_of_isLocalization`,
  `QuadraticForm.anisotropic_baseChangeOfProjective_iff_of_isFractionRing`: `GPR Exc. 12.38(b)` —
  anisotropy is unchanged by localizing at non-zero-divisors, in particular by passing to the
  fraction field.

## Implementation notes

A bilinear representative exists on every free module: that is mathlib's
`LinearMap.BilinMap.toQuadraticMap_surjective`. A finitely generated projective module is a
retract of some `Fin n → R`, and representatives transport along retracts
(`QuadraticMap.HasBilinRepr.of_retract`), which gives the projective case.

`QuadraticForm` and `LinearMap.BilinForm` are `abbrev`s for `QuadraticMap R M R` and
`LinearMap.BilinMap R M R`, so dot notation such as `Q.baseChange A` can resolve ambiguously
against mathlib's `QuadraticForm.baseChange`.  Names are therefore fully qualified throughout,
and the `QuadraticForm`-valued construction is given a distinct name.

## TODO

* Drop the projectivity hypothesis entirely by constructing base change through the divided
  square `Γ₂(M)` (Roby). mathlib now has the divided power algebra `DividedPowerAlgebra R M` and
  polynomial laws `PolynomialLaw`, but not yet `Γ₂(M)` as the universal quadratic map, nor any link
  from either to `QuadraticMap`.

## References

* overview §6(a): the mandatory warning this file exists to satisfy — `QuadraticMap.associated`
  and hence mathlib's `QuadraticForm.baseChange` assume `2 ∈ Rˣ`, which is unusable for the
  characteristic-2 examples (`GPR 19.4`) this development needs to state.
* GN's definition of non-singularity (`QuadraticForm/Regularity.lean`) needs base change along
  finitely generated projective modules specifically — matching this file's hypothesis exactly.
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 12.38.
-/

@[expose] public section

open scoped TensorProduct
open LinearMap (BilinMap BilinForm)

universe uR uA uM uN

namespace QuadraticMap

/-! ### Bilinear representatives -/

section HasBilinRepr

variable (R : Type uR) (M : Type uM) (N : Type uN)
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `HasBilinRepr R M N` says that every quadratic map `Q : M → N` is the diagonal of some
bilinear map, i.e. `LinearMap.BilinMap.toQuadraticMap` is surjective.

Beware the clash of terminology with `QuadraticMap.exists_companion`, whose companion `B`
satisfies `Q (x + y) = Q x + Q y + B x y` (so that `B x x = 2 • Q x`).  Here we ask instead for
`B x x = Q x`, which is a genuine extra condition in characteristic two. -/
def HasBilinRepr : Prop :=
  Function.Surjective (LinearMap.BilinMap.toQuadraticMap : BilinMap R M N → QuadraticMap R M N)

variable {R M N}

theorem apply_self_of_toQuadraticMap_eq {B : BilinMap R M N} {Q : QuadraticMap R M N}
    (hB : B.toQuadraticMap = Q) (x : M) : B x x = Q x :=
  QuadraticMap.congr_fun hB x

/-- Transport along a retract: if `M` is a direct summand of `P` (witnessed by `r ∘ₗ i = id`)
and every quadratic map on `P` has a bilinear representative, then so does every quadratic map
on `M`. -/
theorem HasBilinRepr.of_retract {P : Type*} [AddCommGroup P] [Module R P]
    (h : HasBilinRepr R P N) (i : M →ₗ[R] P) (r : P →ₗ[R] M)
    (hir : r ∘ₗ i = LinearMap.id) : HasBilinRepr R M N := by
  intro Q
  obtain ⟨B, hB⟩ := h (Q.comp r)
  refine ⟨B.compl₁₂ i i, QuadraticMap.ext fun x ↦ ?_⟩
  have hx : r (i x) = x := by simpa using DFunLike.congr_fun hir x
  rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₁₂_apply,
    apply_self_of_toQuadraticMap_eq hB (i x),
    QuadraticMap.comp_apply, hx]

variable (R M N) in
/-- **Existence of bilinear representatives over finitely generated projective modules.**
Every finitely generated projective module is a retract of some `Fin n → R`, which is free, and
on a free module every quadratic map has a bilinear representative
(`LinearMap.BilinMap.toQuadraticMap_surjective`). -/
theorem hasBilinRepr_of_projective [Module.Finite R M] [Module.Projective R M] :
    HasBilinRepr R M N := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  exact HasBilinRepr.of_retract LinearMap.BilinMap.toQuadraticMap_surjective g f hg

/-- For `M` finitely generated projective, `LinearMap.BilinMap.toQuadraticMap` is surjective:
every quadratic map is `x ↦ B x x` for some, generally non-symmetric, bilinear `B`.

This is the characteristic-free replacement for `QuadraticMap.associated`, which requires `2`
to be invertible in order to pick out the *symmetric* representative. -/
theorem exists_bilinMap [Module.Finite R M] [Module.Projective R M] (Q : QuadraticMap R M N) :
    ∃ B : BilinMap R M N, B.toQuadraticMap = Q :=
  hasBilinRepr_of_projective R M N Q

variable [Module.Finite R M] [Module.Projective R M]

/-- A choice of bilinear representative of `Q`.  Non-canonical: only its diagonal is determined
(see `toQuadraticMap_bilinRepr`).  Every construction below is proved to be independent of this
choice. -/
noncomputable def bilinRepr (Q : QuadraticMap R M N) : BilinMap R M N :=
  (exists_bilinMap Q).choose

@[simp]
theorem toQuadraticMap_bilinRepr (Q : QuadraticMap R M N) :
    (bilinRepr Q).toQuadraticMap = Q :=
  (exists_bilinMap Q).choose_spec

@[simp]
theorem bilinRepr_apply_self (Q : QuadraticMap R M N) (x : M) : bilinRepr Q x x = Q x :=
  apply_self_of_toQuadraticMap_eq (toQuadraticMap_bilinRepr Q) x

end HasBilinRepr

/-! ### An extensionality lemma for bilinear maps on a base changed module -/

section BilinExt

variable {R : Type uR} {A : Type uA} {M : Type uM}
variable [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- Bilinear maps on `A ⊗[R] M` are determined by their values on pure tensors `1 ⊗ₜ m`.
Compare `baseChange_ext` for quadratic maps. -/
theorem bilin_ext_of_tmul {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    ⦃B₁ B₂ : BilinMap A (A ⊗[R] M) N₁⦄
    (h : ∀ m m' : M,
      B₁ (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] m') = B₂ (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] m')) :
    B₁ = B₂ := by
  have key : ∀ (a a' : A) (m m' : M),
      B₁ (a ⊗ₜ[R] m) (a' ⊗ₜ[R] m') = B₂ (a ⊗ₜ[R] m) (a' ⊗ₜ[R] m') := by
    intro a a' m m'
    have ha : (a ⊗ₜ[R] m : A ⊗[R] M) = a • (1 ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have ha' : (a' ⊗ₜ[R] m' : A ⊗[R] M) = a' • (1 ⊗ₜ[R] m') := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [ha, ha', map_smul, LinearMap.smul_apply, h]
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  induction x with
  | tmul a m =>
    induction y with
    | tmul a' m' => exact key a a' m m'
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

end BilinExt

/-! ### Base change of quadratic maps -/

section BaseChange

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M]

variable (A) in
/-- **Base change of a quadratic map** along an algebra map `R → A`, for `M` a finitely generated
projective `R`-module.  No invertibility of `2` is required.

Concretely this is the unique quadratic map with `Q_A (a ⊗ₜ m) = (a * a) ⊗ₜ Q m`; uniqueness
is `baseChange_ext`, and independence of the auxiliary choice is
`baseChange_eq_of_toQuadraticMap_eq`. -/
noncomputable def baseChange (Q : QuadraticMap R M N) :
    QuadraticMap A (A ⊗[R] M) (A ⊗[R] N) :=
  ((bilinRepr Q).baseChange A).toQuadraticMap

@[simp]
theorem baseChange_tmul (Q : QuadraticMap R M N) (a : A) (m : M) :
    baseChange A Q (a ⊗ₜ[R] m) = (a * a) ⊗ₜ[R] Q m := by
  rw [baseChange, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.baseChange_tmul, bilinRepr_apply_self]

/-- The base change does not depend on the choice of bilinear representative: *any* bilinear
`B` with `B x x = Q x` computes it. -/
theorem baseChange_eq_of_toQuadraticMap_eq (Q : QuadraticMap R M N) {B : BilinMap R M N}
    (hB : B.toQuadraticMap = Q) :
    baseChange A Q = (B.baseChange A).toQuadraticMap := by
  refine baseChange_ext fun m ↦ ?_
  rw [baseChange_tmul, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.baseChange_tmul, apply_self_of_toQuadraticMap_eq hB]

/-- Characterisation of the base change: it is the unique quadratic map on `A ⊗[R] M` taking the
value `(a * a) ⊗ₜ Q m` on pure tensors. -/
theorem baseChange_eq_iff (Q : QuadraticMap R M N)
    (Q' : QuadraticMap A (A ⊗[R] M) (A ⊗[R] N)) :
    Q' = baseChange A Q ↔ ∀ m : M, Q' (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] Q m := by
  constructor
  · rintro rfl m
    rw [baseChange_tmul, mul_one]
  · intro h
    refine baseChange_ext fun m ↦ ?_
    rw [h, baseChange_tmul, mul_one]

/-- The polar form of the base change is the base change of the polar form.  Unlike
`QuadraticForm.polarBilin_baseChange`, this needs no hypothesis on `2`. -/
theorem polarBilin_baseChange (Q : QuadraticMap R M N) :
    QuadraticMap.polarBilin (baseChange A Q) =
      (QuadraticMap.polarBilin Q).baseChange A := by
  refine bilin_ext_of_tmul fun m m' ↦ ?_
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    LinearMap.BilinMap.baseChange_tmul, ← TensorProduct.tmul_add, baseChange_tmul, mul_one,
    ← TensorProduct.tmul_sub]

end BaseChange

end QuadraticMap

/-! ### Base change of quadratic forms -/

namespace QuadraticForm

variable {R : Type uR} {A : Type uA} {M : Type uM}
variable [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

variable (A) in
/-- **Base change of a quadratic form** along `R → A`, for `M` finitely generated projective.

This agrees with mathlib's `QuadraticForm.baseChange` whenever the latter is defined
(`baseChangeOfProjective_eq_baseChange`) but, unlike it, does not require `2` to be invertible.
It is stated separately from `QuadraticMap.baseChange` so as to land in
`QuadraticForm A (A ⊗[R] M)` rather than `QuadraticMap A (A ⊗[R] M) (A ⊗[R] R)`. -/
noncomputable def baseChangeOfProjective (Q : QuadraticForm R M) : QuadraticForm A (A ⊗[R] M) :=
  (LinearMap.BilinForm.baseChange A (QuadraticMap.bilinRepr Q)).toQuadraticMap

@[simp]
theorem baseChangeOfProjective_tmul (Q : QuadraticForm R M) (a : A) (m : M) :
    baseChangeOfProjective A Q (a ⊗ₜ[R] m) = Q m • (a * a) := by
  rw [baseChangeOfProjective, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.baseChange_tmul, QuadraticMap.bilinRepr_apply_self]

theorem baseChangeOfProjective_eq_of_toQuadraticMap_eq (Q : QuadraticForm R M)
    {B : BilinForm R M} (hB : B.toQuadraticMap = Q) :
    baseChangeOfProjective A Q = (B.baseChange A).toQuadraticMap := by
  refine baseChange_ext fun m ↦ ?_
  rw [baseChangeOfProjective_tmul, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.baseChange_tmul, QuadraticMap.apply_self_of_toQuadraticMap_eq hB]

/-- The polar form of the base change is the base change of the polar form, with no hypothesis
on `2`. -/
theorem polarBilin_baseChangeOfProjective (Q : QuadraticForm R M) :
    QuadraticMap.polarBilin (baseChangeOfProjective A Q) =
      LinearMap.BilinForm.baseChange A (QuadraticMap.polarBilin Q) := by
  refine QuadraticMap.bilin_ext_of_tmul fun m m' ↦ ?_
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    LinearMap.BilinForm.baseChange_tmul, ← TensorProduct.tmul_add,
    baseChangeOfProjective_tmul, mul_one, sub_smul]

/-- **Base change commutes with scaling.** Rescaling `Q` by `a ∈ R` and then base changing is the
same as base changing and rescaling by the image of `a` in `A`. Compared on pure tensors `1 ⊗ₜ m`,
where both sides give `(a * Q m) • 1 = algebraMap a * algebraMap (Q m)`. -/
theorem baseChangeOfProjective_smul (a : R) (Q : QuadraticForm R M) :
    baseChangeOfProjective A (a • Q) = algebraMap R A a • baseChangeOfProjective A Q := by
  refine baseChange_ext fun m ↦ ?_
  rw [baseChangeOfProjective_tmul, smul_apply, smul_apply,
    baseChangeOfProjective_tmul, smul_eq_mul, mul_one, Algebra.smul_def, Algebra.smul_def,
    Algebra.smul_def, map_mul]
  simp [mul_comm]

/-- **Base change commutes with pullback along a linear map.** For `f : P →ₗ[R] M` with `P` and
`M` finitely generated projective, base changing `Q ∘ f` is the same as pulling back `Q_A` along
`f_A`.

Both sides are quadratic forms on `A ⊗[R] P`, so by `baseChange_ext` it is enough to compare them
on the pure tensors `1 ⊗ₜ p`, where both give `Q (f p)`. Note that this holds despite
`baseChangeOfProjective` being built from a *chosen* bilinear representative: the two sides may
well be built from unrelated representatives, but a quadratic form on a base changed module is
determined by its values on `1 ⊗ₜ p`. -/
theorem baseChangeOfProjective_comp {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] (Q : QuadraticForm R M) (f : P →ₗ[R] M) :
    baseChangeOfProjective A (Q.comp f) =
      (baseChangeOfProjective A Q).comp (LinearMap.baseChange A f) := by
  refine baseChange_ext fun p ↦ ?_
  rw [baseChangeOfProjective_tmul, QuadraticMap.comp_apply, QuadraticMap.comp_apply,
    LinearMap.baseChange_tmul, baseChangeOfProjective_tmul]

/-- Base change of an isometry between quadratic forms on finite projective modules. -/
noncomputable def _root_.QuadraticMap.IsometryEquiv.baseChangeOfProjective
    {N : Type uN} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (Q : QuadraticForm R M) (Q' : QuadraticForm R N) (e : Q.IsometryEquiv Q') :
    (Q.baseChangeOfProjective A).IsometryEquiv (Q'.baseChangeOfProjective A) where
  toLinearEquiv := e.toLinearEquiv.baseChange R A M N
  map_app' := by
    have he : Q = Q'.comp e.toLinearEquiv.toLinearMap :=
      QuadraticMap.ext fun x ↦ e.map_app x |>.symm
    intro m
    change (Q'.baseChangeOfProjective A).comp
      (LinearMap.baseChange A e.toLinearEquiv.toLinearMap) m = Q.baseChangeOfProjective A m
    rw [← QuadraticForm.baseChangeOfProjective_comp, ← he]

/-- When `2` is invertible this recovers mathlib's `QuadraticForm.baseChange`. -/
theorem baseChangeOfProjective_eq_baseChange [Invertible (2 : R)] (Q : QuadraticForm R M) :
    baseChangeOfProjective A Q = QuadraticForm.baseChange A Q := by
  refine baseChange_ext fun m ↦ ?_
  rw [baseChangeOfProjective_tmul, QuadraticForm.baseChange_tmul]

/-! ### Transitivity -/

section Trans

variable {S T : Type*} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

variable (S T) in
/-- **Base change is transitive**, in the form that avoids naming the comparison map on the
right-hand side: base changing to `S` and then to `T`, and reading the result back along
`T ⊗[S] (S ⊗[R] M) ≃ T ⊗[R] M`, gives the direct base change to `T`.

Stated this way round because `QuadraticMap.baseChange_ext` compares two forms on `T ⊗[R] M` by
their values at `1 ⊗ₜ m` only, whereas comparing them on `T ⊗[S] (S ⊗[R] M)` would require
knowing them at `1 ⊗ₜ x` for every `x` in `S ⊗[R] M` — a quadratic condition that does not reduce
to pure tensors. -/
theorem baseChangeOfProjective_baseChangeOfProjective_comp_symm (Q : QuadraticForm R M) :
    ((Q.baseChangeOfProjective S).baseChangeOfProjective T).comp
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).symm.toLinearMap =
      Q.baseChangeOfProjective T := by
  refine baseChange_ext fun m ↦ ?_
  rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, baseChangeOfProjective_tmul,
    baseChangeOfProjective_tmul, baseChangeOfProjective_tmul, mul_one, mul_one, smul_assoc,
    one_smul]

variable (S T) in
/-- **Base change is transitive**, as an isometry `T ⊗[S] (S ⊗[R] M) ≃ T ⊗[R] M`.

This is the form the residue-field arguments consume: a predicate on `Q.baseChangeOfProjective F`
for every field `F` over `R` can be tested on `(Q.baseChangeOfProjective S).baseChangeOfProjective
F` for every field `F` over `S`, since the two forms differ by this isometry. -/
noncomputable def baseChangeOfProjectiveIsometryEquiv (Q : QuadraticForm R M) :
    QuadraticMap.IsometryEquiv ((Q.baseChangeOfProjective S).baseChangeOfProjective T)
      (Q.baseChangeOfProjective T) where
  __ := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
  map_app' x := by
    conv_lhs => rw [← baseChangeOfProjective_baseChangeOfProjective_comp_symm S T Q]
    simp

end Trans

end QuadraticForm

/-! ### Anisotropy and localization (`GPR Exc. 12.38(b)`) -/

namespace QuadraticForm

open scoped nonZeroDivisors

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- **`GPR Exc. 12.38(b)`, for quadratic forms.** Let `L` be the localization of `R` at a
multiplicative set `S` of non-zero-divisors. A quadratic form on a finitely generated projective
`R`-module is anisotropic if and only if its base change to `L` is; equivalently, it represents
zero if and only if its base change does.

A null vector `m ≠ 0` gives the null vector `1 ⊗ m ≠ 0`, since a projective module has no
`S`-torsion. Conversely a null vector `x` of `L ⊗[R] M` satisfies `s • x = 1 ⊗ m` for some `s ∈ S`
and `m ∈ M`, and then `Q m` maps to `s² Q_L(x) = 0`. -/
theorem anisotropic_baseChangeOfProjective_iff_of_isLocalization (S : Submonoid R) (hS : S ≤ R⁰)
    (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L] (Q : QuadraticForm R M) :
    (Q.baseChangeOfProjective L).Anisotropic ↔ Q.Anisotropic := by
  have hval (m : M) :
      Q.baseChangeOfProjective L (TensorProduct.mk R L M 1 m) = algebraMap R L (Q m) := by
    rw [TensorProduct.mk_apply, baseChangeOfProjective_tmul, mul_one, Algebra.smul_def, mul_one]
  refine ⟨fun h m hm ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S (TensorProduct.mk R L M 1)).mp <|
      h _ (by rw [hval, hm, map_zero])
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (hS s.2) (hs.trans (smul_zero _).symm)
  · obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S (TensorProduct.mk R L M 1) x
    rw [Submonoid.smul_def, ← algebraMap_smul L] at hms
    have hm : m = 0 := h m <| IsLocalization.injective L hS <| by
      rw [map_zero, ← hval, ← hms, QuadraticMap.map_smul, hx, smul_zero]
    rw [hm, map_zero] at hms
    exact (IsLocalization.map_units L s).smul_eq_zero.mp hms

/-- **`GPR Exc. 12.38(b)` over the fraction field.** A quadratic form on a finitely generated
projective module is anisotropic if and only if its base change to the fraction field is. -/
theorem anisotropic_baseChangeOfProjective_iff_of_isFractionRing (F : Type*) [CommRing F]
    [Algebra R F] [IsFractionRing R F] (Q : QuadraticForm R M) :
    (Q.baseChangeOfProjective F).Anisotropic ↔ Q.Anisotropic :=
  anisotropic_baseChangeOfProjective_iff_of_isLocalization R⁰ le_rfl F Q

end QuadraticForm
