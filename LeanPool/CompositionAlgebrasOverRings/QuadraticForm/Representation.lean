/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Semilocal
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Unimodular
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Polynomial
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The representation lemma (`GPR 11.26`, `GN Lemma C.13(a)`)

Over an LG-ring `R`, a non-singular quadratic form `(M, q)` with `M` finitely generated projective
represents a unit — `q(M) ∩ Rˣ ≠ ∅` — if and only if `M` has **full support**.

`GPR 11.26` states this for `q` regular; `GN C.13(a)` observes that the same proof gives the
non-singular case, which is the version formalized here (`IsGPRNonsingular`, from
`QuadraticForm/Regularity.lean`).

## Main definitions

* `Module.HasFullSupport R M` : `F ⊗[R] M ≠ 0` for every field `F ∈ R`-alg. This is condition (iv)
  of `GPR 11.25`, the formulation the proof actually consumes. For `M` finitely generated it is
  mathlib's `Module.support R M = Set.univ` (`Module.hasFullSupport_iff_support_eq_univ`).

## Main results

* `Module.hasFullSupport_of_isUnit_apply` : the easy direction of `GN C.13(a)`, `(ai) ⇒ (aii)`.
  Needs neither the LG hypothesis nor freeness: a unit value `q m ∈ Rˣ` stays a unit in every
  `F ⊗[R] M`, which is therefore nonzero.
* `QuadraticForm.exists_apply_ne_zero_of_radical_eq_bot` : over a field, a form whose radical
  vanishes on a nonzero space takes a nonzero — hence invertible — value. If `q` vanished
  identically its radical would be everything.
* `QuadraticForm.exists_isUnit_baseChange_of_hasFullSupport` : the **local half** of the hard
  direction. For `q` non-singular and `M` of full support, `q` represents a unit over every field
  `F ∈ R`-alg. This is exactly the hypothesis the LG axiom consumes.
* `QuadraticForm.exists_isUnit_apply_of_hasFullSupport` : the hard direction `(aii) ⇒ (ai)`, in
  full generality, by applying the LG axiom to the polynomial of `GPR 11.8`.
* `QuadraticForm.exists_isUnit_apply_iff_hasFullSupport` : **`GPR 11.26`** / **`GN C.13(a)`**, the
  two directions combined.
* `Module.exists_isUnimodular_of_hasFullSupport` : **`GN 2.6(a)`** restated for full support — a
  finitely generated projective module of full support over an LG-ring contains a unimodular
  element. Proved in `LGRing/Unimodular.lean`.

## Implementation notes

`GPR 11.8` (`QuadraticForm/Polynomial.lean`) writes a quadratic form on a *free* module as a
polynomial, and `M` is only projective, so the hard direction looks as though it needs a basis —
which is how `GPR` and `GN` proceed, reducing to the constant-rank case by the rank decomposition
(`GPR Exc. 9.31`) and then invoking constant-rank-projective ⇒ free (`GPR 11.24` = `GN 2.6(b)`).

That route is available in this development (`Module/RankDecomposition.lean` and
`LGRing/ConstantRank.lean`), but it is not the route taken here. Choosing a presentation
`π : Rⁿ ↠ M` and pulling `q` back to `q ∘ π` on the free module `Rⁿ` is enough: the polynomial of
`GPR 11.8` then exists outright, and the residue-field hypothesis survives the pullback because
`π ⊗ k` is still surjective. So neither `GN 2.6(b)` nor the rank decomposition is needed for
`GPR 11.26`. This is the same device that proves `GN 2.6(a)` in `LGRing/Unimodular.lean`.

The pullback is compared with base change by `QuadraticForm.baseChangeOfProjective_comp`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.25, 11.26.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Lemma C.13(a).
-/

@[expose] public section

universe u v

open scoped TensorProduct

/-- `M` has **full support** over `R`: base change to every field in `R`-alg is nonzero. This is
condition (iv) of `GPR 11.25`; `GPR` and `GN` also call a finitely generated projective module
with this property *faithfully projective*. -/
def Module.HasFullSupport (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    Prop :=
  ∀ (F : Type u) [Field F] [Algebra R F], Nontrivial (F ⊗[R] M)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **Full support is mathlib's `Module.support R M = Set.univ`**, for `M` finitely generated.

`F ⊗[R] M ≠ 0` at the residue field `κ(𝔭)` of every prime is membership of `𝔭` in the support
(`Module.mem_support_iff_nontrivial_residueField_tensorProduct`, which is where finite generation
is used). Conversely, a field `F ∈ R`-alg receives `κ(𝔭)` for `𝔭 = ker (R → F)`, and
`F ⊗[R] M = F ⊗[κ(𝔭)] (κ(𝔭) ⊗[R] M)` is nonzero because `F` is faithfully flat over the field
`κ(𝔭)`. -/
theorem Module.hasFullSupport_iff_support_eq_univ [Module.Finite R M] :
    Module.HasFullSupport R M ↔ Module.support R M = Set.univ := by
  refine ⟨fun h ↦ Set.eq_univ_of_forall fun p ↦
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mpr
      (h p.asIdeal.ResidueField), fun h F _ _ ↦ ?_⟩
  let p : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R F), RingHom.ker_isPrime _⟩
  have : p.asIdeal.IsPrime := p.2
  have : Nontrivial (p.asIdeal.ResidueField ⊗[R] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp (h ▸ Set.mem_univ p)
  let f : p.asIdeal.ResidueField →+* F :=
    Ideal.ResidueField.lift p.asIdeal (algebraMap R F) le_rfl fun r hr ↦
      isUnit_iff_ne_zero.mpr fun h0 ↦ hr (RingHom.mem_ker.mpr h0)
  let : Algebra p.asIdeal.ResidueField F := f.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField F :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap R F) _ _ r).symm
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField F F
    M).symm.toEquiv.nontrivial

/-- Full support gives the residue-field condition — condition (iv) of `GPR 11.25` implies
condition (iii). This is the form the LG axiom consumes, since `IsLGRing` quantifies over residue
fields.

The converse also holds for `M` finitely generated projective (`GPR 11.25`), but needs the rank
function on projective modules: a field `F ∈ R`-alg has `ker (algebraMap R F)` prime, and one must
know that the rank at that prime agrees with the rank at a maximal ideal containing it. That is
not proved here. -/
theorem Module.HasFullSupport.nontrivial_quotient_tensor (h : Module.HasFullSupport R M)
    (𝔪 : Ideal R) [𝔪.IsMaximal] : Nontrivial ((R ⧸ 𝔪) ⊗[R] M) := by
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  exact h (R ⧸ 𝔪)

/-- **`GN 2.6(a)`**, in terms of full support: over an LG-ring, a finitely generated projective
module of full support contains a unimodular element. This is `IsLGRing.exists_isUnimodular`
(`LGRing/Unimodular.lean`) fed through `HasFullSupport.nontrivial_quotient_tensor`. -/
theorem Module.exists_isUnimodular_of_hasFullSupport [Module.Finite R M] [Module.Projective R M]
    (hLG : IsLGRing R) (hM : Module.HasFullSupport R M) : ∃ m : M, Module.IsUnimodular R m :=
  hLG.exists_isUnimodular fun 𝔪 h𝔪 ↦ haveI := h𝔪; hM.nontrivial_quotient_tensor 𝔪

/-- **`GN C.13(a)`, `(ai) ⇒ (aii)`.** If `q` takes an invertible value then `M` has full support.

No LG hypothesis and no freeness: the value `q m ∈ Rˣ` maps to a unit of `F`, so
`q_F (1 ⊗ m) ≠ 0`, so `1 ⊗ m ≠ 0`. -/
theorem Module.hasFullSupport_of_isUnit_apply [Module.Finite R M] [Module.Projective R M]
    (q : QuadraticForm R M) {m : M} (hm : IsUnit (q m)) : Module.HasFullSupport R M := by
  intro F _ _
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hzero : (1 : F) ⊗ₜ[R] m = 0 := Subsingleton.elim _ _
  have hval : (q.baseChangeOfProjective F) ((1 : F) ⊗ₜ[R] m) = algebraMap R F (q m) := by
    rw [QuadraticForm.baseChangeOfProjective_tmul, mul_one, Algebra.smul_def, mul_one]
  rw [hzero, map_zero] at hval
  exact (hm.map (algebraMap R F)).ne_zero hval.symm

/-- Over a field, a quadratic form with vanishing radical on a nonzero space takes a nonzero
value. If it vanished identically, its polar form would too, so its radical would be all of `V`,
contradicting `radical = ⊥` on a nontrivial space. -/
theorem QuadraticForm.exists_apply_ne_zero_of_radical_eq_bot {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] [Nontrivial V] (q : QuadraticForm F V)
    (h : q.radical = ⊥) : ∃ v : V, q v ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have htop : q.radical = ⊤ := by
    refine eq_top_iff.mpr fun v _ ↦ ⟨hcon v, LinearMap.ext fun w ↦ ?_⟩
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hcon v, hcon w, hcon (v + w),
      LinearMap.zero_apply, sub_zero, sub_zero]
  rw [h] at htop
  exact absurd htop bot_ne_top

/-- **The local half of `GN C.13(a)`, `(aii) ⇒ (ai)`.** For `q` non-singular and `M` of full
support, `q` represents a unit over every field `F ∈ R`-alg.

Full support makes `F ⊗[R] M` nonzero and non-singularity makes the radical of `q_F` vanish, so
`q_F` cannot be identically zero; over a field a nonzero value is a unit.

This is precisely the hypothesis the LG axiom consumes — see the module docstring for what still
stands between this and the global statement. -/
theorem QuadraticForm.exists_isUnit_baseChange_of_hasFullSupport [Module.Finite R M]
    [Module.Projective R M] {q : QuadraticForm R M} (hq : q.IsGPRNonsingular.{u, v, u})
    (hM : Module.HasFullSupport R M) (F : Type u) [Field F] [Algebra R F] :
    ∃ x : F ⊗[R] M, IsUnit ((q.baseChangeOfProjective F) x) := by
  have := hM F
  obtain ⟨x, hx⟩ := (q.baseChangeOfProjective F).exists_apply_ne_zero_of_radical_eq_bot (hq F)
  exact ⟨x, hx.isUnit⟩

/-! ### The hard direction of `GN C.13(a)`, `(aii) ⇒ (ai)` -/

/-- **`GN C.13(a)`, `(aii) ⇒ (ai)`.** Over an LG-ring, a non-singular quadratic form on a finitely
generated projective module of full support represents a unit.

This is the point where the LG axiom is applied. `M` need not be free, so there is no basis in
which to write `q` as a polynomial; instead choose a presentation `π : Rⁿ ↠ M` and pull `q` back
to `q' := q ∘ π` on the *free* module `Rⁿ`, where `GPR 11.8`
(`QuadraticForm.aeval_toMvPolynomial`) does apply. Then

* `q'` represents a unit at every residue field `k`, because `q` does
  (`exists_isUnit_baseChange_of_hasFullSupport`) and `π ⊗ k` is still surjective, so the witness
  in `k ⊗ M` lifts to one in `k ⊗ Rⁿ` — which is free, so it can be expanded in coordinates to
  give the point of `Fin n → k` the LG axiom wants;
* the axiom descends that to `t : Fin n → R` with `q' t = q (π t)` a unit.

The comparison `(q ∘ π)_k = q_k ∘ (π ⊗ k)` is
`QuadraticForm.baseChangeOfProjective_comp`. -/
theorem QuadraticForm.exists_isUnit_apply_of_hasFullSupport [Module.Finite R M]
    [Module.Projective R M] (hLG : IsLGRing R) {q : QuadraticForm R M}
    (hq : q.IsGPRNonsingular.{u, v, u}) (hM : Module.HasFullSupport R M) :
    ∃ m : M, IsUnit (q m) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  set bm : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n) with hbm
  set q' : QuadraticForm R (Fin n → R) := q.comp π with hq'
  have hrep : (QuadraticForm.toMvPolynomial q' bm).RepresentsUnit R := by
    refine (hLG n _).mpr fun 𝔪 _ ↦ ?_
    let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    obtain ⟨x, hx⟩ := q.exists_isUnit_baseChange_of_hasFullSupport hq hM (R ⧸ 𝔪)
    obtain ⟨y, rfl⟩ := LinearMap.baseChange_surjective (R ⧸ 𝔪) hπ x
    set b' := Algebra.TensorProduct.basis (R ⧸ 𝔪) bm with hb'
    refine ⟨fun i ↦ b'.repr y i, ?_⟩
    have hy : ∑ i, b'.repr y i • ((1 : R ⧸ 𝔪) ⊗ₜ[R] bm i) = y := by
      simpa [hb', Algebra.TensorProduct.basis_apply] using b'.sum_repr y
    rw [QuadraticForm.aeval_toMvPolynomial, hy, hq',
      QuadraticForm.baseChangeOfProjective_comp, QuadraticMap.comp_apply]
    exact hx
  obtain ⟨t, ht⟩ := hrep
  rw [QuadraticForm.aeval_toMvPolynomial_self] at ht
  have hsum : ∑ i, t i • bm i = t := by
    simpa [hbm] using (Pi.basisFun R (Fin n)).sum_repr t
  rw [hsum, hq', QuadraticMap.comp_apply] at ht
  exact ⟨π t, ht⟩

/-- **`GPR 11.26`, `GN Lemma C.13(a)`.** Over an LG-ring, a non-singular quadratic form on a
finitely generated projective module represents a unit if and only if the module has full
support. -/
theorem QuadraticForm.exists_isUnit_apply_iff_hasFullSupport [Module.Finite R M]
    [Module.Projective R M] (hLG : IsLGRing R) {q : QuadraticForm R M}
    (hq : q.IsGPRNonsingular.{u, v, u}) :
    (∃ m : M, IsUnit (q m)) ↔ Module.HasFullSupport R M :=
  ⟨fun ⟨_, hm⟩ ↦ Module.hasFullSupport_of_isUnit_apply q hm,
    q.exists_isUnit_apply_of_hasFullSupport hLG hq⟩
