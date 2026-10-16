/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankTwoSubalgebra

/-!
# The regular-or-rank-one dichotomy for composition algebras

This file proves the regular-or-rank-one dichotomy of **`GPR 19.11`**. Over a field, the norm of a
composition algebra is regular unless the algebra has dimension one; in the exceptional case the
field has characteristic two. The field result then globalizes: a constant-rank composition
algebra over a commutative ring is regular unless its rank is one and `2` is not a unit.

The quadratic-form dichotomy of `GPR Exercise 11.37` says that a nonregular nonsingular form has a
one-dimensional polar radical and that the field has characteristic two. The extra algebraic step
is to show that the whole algebra, not merely that radical, is one-dimensional. Choose a nonzero
element `u` in the polar radical. Its norm is nonzero because the quadratic radical vanishes.
Norm-associativity and right alternativity then make right multiplication by `conj u` surjective,
so orthogonality of `u` forces the trace to vanish identically. Multiplicativity now forces the
whole polar form to vanish, and its one-dimensional kernel is therefore the whole algebra.

## Main results

* `ConicAlgebra.IsComposition.isGPRRegular_or_finrank_eq_one` : the field-fibre dichotomy in
  `GPR 19.11`.
* `ConicAlgebra.IsComposition.isGPRRegular_of_forall_rankAtStalk_ne_one` : `GPR 19.11` for a
  composition algebra whose rank is never `1`, without a constant-rank hypothesis.
* `ConicAlgebra.IsComposition.isGPRRegular_or_rank_eq_one` : the constant-rank ring statement.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.9, 19.11.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {F : Type u} {A : Type v} [Field F] [NonAssocRing A] [Module F A]
  [SMulCommClass F A A] [IsScalarTower F A A] [Module.Finite F A] [Module.Projective F A]
  {C : ConicAlgebra F A}

/-- **The field-fibre core of `GPR 19.11`.** A composition algebra over a field has regular norm,
or it has dimension one and the field has characteristic two. -/
theorem IsComposition.isGPRRegular_or_finrank_eq_one (h : C.IsComposition.{u, v, u}) :
    C.norm.IsGPRRegular ∨ Module.finrank F A = 1 ∧ ringChar F = 2 := by
  have hnd : QuadraticMap.Nondegenerate (Q := C.norm) :=
    (C.norm.isGPRNonsingular_iff_nondegenerate).mp h.isGPRNonsingular
  rcases C.norm.isGPRRegular_xor_finrank_ker_polarBilin_eq_one hnd with
    hreg | hker
  · exact Or.inl hreg.1
  · right
    have hdim := hker.1
    have h2 : (2 : F) = 0 :=
      C.norm.two_eq_zero_of_finrank_ker_polarBilin_eq_one h.isGPRNondegenerate hdim
    let P := LinearMap.ker (QuadraticMap.polarBilin C.norm)
    have hPpos : 0 < Module.finrank F P := by simp [P, hdim]
    let : Nontrivial P := Module.nontrivial_of_finrank_pos hPpos
    obtain ⟨u, hu⟩ : ∃ u : P, u ≠ 0 := exists_ne 0
    have hnu : C.norm (u : A) ≠ 0 := by
      intro hnu
      have hurad : (u : A) ∈ C.norm.radical := ⟨hnu, LinearMap.mem_ker.mp u.2⟩
      rw [h.isGPRNondegenerate, Submodule.mem_bot] at hurad
      exact hu (Subtype.ext hurad)
    let : IsAlternative A := h.isAlternative
    have htu : C.trace (u : A) = 0 := by
      rw [C.trace_apply, QuadraticMap.polar_comm]
      exact DFunLike.congr_fun (LinearMap.mem_ker.mp u.2) 1
    have hconj : C.conj (u : A) = u := by
      rw [conj_apply, htu, zero_smul, zero_sub]
      apply neg_eq_iff_add_eq_zero.mpr
      rw [← two_smul F (u : A), h2, zero_smul]
    have huu : (u : A) * u = C.norm u • (1 : A) := by
      calc
        (u : A) * u = C.conj u * u := congrArg (fun a : A ↦ a * u) hconj.symm
        _ = C.norm u • (1 : A) := C.conj_mul_self u
    have htrace : ∀ x : A, C.trace x = 0 := by
      intro x
      set z : A := (C.norm u)⁻¹ • (x * u)
      have hzu : z * C.conj u = x := by
        dsimp [z]
        rw [hconj, smul_mul_assoc, IsAlternative.mul_self_mul_right, huu,
          mul_smul_comm, mul_one, inv_smul_smul₀ hnu]
      have huorth : QuadraticMap.polar C.norm (u : A) z = 0 :=
        DFunLike.congr_fun (LinearMap.mem_ker.mp u.2) z
      calc
        C.trace x = QuadraticMap.polar C.norm 1 x := C.trace_apply x
        _ = QuadraticMap.polar C.norm (1 * u) z := by
          rw [h.polar_mul_right, hzu]
        _ = 0 := by simpa only [one_mul] using huorth
    have hpolar : QuadraticMap.polarBilin C.norm = 0 := by
      ext x y
      rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply]
      exact h.isMultiplicative.polar_eq_zero_of_trace_eq_zero h2 htrace x y
    have htop : LinearMap.ker (QuadraticMap.polarBilin C.norm) = ⊤ := by
      rw [hpolar, LinearMap.ker_zero]
    constructor
    · rw [htop, finrank_top] at hdim
      exact hdim
    · exact C.norm.ringChar_eq_two_of_finrank_ker_polarBilin_eq_one
        h.isGPRNondegenerate hdim

section CommRing

variable {k : Type u} {B : Type v} [CommRing k] [NonAssocRing B] [Module k B]
  [SMulCommClass k B B] [IsScalarTower k B B] [Module.Finite k B] [Module.Projective k B]
  {D : ConicAlgebra k B}

/-- **`GPR 19.11`, pointwise on `Spec k`.** A composition algebra whose rank is different from `1`
at every prime has regular norm. No constant-rank hypothesis is needed: regularity is checked
after base change to each field `F`
(`QuadraticForm.isGPRRegular_of_forall_baseChangeOfProjective_isGPRRegular`), and the dimension of
`F ⊗ A` is the rank of `A` at the single prime under the zero ideal of `F`.
`ConicAlgebra.IsComposition.isGPRRegular_of_rankAtStalk_ne_one` is the constant-rank case. -/
theorem IsComposition.isGPRRegular_of_forall_rankAtStalk_ne_one (h : D.IsComposition.{u, v, u})
    (hrank : ∀ p, Module.rankAtStalk (R := k) B p ≠ 1) : D.norm.IsGPRRegular := by
  apply QuadraticForm.isGPRRegular_of_forall_baseChangeOfProjective_isGPRRegular
  intro F _ _
  rcases (h.baseChangeOfProjective F).isGPRRegular_or_finrank_eq_one with hreg | hdim
  · exact hreg
  · refine (hrank ((⊥ : PrimeSpectrum F).comap (algebraMap k F)) ?_).elim
    have hbase := Module.rankAtStalk_baseChange (R := k) (M := B) (S := F) ⊥
    rw [Module.rankAtStalk_eq_finrank_of_free] at hbase
    exact hbase.symm.trans hdim.1

/-- The non-rank-one half of **`GPR 19.11`**. If a composition algebra has constant rank other
than one, its norm is regular.

The field-fibre dichotomy proves regularity after every field base change. Regularity then descends
by the local-global principle for the polar map
(`ConicAlgebra.IsComposition.isGPRRegular_of_forall_rankAtStalk_ne_one`). -/
theorem IsComposition.isGPRRegular_of_rankAtStalk_ne_one (h : D.IsComposition.{u, v, u})
    {r : ℕ} (hrank : Module.rankAtStalk (R := k) B = fun _ ↦ r) (hr : r ≠ 1) :
    D.norm.IsGPRRegular :=
  h.isGPRRegular_of_forall_rankAtStalk_ne_one fun p ↦ by rw [hrank]; exact hr

/-- **`GPR 19.11`, for the project's finitely generated definition of composition algebra.**
If a composition algebra has constant rank `r`, then its norm is regular, or `r = 1` and `2` is
not a unit in the base ring.

The finite-generation conclusion of `GPR 19.11` is already an instance hypothesis in this
project's deliberately narrower `ConicAlgebra.IsComposition` API. -/
theorem IsComposition.isGPRRegular_or_rank_eq_one (h : D.IsComposition.{u, v, u}) {r : ℕ}
    (hrank : Module.rankAtStalk (R := k) B = fun _ ↦ r) :
    D.norm.IsGPRRegular ∨ r = 1 ∧ ¬ IsUnit (2 : k) := by
  by_cases hreg : D.norm.IsGPRRegular
  · exact Or.inl hreg
  · right
    have hr : r = 1 := by
      by_contra hr
      exact hreg (h.isGPRRegular_of_rankAtStalk_ne_one hrank hr)
    refine ⟨hr, ?_⟩
    intro h2
    let : Invertible (2 : k) := h2.invertible
    exact hreg h.isGPRRegular

omit [SMulCommClass k B B] [IsScalarTower k B B] in
/-- In a constant-rank-one conic algebra, every element is its `unitForm` coefficient times `1`.

The unit splits off a free rank-one summand. Since the whole module already has rank one, the
kernel of `unitForm` has rank zero and is trivial. This argument remains valid in characteristic
two, where the polar norm itself may be nonregular. -/
theorem eq_unitForm_smul_one_of_rankAtStalk_eq_one (D : ConicAlgebra k B)
    [Nontrivial k] (hB : Module.rankAtStalk (R := k) B = fun _ ↦ 1) (x : B) :
    x = D.unitForm x • (1 : B) := by
  let N := LinearMap.ker D.unitForm
  let p : B →ₗ[k] N := LinearMap.codRestrict N
    (LinearMap.id - LinearMap.toSpanSingleton k B 1 ∘ₗ D.unitForm) (fun z ↦ by
      simp [N, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, D.unitForm_one])
  have hpi : p ∘ₗ N.subtype = LinearMap.id := by
    refine LinearMap.ext fun z ↦ Subtype.ext ?_
    have hz : D.unitForm (z : B) = 0 := z.2
    simp [p, hz, LinearMap.toSpanSingleton_apply]
  let : Module.Finite k N :=
    Module.Finite.of_surjective p fun z ↦ ⟨(z : B), DFunLike.congr_fun hpi z⟩
  let : Module.Projective k N := Module.Projective.of_split N.subtype p hpi
  let E := LinearMap.equivProdKerOfApplyEqOne D.unitForm (1 : B) D.unitForm_one
  have hN : Module.rankAtStalk (R := k) N = 0 := by
    have hprod := Module.rankAtStalk_prod (R := k) k N
    have hE := Module.rankAtStalk_eq_of_equiv E
    rw [hprod, Module.rankAtStalk_self] at hE
    funext q
    have hq := congrFun (hE.symm.trans hB) q
    simp only [Pi.add_apply, Pi.one_apply, Pi.zero_apply] at hq ⊢
    omega
  let : Subsingleton N :=
    (Module.rankAtStalk_eq_zero_iff_subsingleton (R := k)).mp hN
  have hx : x - D.unitForm x • (1 : B) ∈ N := by
    simp [N, LinearMap.mem_ker, D.unitForm_one]
  have hzero : x - D.unitForm x • (1 : B) = 0 :=
    congrArg Subtype.val (Subsingleton.elim ⟨x - D.unitForm x • (1 : B), hx⟩ 0)
  exact sub_eq_zero.mp hzero

end CommRing

end ConicAlgebra
