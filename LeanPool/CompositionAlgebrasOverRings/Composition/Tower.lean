/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Doubling
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankTwoSubalgebra

/-!
# The Cayley–Dickson tower exhausts a composition algebra (`GPR 19.17`)

Over an **LG ring**, a composition algebra `C` of constant rank `r > 1` is obtained from a
rank-two composition algebra by iterated Cayley–Dickson doubling. At every noninitial rung there
are a unital subalgebra `B` with regular restricted norm, of constant rank `r / 2`, and a
`v ⊥ B` with `n(v) ∈ kˣ`, such that

  `Cay(B, -n(v)) → C`,   `u + wj ↦ u + wv`,

is **bijective**, unital, multiplicative and an isometry. `B` is then again a composition algebra,
of half the rank, so the statement applies to it in turn and the whole tower descends to the
rank-two subalgebra of `GPR 19.16(b)`. If `2` is a unit, the rank-one scalar subalgebra may be
used as the initial rung instead. These are the two clauses of `GPR 19.17`.

## The three ingredients, and where each comes from

1. **Start** (`GPR 19.16(b)`, `Composition/RankTwoSubalgebra.lean`): rank `> 1` produces a regular
   rank-two subalgebra `k[u]`. The tower starts here and not at `k · 1`, whose restricted norm
   `⟨1⟩` is regular only when `2 ∈ kˣ`; under that extra hypothesis the tower starts at `k`.
2. **Step** (`GPR 19.16(a)`, `Composition/Doubling.lean`): a regular subalgebra whose orthogonal
   complement has full support is doubled inside `C`.
3. **Regularity of the new rung** (`GPR 19.11`, `Composition/RankDichotomy.lean`): the image is a
   composition algebra of constant rank `2s`, and `2s ≠ 1` because it is even, so its norm is
   regular and step 2 applies again. Without this the induction could not feed its own output back
   in — regularity of `q₁ ⊥ q₂` does not follow from regularity of `q₁`, only non-singularity
   does (`GN (C.8.3)`).

## The rank bookkeeping

This is what the file supplies, and it is what "`C` is exhausted" turns into:

* `ConicAlgebra.rankAtStalk_cay` : the rank doubles, pointwise on `Spec k` — the projective
  version of `ConicAlgebra.Cay.finrank_cay`, which needs a basis.
* `ConicAlgebra.rankAtStalk_add_polarOrthogonal` : a regular subalgebra is a direct summand, so
  `rk C = rk B + rk Bᗮ`. Its two consequences are the two ends of the induction —
  `ConicAlgebra.rankAtStalk_le_of_isGPRRegular` bounds each rung by `r`, so doubling terminates,
  and `ConicAlgebra.mem_of_isGPRRegular_of_rankAtStalk_eq` says a regular subalgebra of full rank
  is everything, which is what turns the last doubling into a *surjection*.
* `ConicAlgebra.hasFullSupport_polarOrthogonal_of_rankAtStalk_lt` : constant rank `s < r` gives
  the full-support hypothesis that `GPR 19.16(a)` consumes, via
  `Module.finrank_baseChange_of_rankAtStalk_eq`.

⚠ `[Nontrivial k]` is a genuine hypothesis of the induction, not decoration: over the zero ring
`Spec k` is empty, every rank statement is vacuous, and the bound `2s ≤ r` that makes the tower
terminate cannot be read off from any prime. (The conclusion still holds there, since every module
is trivial, but by a different argument.)

⚠ The subalgebra produced at each step is the **image** of `ConicAlgebra.cayToAlgebra`, packaged
existentially by `ConicAlgebra.exists_subalgebra_equiv_cay` rather than as a definition: its
closure under multiplication needs the orthogonality and invertibility hypotheses, and
overview §2 keeps hypotheses off definitions.

## Main results

* `ConicAlgebra.IsComposition.rank_eq_two_or_exists_bijective_cayToAlgebra` : the full
  rank-`> 1` clause of **`GPR 19.17`**, with rank two as the initial rung.
* `ConicAlgebra.IsComposition.exists_bijective_cayToAlgebra_of_invertible_two` : the clause of
  **`GPR 19.17`** starting the tower at the base ring when `2` is invertible.
* `ConicAlgebra.IsComposition.exists_bijective_cayToAlgebra` : the noninitial doubling step.
* `ConicAlgebra.IsComposition.exists_isGPRRegular_rankAtStalk_two_mul` : one rung of the tower.
* `ConicAlgebra.exists_subalgebra_equiv_cay` : the image `B + Bv` as a unital subalgebra.
* `ConicAlgebra.isGPRRegular_restrict_and_rankAtStalk_of_equiv_cay` : every internal doubled image
  of a regular constant-rank subalgebra is regular and has twice the rank.
* `ConicAlgebra.mem_of_isGPRRegular_of_rankAtStalk_eq` : the exhaustion criterion.
* `ConicAlgebra.rankAtStalk_cay`, `ConicAlgebra.rankAtStalk_add_polarOrthogonal` : the rank
  bookkeeping.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.11, 19.16,
  19.17.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European J. Math. **11** (2025), art. 42,
  C.8.3.
-/

@[expose] public section

universe u v

open QuadraticMap (polar)
open scoped TensorProduct

namespace Module

variable {k : Type u} [CommRing k] {M : Type v} [AddCommGroup M] [Module k M]

/-- **Constant rank is dimension after base change to any field.** `Module.rankAtStalk` is
computed at primes of `k`; base change to a field `F ∈ k`-alg reads it off at the prime `⊥` of
`F`, where the module is free. -/
theorem finrank_baseChange_of_rankAtStalk_eq [Module.Finite k M] [Module.Projective k M] {r : ℕ}
    (hr : Module.rankAtStalk (R := k) M = fun _ ↦ r) (F : Type u) [Field F] [Algebra k F] :
    Module.finrank F (F ⊗[k] M) = r := by
  have hbase := Module.rankAtStalk_baseChange (R := k) (M := M) (S := F) ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free, hr] at hbase

end Module

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A} {B : NonAssocSubalgebra k A}

/-- A unital subalgebra and its underlying submodule are the same module. The two coercions are
definitionally equal but not syntactically so, and `Module.rankAtStalk` statements have to be
moved between them: the orthogonal-complement API is stated for submodules, the conic API for
subalgebras. -/
def toSubmoduleEquiv (B : NonAssocSubalgebra k A) :
    B.toNonUnitalSubalgebra.toSubmodule ≃ₗ[k] B where
  toFun x := ⟨(x : A), x.2⟩
  invFun x := ⟨(x : A), x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A] in
/-- `Module.rankAtStalk` does not see the difference between a subalgebra and its submodule. -/
theorem rankAtStalk_toSubmodule (B : NonAssocSubalgebra k A) :
    Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule =
      Module.rankAtStalk (R := k) B :=
  Module.rankAtStalk_eq_of_equiv (toSubmoduleEquiv B)

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **The rank criterion for properness.** A regular subalgebra whose constant rank is smaller
than the constant rank of the ambient algebra has a complement of full support, which is the
hypothesis `GPR 19.16(a)` consumes. -/
theorem hasFullSupport_polarOrthogonal_of_rankAtStalk_lt
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm) {r s : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ s)
    (hlt : s < r) :
    Module.HasFullSupport k
      (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule) :=
  haveI := QuadraticForm.finite_of_comp_isGPRRegular (Q := C.norm) hreg
  haveI := QuadraticForm.projective_of_comp_isGPRRegular (Q := C.norm) hreg
  hasFullSupport_polarOrthogonal_of_finrank_lt hreg fun F _ _ ↦ by
    rw [Module.finrank_baseChange_of_rankAtStalk_eq hB F,
      Module.finrank_baseChange_of_rankAtStalk_eq hA F]
    exact hlt

/-! ### The image of the doubling map as a subalgebra -/

variable {v : A}

/-- **`B + Bv` is a unital subalgebra, isomorphic to `Cay(B, -n(v))`.**

The image of `ConicAlgebra.cayToAlgebra` is closed under multiplication precisely because that map
is multiplicative (`GPR 18.1`), and it contains `1` because the map is unital. Packaged with the
linear equivalence onto it, which is what carries the norm, the rank and the composition structure
across.

Existential rather than a definition: the subalgebra structure needs the orthogonality and
invertibility hypotheses, and overview §2 keeps hypotheses off definitions. -/
theorem exists_subalgebra_equiv_cay [IsAlternative A] (hBv : ∀ b ∈ B, polar C.norm b v = 0)
    (hu : IsUnit (C.norm v)) (hinj : Function.Injective (cayToAlgebra C B v)) :
    ∃ (D : NonAssocSubalgebra k A) (e : Cay (C.restrict B) (-C.norm v) ≃ₗ[k] D),
      ∀ p, ((e p : A)) = cayToAlgebra C B v p := by
  have hconj := C.conjIsInvolution_of_projective
  set S : Set A := Set.range (cayToAlgebra C B v) with hS
  have hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact ⟨p + q, map_add _ _ _⟩
  have hsmul : ∀ (c : k), ∀ x ∈ S, c • x ∈ S := by
    rintro c _ ⟨p, rfl⟩
    exact ⟨c • p, map_smul _ _ _⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact ⟨p * q, cayToAlgebra_mul hBv hconj hu p q⟩
  let D : NonAssocSubalgebra k A :=
    { carrier := S
      add_mem' := fun ha hb ↦ hadd _ ha _ hb
      zero_mem' := ⟨0, map_zero _⟩
      mul_mem' := fun ha hb ↦ hmul _ ha _ hb
      smul_mem' := fun c _ ha ↦ hsmul c _ ha
      one_mem := ⟨1, cayToAlgebra_one⟩ }
  let g : Cay (C.restrict B) (-C.norm v) →ₗ[k] D :=
    { toFun := fun p ↦ ⟨cayToAlgebra C B v p, ⟨p, rfl⟩⟩
      map_add' := fun p q ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun c p ↦ Subtype.ext (map_smul _ _ _) }
  refine ⟨D, LinearEquiv.ofBijective g ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · exact fun p q hpq ↦ hinj (congrArg Subtype.val hpq)
  · rintro ⟨_, p, rfl⟩
    exact ⟨p, rfl⟩

/-! ### The rank doubles

`ConicAlgebra.Cay.finrank_cay` says this for free modules; the tower needs it pointwise on
`Spec k`, since that is the form in which the rank of a subalgebra is controlled. -/

/-- **The rank of the double is twice the rank.** The pointwise form of
`ConicAlgebra.Cay.finrank_cay`, with no freeness hypothesis. -/
theorem rankAtStalk_cay {B' : Type v} [NonAssocRing B'] [Module k B'] [Module.Finite k B']
    [Module.Projective k B'] (C' : ConicAlgebra k B') (μ : k) :
    Module.rankAtStalk (R := k) (Cay C' μ) = 2 * Module.rankAtStalk (R := k) B' := by
  have e : Cay C' μ ≃ₗ[k] B' × B' :=
    { toFun := fun p ↦ (p.1, p.2)
      invFun := fun p ↦ ((p.1, p.2) : Cay C' μ)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  ext p
  simp [two_mul]

/-- **Regularity and rank of an internal doubled image.** Suppose `D` is the image of the internal
doubling map on a regular subalgebra `B` of constant rank `s`. Then the restricted norm on `D` is
regular and `D` has constant rank `2s`.

The norm pulled back to the external double is the Cayley–Dickson norm. It is non-singular by
`GN (C.8.3)`, so the image is a composition algebra; its even rank then rules out the exceptional
rank-one case in `GPR 19.11`. -/
theorem isGPRRegular_restrict_and_rankAtStalk_of_equiv_cay
    (h : C.IsComposition.{u, v, u})
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm)
    (hBv : ∀ b ∈ B, polar C.norm b v = 0) (hu : IsUnit (C.norm v))
    (D : NonAssocSubalgebra k A) (e : Cay (C.restrict B) (-C.norm v) ≃ₗ[k] D)
    (he : ∀ p, ((e p : D) : A) = cayToAlgebra C B v p) {s : ℕ}
    (hB : Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ s) :
    QuadraticForm.IsGPRRegular (C.restrict D).norm ∧
      Module.rankAtStalk (R := k) D.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ 2 * s := by
  let : Module.Finite k B := by
    have := QuadraticForm.finite_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Finite.equiv (toSubmoduleEquiv B)
  let : Module.Projective k B := by
    have := QuadraticForm.projective_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Projective.of_equiv (toSubmoduleEquiv B)
  have hpull : (C.restrict D).norm.comp e.toLinearMap =
      ((C.restrict B).cay (-C.norm v)).norm := by
    refine QuadraticMap.ext fun p ↦ ?_
    rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe]
    change C.norm ((e p : D) : A) = _
    rw [he p, norm_cayToAlgebra hBv h.isMultiplicative]
  let : Module.Finite k D := Module.Finite.equiv e
  let : Module.Projective k D := Module.Projective.of_equiv e
  have hcay : QuadraticForm.IsGPRNonsingular.{u, v, u}
      ((C.restrict B).cay (-C.norm v)).norm :=
    hreg.prod_isGPRNonsingular
      (hreg.isGPRNonsingular.smul_of_isUnit (by rwa [neg_neg] : IsUnit (-(-C.norm v))))
  have hDns : QuadraticForm.IsGPRNonsingular.{u, v, u} (C.restrict D).norm := by
    have hcomp := hcay.comp_linearEquiv e.symm
    have heq : ((C.restrict B).cay (-C.norm v)).norm.comp e.symm.toLinearMap =
        (C.restrict D).norm := by
      rw [← hpull]
      refine QuadraticMap.ext fun d ↦ ?_
      simp
    rwa [heq] at hcomp
  have hDcomp : (C.restrict D).IsComposition.{u, v, u} :=
    ⟨hDns, h.isMultiplicative.restrict⟩
  have hDrank : Module.rankAtStalk (R := k) D = fun _ ↦ 2 * s := by
    rw [← Module.rankAtStalk_eq_of_equiv e, rankAtStalk_cay, ← rankAtStalk_toSubmodule, hB]
    rfl
  have hDrank' : Module.rankAtStalk (R := k) D.toNonUnitalSubalgebra.toSubmodule =
      fun _ ↦ 2 * s := by
    rw [rankAtStalk_toSubmodule]
    exact hDrank
  exact ⟨hDcomp.isGPRRegular_of_rankAtStalk_ne_one hDrank (by omega), hDrank'⟩

/-! ### A regular subalgebra of full rank is everything -/

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **The ranks add up.** A subalgebra with regular restricted norm is a direct summand — that is
`QuadraticForm.orthogonalDecomposition` — so its rank and the rank of its orthogonal complement
add up to the rank of the ambient algebra, pointwise on `Spec k`. -/
theorem rankAtStalk_add_polarOrthogonal
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm) :
    Module.rankAtStalk (R := k) A =
      Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule +
        Module.rankAtStalk (R := k)
          (C.norm.polarOrthogonal B.toNonUnitalSubalgebra.toSubmodule) := by
  have := QuadraticForm.finite_of_comp_isGPRRegular (Q := C.norm) hreg
  have := QuadraticForm.projective_of_comp_isGPRRegular (Q := C.norm) hreg
  have := QuadraticForm.finite_polarOrthogonal (Q := C.norm) hreg
  have := QuadraticForm.projective_polarOrthogonal (Q := C.norm) hreg
  have h := Module.rankAtStalk_eq_of_equiv
    (QuadraticForm.orthogonalDecomposition (Q := C.norm)
      (N := B.toNonUnitalSubalgebra.toSubmodule) hreg)
  rw [Module.rankAtStalk_prod] at h
  exact h.symm

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- A subalgebra with regular restricted norm has rank at most that of the ambient algebra. This
is what bounds the tower: each rung doubles the rank, and no rung can outgrow `C`. -/
theorem rankAtStalk_le_of_isGPRRegular
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm) (p : PrimeSpectrum k) :
    Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule p ≤
      Module.rankAtStalk (R := k) A p := by
  have h := congrFun (rankAtStalk_add_polarOrthogonal hreg) p
  simp only [Pi.add_apply] at h
  omega

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **The exhaustion criterion.** A subalgebra whose restricted norm is regular is a direct
summand, so if its rank agrees with the rank of the ambient algebra everywhere on `Spec k`, the
complement has rank zero and hence vanishes: the subalgebra is the whole algebra.

This is the rank bookkeeping that turns "`C` is exhausted" into a statement about `Bᗮ`. -/
theorem mem_of_isGPRRegular_of_rankAtStalk_eq
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ r)
    (x : A) : x ∈ B := by
  have htop := QuadraticForm.eq_top_of_isGPRRegular_of_rankAtStalk_eq
    (Q := C.norm) (N := B.toNonUnitalSubalgebra.toSubmodule) hreg hA hB
  have hx : x ∈ B.toNonUnitalSubalgebra.toSubmodule := htop ▸ Submodule.mem_top
  exact hx

/-! ### One rung of the tower -/

/-- **The doubling step.** Over an LG ring, a regular subalgebra of a composition algebra whose
constant rank `s` is smaller than the constant rank `r` of the ambient algebra is contained in a
regular subalgebra of constant rank `2s` — the image of `Cay(B, -n(v))` — and when `2s = r` that
image is the whole algebra.

Regularity of the new subalgebra is *not* proved from regularity of the doubled quadratic form,
which would need `q₁ ⊥ q₂` regular from `q₁` regular. It comes from `GPR 19.11`
(`ConicAlgebra.IsComposition.isGPRRegular_of_rankAtStalk_ne_one`): the image is a composition
algebra of constant rank `2s`, and `2s ≠ 1` because it is even. This is the step that `GPR 19.11`
unblocks, and it is what lets the induction feed its own output back in. -/
theorem IsComposition.exists_isGPRRegular_rankAtStalk_two_mul (hLG : IsLGRing k)
    (h : C.IsComposition.{u, v, u})
    (hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm) {r s : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r)
    (hB : Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ s)
    (hlt : s < r) :
    ∃ (D : NonAssocSubalgebra k A) (v : A),
      IsUnit (C.norm v) ∧ (∀ b ∈ B, polar C.norm b v = 0) ∧
      QuadraticForm.IsGPRRegular (C.restrict D).norm ∧
      Module.rankAtStalk (R := k) D.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ 2 * s) ∧
      (2 * s = r → Function.Bijective (cayToAlgebra C B v)) := by
  let : IsAlternative A := h.isAlternative_general
  have : Module.Finite k B := by
    have := QuadraticForm.finite_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Finite.equiv (toSubmoduleEquiv B)
  have : Module.Projective k B := by
    have := QuadraticForm.projective_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Projective.of_equiv (toSubmoduleEquiv B)
  obtain ⟨v, hu, hBv, hinj, -, -⟩ := h.exists_cayToAlgebra hLG hreg
    (hasFullSupport_polarOrthogonal_of_rankAtStalk_lt hreg hA hB hlt)
  obtain ⟨D, e, he⟩ := exists_subalgebra_equiv_cay hBv hu hinj
  obtain ⟨hDreg, hDrank'⟩ :=
    isGPRRegular_restrict_and_rankAtStalk_of_equiv_cay h hreg hBv hu D e he hB
  refine ⟨D, v, hu, hBv, hDreg, hDrank', fun hfull ↦ ⟨hinj, fun x ↦ ?_⟩⟩
  have hmem : x ∈ D := mem_of_isGPRRegular_of_rankAtStalk_eq hDreg hA (hfull ▸ hDrank') x
  exact ⟨e.symm ⟨x, hmem⟩, by rw [← he, e.apply_symm_apply]⟩

/-! ### Iterating: `GPR 19.17` -/

/-- The induction behind `GPR 19.17`, with an explicit fuel parameter `n` bounding `r - s`.

Each pass either finishes — when the double already fills up `C` — or replaces `B` by a regular
subalgebra of twice the rank, which is still at most `r` because a regular subalgebra is a direct
summand (`ConicAlgebra.rankAtStalk_le_of_isGPRRegular`). Since `s ≥ 1`, doubling strictly
decreases `r - s`, so the fuel suffices. -/
private theorem IsComposition.exists_bijective_cayToAlgebra_aux [Nontrivial k] (hLG : IsLGRing k)
    (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) :
    ∀ (n s : ℕ) (B : NonAssocSubalgebra k A),
      QuadraticForm.IsGPRRegular (C.restrict B).norm →
      Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) →
      0 < s → s < r → r - s ≤ n →
      ∃ (D : NonAssocSubalgebra k A) (v : A) (t : ℕ),
        2 * t = r ∧
        Module.rankAtStalk (R := k) D.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ t) ∧
        IsUnit (C.norm v) ∧ (∀ b ∈ D, polar C.norm b v = 0) ∧
        QuadraticForm.IsGPRRegular (C.restrict D).norm ∧
        Function.Bijective (cayToAlgebra C D v) := by
  intro n
  induction n with
  | zero => intro s _ _ _ _ hsr hfuel; omega
  | succ n ih =>
    intro s B hreg hs hs0 hsr hfuel
    obtain ⟨D, v, hu, hBv, hDreg, hDrank, hbij⟩ :=
      h.exists_isGPRRegular_rankAtStalk_two_mul hLG hreg hA hs hsr
    by_cases hfull : 2 * s = r
    · exact ⟨B, v, s, hfull, hs, hu, hBv, hreg, hbij hfull⟩
    · have hle : 2 * s ≤ r := by
        have := rankAtStalk_le_of_isGPRRegular hDreg (Classical.arbitrary (PrimeSpectrum k))
        rwa [hDrank, hA] at this
      exact ih (2 * s) D hDreg hDrank (by omega) (by omega) (by omega)

/-- **`GPR 19.17`: a composition algebra of rank greater than two arises by the Cayley–Dickson
process.** Over an LG ring, a composition algebra of constant rank `r > 2` is the double of one of
its own subalgebras: there are a subalgebra `B` with regular restricted norm and a `v ∈ Bᗮ` with
`n(v) ∈ kˣ` for which

  `Cay(B, -n(v)) → C`,   `u + wj ↦ u + wv`,

is bijective. It is automatically unital, multiplicative and an isometry
(`ConicAlgebra.cayToAlgebra_one`, `ConicAlgebra.cayToAlgebra_mul`,
`ConicAlgebra.norm_cayToAlgebra`), so `C` *is* `Cay(B, -n(v))`. Since `B` is again a composition
algebra — of half the rank, by `ConicAlgebra.rankAtStalk_cay` — iterating the statement descends
the whole tower.

The tower starts at the rank-two subalgebra of `GPR 19.16(b)` and not at `k · 1`, whose restricted
norm `⟨1⟩` is regular only when `2 ∈ kˣ`. That is why the hypothesis is `2 < r` rather than
`1 < r`: rank two is the base case of the process, not a step in it. -/
theorem IsComposition.exists_bijective_cayToAlgebra [Nontrivial k] (hLG : IsLGRing k)
    (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : 2 < r) :
    ∃ (B : NonAssocSubalgebra k A) (v : A) (s : ℕ),
      2 * s = r ∧
      Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) ∧
      IsUnit (C.norm v) ∧
      QuadraticForm.IsGPRRegular (C.restrict B).norm ∧
      Function.Bijective (cayToAlgebra C B v) ∧
      cayToAlgebra C B v 1 = 1 ∧
      (∀ p q, cayToAlgebra C B v (p * q) = cayToAlgebra C B v p * cayToAlgebra C B v q) ∧
      (∀ p, C.norm (cayToAlgebra C B v p) = ((C.restrict B).cay (-C.norm v)).norm p) := by
  let : IsAlternative A := h.isAlternative_general
  obtain ⟨u, hu⟩ := h.exists_isRegularRankTwoComposition_of_rankAtStalk hLG (by
    intro 𝔭
    simp only [hA]
    omega)
  have hdisc : IsUnit (C.elementDiscriminant u) :=
    (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mp hu
  have hreg : QuadraticForm.IsGPRRegular (C.restrict (C.adjoinElement u)).norm :=
    C.normAdjoinElement_isGPRRegular hdisc
  have hrank : Module.rankAtStalk (R := k)
      (C.adjoinElement u).toNonUnitalSubalgebra.toSubmodule = fun _ ↦ 2 := by
    rw [rankAtStalk_toSubmodule, ← Module.rankAtStalk_eq_of_equiv (C.quadraticSpanEquiv hdisc),
      Module.rankAtStalk_prod, Module.rankAtStalk_self]
    rfl
  obtain ⟨B, v, s, hs2, hsrank, hunit, hBv, hBreg, hbij⟩ :=
    h.exists_bijective_cayToAlgebra_aux hLG hA r 2 (C.adjoinElement u) hreg hrank
      (by omega) hr (by omega)
  exact ⟨B, v, s, hs2, hsrank, hunit, hBreg, hbij, cayToAlgebra_one,
    cayToAlgebra_mul hBv C.conjIsInvolution_of_projective hunit,
    norm_cayToAlgebra hBv h.isMultiplicative⟩

/-- **Full `GPR 19.17`, starting in rank two.** A composition algebra of constant rank greater
than one over an LG ring is either already of rank two, or is a Cayley–Dickson double of a regular
composition subalgebra of half its rank. Reapplying the second alternative to that subalgebra
gives the finite tower starting in rank two asserted by the corollary. -/
theorem IsComposition.rank_eq_two_or_exists_bijective_cayToAlgebra [Nontrivial k]
    (hLG : IsLGRing k) (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : 1 < r) :
    r = 2 ∨
      ∃ (B : NonAssocSubalgebra k A) (v : A) (s : ℕ),
        2 * s = r ∧
        Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) ∧
        IsUnit (C.norm v) ∧
        QuadraticForm.IsGPRRegular (C.restrict B).norm ∧
        Function.Bijective (cayToAlgebra C B v) ∧
        cayToAlgebra C B v 1 = 1 ∧
        (∀ p q, cayToAlgebra C B v (p * q) =
          cayToAlgebra C B v p * cayToAlgebra C B v q) ∧
        ∀ p, C.norm (cayToAlgebra C B v p) =
          ((C.restrict B).cay (-C.norm v)).norm p := by
  by_cases h2 : r = 2
  · exact Or.inl h2
  · exact Or.inr (h.exists_bijective_cayToAlgebra hLG hA (by omega))

/-- The scalar subalgebra `k · 1 = k[0]`, as a free rank-one module. -/
noncomputable def scalarAdjoinZeroLinearEquiv (C : ConicAlgebra k A) :
    k ≃ₗ[k] C.adjoinElement 0 where
  toFun r := ⟨r • (1 : A), (C.mem_adjoinElement_iff 0 _).mpr ⟨r, 0, by simp⟩⟩
  invFun x := C.unitForm x
  map_add' r s := Subtype.ext (add_smul r s (1 : A))
  map_smul' r s := Subtype.ext (smul_smul r s (1 : A)).symm
  left_inv r := by simp
  right_inv x := by
    apply Subtype.ext
    obtain ⟨r, s, hx⟩ := (C.mem_adjoinElement_iff 0 x).mp x.2
    change C.unitForm x • (1 : A) = x
    rw [← hx]
    simp [C.unitForm_one]

/-- **The second clause of `GPR 19.17`.** If `2` is invertible, the Cayley–Dickson tower may be
started at the base ring itself. The scalar subalgebra has rank one and its norm is the regular
form `⟨1⟩`; the same doubling induction as above then reaches the ambient algebra. -/
theorem IsComposition.exists_bijective_cayToAlgebra_of_invertible_two [Nontrivial k]
    [Invertible (2 : k)] (hLG : IsLGRing k) (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) (hr : 1 < r) :
    ∃ (B : NonAssocSubalgebra k A) (v : A) (s : ℕ),
      2 * s = r ∧
      Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = (fun _ ↦ s) ∧
      IsUnit (C.norm v) ∧
      QuadraticForm.IsGPRRegular (C.restrict B).norm ∧
      Function.Bijective (cayToAlgebra C B v) := by
  let B := C.adjoinElement 0
  let e := scalarAdjoinZeroLinearEquiv C
  have hB : Module.rankAtStalk (R := k) B.toNonUnitalSubalgebra.toSubmodule = fun _ ↦ 1 := by
    rw [rankAtStalk_toSubmodule, ← Module.rankAtStalk_eq_of_equiv e,
      Module.rankAtStalk_self]
    rfl
  have hpull : (C.restrict B).norm.comp e.toLinearMap = QuadraticForm.rankOne (1 : k) := by
    refine QuadraticMap.ext fun x ↦ ?_
    change C.norm (x • (1 : A)) = QuadraticForm.rankOne (1 : k) x
    rw [C.norm.map_smul, C.norm_one, QuadraticForm.rankOne_apply]
    simp only [smul_eq_mul, mul_one, one_mul, pow_two]
  have hreg : QuadraticForm.IsGPRRegular (C.restrict B).norm := by
    apply (QuadraticForm.isGPRRegular_comp_linearEquiv_iff e).mp
    rw [hpull]
    exact (QuadraticForm.isGPRRegular_rankOne_iff_isUnit_two (isUnit_one : IsUnit (1 : k))).mpr
      (isUnit_of_invertible (2 : k))
  obtain ⟨D, v, s, hs, hD, hv, hDv, hDreg, hbij⟩ :=
    h.exists_bijective_cayToAlgebra_aux hLG hA r 1 B hreg hB (by omega) hr (by omega)
  exact ⟨D, v, s, hs, hD, hv, hDreg, hbij⟩

end ConicAlgebra
