/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticEtale
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Capstone
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Fields over which every quadratic étale algebra splits (`GPR 23.12`)

Over such a field there is exactly one composition algebra in each of the dimensions `1`, `2`, `4`,
`8` — the split one — and no division algebra beyond the base field itself.

⚠ `GPR 23.12` also treats fields in which every element is a square (of interest in
characteristic 2, e.g. perfect fields), where every quaternion and octonion algebra is split
because every quadratic étale norm is surjective. That paragraph is not formalized here.

Two forms of the hypothesis appear here.

* **As a hypothesis.** `ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_adjoinElement`
  (`Composition/Reduced/Capstone.lean`) already proves this over an LG ring; over a field it gives
  the statement above verbatim.
* **Discharged, for a separably closed field.** The condition is *separable* closure, not
  algebraic closure, and the proof shows why. For `u` in a composition algebra `C` of dimension
  greater than one,

  `n(a·1 + u) = a² + t(u) a + n(u)`,

  so a root of `X² + t(u) X + n(u)` produces a null vector, nonzero as soon as `u ∉ K·1`. In
  characteristic other than two the discriminant `t(u)² - 4n(u)` has a square root because `X² - c`
  is separable, and the usual formula applies. In characteristic two the polynomial is separable
  exactly when `t(u) ≠ 0`, and such a `u` exists because the norm is regular: were the trace
  identically zero, `1` would lie in the kernel of the polar form. That is the only place
  regularity is used, and it is why `GPR 19.11` — the rank dichotomy — is a prerequisite.

## Main results

* `ConicAlgebra.IsComposition.not_anisotropic_of_isSepClosed` : over a separably closed field, the
  norm of a composition algebra of dimension greater than one is isotropic.
* `ConicAlgebra.IsComposition.isSplitOfRank_of_isSepClosed` : **`GPR 23.12`**, over a separably
  closed field every composition algebra of dimension `2`, `4`, or `8` is split.
* `ConicAlgebra.IsComposition.isomorphic_of_isSepClosed` : consequently there is exactly one in
  each dimension.
* `ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_quadraticEtale` : **`GPR 23.12`**
  with the hypothesis stated over quadratic étale algebras, as in the source.
* `ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_quadraticSubalgebra` : the same
  conclusion from the hypothesis restricted to the quadratic subalgebras of the algebra at hand.

## Implementation notes

⚠ Separably closed is strictly weaker than algebraically closed in characteristic `p`, and the
distinction is exactly the point of `GPR 23.12`: an inseparable extension of a separably closed
field of characteristic two is a purely inseparable quadratic algebra, which is *not* étale and
*not* the norm data of a composition algebra — see `Composition/Inseparable.lean`. The proof below
therefore never needs a square root of a general element in characteristic two.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.11, 22.18,
  23.12.
-/

@[expose] public section

universe u v w

open QuadraticMap (polar)

namespace ConicAlgebra

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A]
  {B : Type w} [NonAssocRing B] [Module K B] [SMulCommClass K B B] [IsScalarTower K B B]
  [Module.Finite K B] [Module.Projective K B]
  {C : ConicAlgebra K A} {D : ConicAlgebra K B} {r : ℕ}

/-! ### The quadratic polynomial attached to an element -/

omit [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A] in
/-- The norm along the line through `1` and `u`: `n(a·1 + u) = a² + t(u) a + n(u)`. This is the
polynomial whose roots are the null vectors of `C` in the plane `K·1 + K·u`. -/
theorem norm_smul_one_add (C : ConicAlgebra K A) (a : K) (u : A) :
    C.norm (a • (1 : A) + u) = a ^ 2 + C.trace u * a + C.norm u := by
  rw [C.norm_add, QuadraticMap.map_smul, C.norm_one, QuadraticMap.polar_smul_left,
    ← C.trace_apply, smul_eq_mul, smul_eq_mul, mul_one]
  ring

omit [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A] in
/-- **In characteristic two a regular norm has a nonzero trace somewhere.** If the trace vanished
identically, then `1` would lie in the kernel of the polar form, which regularity forbids. -/
theorem IsComposition.exists_trace_ne_zero_of_isGPRRegular (C : ConicAlgebra K A)
    (hreg : C.norm.IsGPRRegular) [Nontrivial A] : ∃ u : A, C.trace u ≠ 0 := by
  by_contra hcon
  have hzero : C.norm.polarBilin (1 : A) = 0 := by
    ext y
    simpa only [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, ← C.trace_apply]
      using not_not.mp (not_exists.mp hcon y)
  exact one_ne_zero ((injective_iff_map_eq_zero _).mp hreg.1 (1 : A) hzero)

/-! ### Separably closed fields -/

/-- **Over a separably closed field the norm of a composition algebra of dimension greater than one
is isotropic.** See the module docstring for the two characteristics. -/
theorem IsComposition.not_anisotropic_of_isSepClosed [IsSepClosed K]
    (h : C.IsComposition.{u, v, u}) (hA : 1 < Module.finrank K A) : ¬ C.norm.Anisotropic := by
  have := nontrivial_of_conicAlgebra C
  intro hani
  have hreg : C.norm.IsGPRRegular :=
    h.isGPRRegular_of_rankAtStalk_ne_one
      (Module.rankAtStalk_eq_of_finrank_eq (rfl : Module.finrank K A = Module.finrank K A))
      (by omega)
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- Characteristic two: pick `u` with `t(u) ≠ 0`; the polynomial is then separable.
    obtain ⟨u, hu⟩ := IsComposition.exists_trace_ne_zero_of_isGPRRegular C hreg
    obtain ⟨a, ha⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
      (n := 2) 1 (C.trace u) (C.norm u) (by exact_mod_cast h2) le_rfl hu
    have hnull : C.norm (a • (1 : A) + u) = 0 := by
      rw [C.norm_smul_one_add]
      linear_combination ha
    have hzero := hani _ hnull
    rw [add_comm] at hzero
    -- `u + a·1 = 0` makes `u = (-a)·1`, whose trace is `-2a = 0` in characteristic two.
    have hu' : u = (-a) • (1 : A) := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hzero
    exact hu (by rw [hu', map_smul, C.trace_one, smul_eq_mul, h2, mul_zero])
  · -- Characteristic other than two: complete the square.
    obtain ⟨u, hu⟩ : ∃ u : A, ∀ d : K, u ≠ d • (1 : A) := by
      by_contra hcon
      have : ∀ x : A, ∃ d : K, x = d • (1 : A) := by
        intro x
        by_contra hx
        exact hcon ⟨x, fun d hd ↦ hx ⟨d, hd⟩⟩
      exact absurd (finrank_le_one_of_forall_exists_smul (1 : A) this) (by omega)
    have : NeZero (2 : K) := ⟨h2⟩
    obtain ⟨e, he⟩ := IsSepClosed.exists_pow_nat_eq (C.trace u ^ 2 - 4 * C.norm u) 2
    set a : K := (-(C.trace u) + e) / 2 with hadef
    have hnull : C.norm (a • (1 : A) + u) = 0 := by
      rw [C.norm_smul_one_add, hadef]
      field_simp
      linear_combination he
    have hzero := hani _ hnull
    rw [add_comm] at hzero
    exact hu (-a) (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hzero)

/-- **`GPR 23.12`.** Over a separably closed field every composition algebra of dimension `2`, `4`,
or `8` is split. -/
theorem IsComposition.isSplitOfRank_of_isSepClosed [IsSepClosed K] (h : C.IsComposition.{u, v, u})
    (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8) : C.IsSplitOfRank r :=
  (h.isSplitOfRank_iff_not_anisotropic hA hr).mpr
    (h.not_anisotropic_of_isSepClosed (by rcases hr with rfl | rfl | rfl <;> omega))

/-- **`GPR 23.12`, uniqueness.** Over a separably closed field there is exactly one composition
algebra of each dimension `1`, `2`, `4`, `8`. -/
theorem IsComposition.isomorphic_of_isSepClosed [IsSepClosed K] (hC : C.IsComposition.{u, v, u})
    (hD : D.IsComposition.{u, w, u}) (hA : Module.finrank K A = r) (hB : Module.finrank K B = r)
    (hr : r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8) : C.Isomorphic D := by
  rcases hr with rfl | hr
  · exact (isSplitOfRank_one (Module.rankAtStalk_eq_of_finrank_eq hA)).isomorphic
      (isSplitOfRank_one (Module.rankAtStalk_eq_of_finrank_eq hB)) (Or.inl rfl)
  · exact (hC.isSplitOfRank_of_isSepClosed hA hr).isomorphic
      (hD.isSplitOfRank_of_isSepClosed hB hr) (by tauto)

/-! ### The hypothesis in its original form -/

/-- **`GPR 23.12`, subalgebra form.** Over a field over which every regular rank-two composition
subalgebra `K[u]` splits, every composition algebra of dimension `2`, `4`, or `8` is split.

This is the field case of
`ConicAlgebra.IsComposition.isSplitOfRank_of_forall_isSplit_adjoinElement`, whose proof runs over
an arbitrary LG ring. The hypothesis is weaker than quantifying over all quadratic étale algebras,
which is why `isSplitOfRank_of_forall_isSplit_quadraticEtale` above is proved through it. -/
theorem IsComposition.isSplitOfRank_of_forall_isSplit_quadraticSubalgebra
    (h : C.IsComposition.{u, v, u}) (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8)
    (hsplit : ∀ (u : A) (hu : C.RegularRankTwoCompositionStructure u),
      letI := C.adjoinElementCommRing u
      letI := C.adjoinElementAlgebra u
      letI : Module.Finite K (C.adjoinElement u) := C.finite_adjoinElement u
      letI : Module.Projective K (C.adjoinElement u) := hu.projective
      hu.conic.IsSplitOfRank 2) : C.IsSplitOfRank r :=
  h.isSplitOfRank_of_forall_isSplit_adjoinElement (isLGRing_of_field K)
    (Module.rankAtStalk_eq_of_finrank_eq hA) hr hsplit

/-- **`GPR 23.12`, with the hypothesis on quadratic étale algebras themselves.** Over a field over
which *every* quadratic étale algebra splits, every composition algebra of dimension `2`, `4`, or
`8` is split.

This is the statement `GPR 23.12` makes. It implies the subalgebra form below, because the regular
quadratic subalgebra `K[u]` produced by `GPR 19.16(b)` *is* a quadratic étale algebra: its
generator satisfies the degree-two identity, the coefficient map is bijective by regularity
(`GPR 19.8(ii) ⇔ (iii)`), and its discriminant is the unit `GPR 19.8(iii)` provides. The conic
structure carried by that subalgebra agrees with the one the presentation builds, because the norm
of a finitely generated projective conic algebra is unique (`GPR 16.7`, `GPR 19.3`) and a conic
algebra is determined by its norm. -/
theorem IsComposition.isSplitOfRank_of_forall_isSplit_quadraticEtale
    (h : C.IsComposition.{u, v, u}) (hA : Module.finrank K A = r) (hr : r = 2 ∨ r = 4 ∨ r = 8)
    (hsplit : ∀ (L : Type v) [CommRing L] [Algebra K L] (w : L) (t n₀ : K)
      (hq : IsQuadraticAlgebra w t n₀), IsUnit (t ^ 2 - 4 * n₀) → hq.conic.IsSplitOfRank 2) :
    C.IsSplitOfRank r := by
  refine h.isSplitOfRank_of_forall_isSplit_quadraticSubalgebra hA hr ?_
  intro u hu
  let := C.adjoinElementCommRing u
  let := C.adjoinElementAlgebra u
  let : Module.Finite K (C.adjoinElement u) := C.finite_adjoinElement u
  let : Module.Projective K (C.adjoinElement u) := hu.projective
  have hdisc : IsUnit (C.elementDiscriminant u) :=
    (C.isRegularRankTwoComposition_iff_isUnit_discriminant u).mp ⟨hu⟩
  -- The subalgebra, presented as an abstract quadratic algebra on the generator `u`.
  have humem : u ∈ C.adjoinElement u := ⟨(0, 1), by simp⟩
  have hq : IsQuadraticAlgebra (⟨u, humem⟩ : C.adjoinElement u) (C.trace u) (C.norm u) := by
    constructor
    · exact Subtype.ext (C.mul_self_eq u)
    · have hmap : spanOne K (⟨u, humem⟩ : C.adjoinElement u) =
          (C.quadraticSpanEquiv hdisc).toLinearMap :=
        LinearMap.ext fun _ ↦ Subtype.ext rfl
      rw [hmap]
      exact (C.quadraticSpanEquiv hdisc).bijective
  -- Its discriminant is the one `GPR 19.8(iii)` supplies.
  have hdisc' : IsUnit (C.trace u ^ 2 - 4 * C.norm u) := hdisc
  -- The two conic structures on the subalgebra have the same norm, hence are equal.
  have hnorm : hq.conic = hu.conic := ConicAlgebra.ext (norm_eq_of_projective hq.conic hu.conic)
  exact hnorm ▸ hsplit (C.adjoinElement u) _ (C.trace u) (C.norm u) hq hdisc'

end ConicAlgebra
