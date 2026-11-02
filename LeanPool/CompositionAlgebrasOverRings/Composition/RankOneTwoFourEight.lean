/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Tower
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAlternative
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAssociative
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Semilocal

/-!
# The rank of a composition algebra is 1, 2, 4 or 8 (`GPR 19.18`)

A composition algebra of constant rank over a nontrivial commutative ring is the base ring in
rank `1`; commutative associative with nontrivial conjugation in rank `2`; associative and
noncommutative in rank `4`; or alternative and nonassociative in rank `8`. In particular its rank
is `1`, `2`, `4`, or `8`. The positive identities descend from localizations, while the negative
ones are detected over a residue field.

⚠ **No LG hypothesis.** The tower that proves the field case runs over a field, and every field is
an LG ring, so nothing here assumes `IsLGRing k`.

## The two halves

**The rank is a power of two.** That is `GPR 19.17` (`Composition/Tower.lean`): a composition
algebra of dimension `r > 2` is a Cayley–Dickson double of a composition subalgebra of dimension
`r / 2`. Iterating halves the dimension until it reaches `2`.

**The tower stops at eight.** That is the converse half of `GPR 18.14(c)`
(`Conic/CayleyDicksonAlternative.lean`), and it is what the descent below is for. Reading the
chain downwards from a hypothetical algebra of dimension `16`:

* it is alternative — every composition algebra over a field is (`GPR 19.3`) — and it is a double,
  so its eight-dimensional half is **associative** (`ConicAlgebra.mul_assoc_of_isAlternative_cay`);
* an associative double forces its own half to be **commutative**
  (`ConicAlgebra.exists_mul_mul_ne_mul_mul_cay`, contrapositive), so the four-dimensional rung is
  commutative;
* a commutative double forces the conjugation of its half to be the **identity**
  (`ConicAlgebra.exists_mul_ne_mul_cay`, contrapositive), so the two-dimensional rung has
  `conj x = x`;
* but a composition algebra with trivial conjugation has dimension at most one
  (`ConicAlgebra.IsComposition.finrank_le_one_of_conj_eq_id`) — contradiction.

Only the first bullet is new; the middle two are the explicit witnesses already in
`Conic/CayleyDicksonAssociative.lean`, used in the contrapositive direction they were built for.

## The bottom of the descent

`finrank_le_one_of_conj_eq_id` is where the two characteristics part company. `conj x = x` reads
`2x = t(x) · 1`. When `2 ≠ 0` every element is therefore a scalar multiple of `1`, and the
dimension is at most one outright. When `2 = 0` it reads `t(x) · 1 = 0`, so `t ≡ 0` because
`1 ≠ 0`; then `n(1, y) = t(y) = 0` for every `y`, so `1` is a nonzero vector in the kernel of the
polar form, the norm is not regular, and `GPR 19.11` (`Composition/RankDichotomy.lean`) leaves only
dimension one. The characteristic-two branch is the one that needs `19.11`, and it is the reason
this file depends on it.

## Implementation notes

Each rung is identified with the next by `ConicAlgebra.cayToAlgebra`, a `LinearMap` that happens
to be bijective and multiplicative but is not a bundled algebra map, so alternativity,
associativity and commutativity are moved across by hand (`isAlternative_of_injective` and
friends). Injectivity alone suffices in every case.

The induction runs over the carrier type as well as the dimension, since each rung is a subalgebra
of the previous one and so a different type.

## Main results

* `ConicAlgebra.IsComposition.rankAtStalk_classification` : full **`GPR 19.18`**, including the
  structure in each of the four ranks.
* `ConicAlgebra.IsComposition.rankAtStalk_eq_one_or_two_or_four_or_eight` : its rank-only part.
* `ConicAlgebra.IsComposition.finrank_eq_one_or_two_or_four_or_eight` : the same over a field.
* `ConicAlgebra.mul_comm_of_rankAtStalk_eq_two`, `ConicAlgebra.mul_assoc_of_rankAtStalk_eq_two` :
  a finitely generated projective conic algebra of constant rank two over any commutative ring is
  commutative and associative (`GPR 16.4`); no composition hypothesis is needed.
* `ConicAlgebra.IsComposition.finrank_le_four_of_mul_assoc`,
  `ConicAlgebra.IsComposition.finrank_le_two_of_mul_comm`,
  `ConicAlgebra.IsComposition.finrank_le_one_of_conj_eq_id` : the three steps of the descent.
* `ConicAlgebra.not_isComposition_of_finrank_notMem` : the contrapositive. Applied to the
  sixteen-dimensional double of an octonion algebra it says the **sedenions** are not a composition
  algebra (`GPR 19.23`).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 16.4, 18.14(c),
  19.3, 19.11, 19.17, 19.18.
-/

@[expose] public section

universe u v w

open QuadraticMap (polar)
open scoped TensorProduct

/-! ### Transporting multiplicative properties along an injective multiplicative map

Each rung of the Cayley–Dickson tower is identified with an algebra by a bijection that is
multiplicative but is not an algebra homomorphism of any bundled kind (`ConicAlgebra.cayToAlgebra`
is a `LinearMap`), so the properties have to be moved by hand. Injectivity alone suffices in every
case — surjectivity is never used. -/

section Transport

variable {X : Type v} {Y : Type w} [Mul X] [Mul Y] (f : X → Y) (hf : Function.Injective f)
  (hmul : ∀ p q, f (p * q) = f p * f q)
include hf hmul

/-- Alternativity pulls back along an injective multiplicative map. -/
theorem isAlternative_of_injective [IsAlternative Y] : IsAlternative X where
  left_alt a b := hf (by simp only [hmul]; exact IsAlternative.left_alt _ _)
  right_alt a b := hf (by simp only [hmul]; exact IsAlternative.right_alt _ _)

/-- Associativity pulls back along an injective multiplicative map. -/
theorem mul_assoc_of_injective (h : ∀ a b c : Y, a * b * c = a * (b * c)) (a b c : X) :
    a * b * c = a * (b * c) :=
  hf (by simp only [hmul]; exact h _ _ _)

/-- Commutativity pulls back along an injective multiplicative map. -/
theorem mul_comm_of_injective (h : ∀ a b : Y, a * b = b * a) (a b : X) : a * b = b * a :=
  hf (by simp only [hmul]; exact h _ _)

end Transport

/-- A unital subalgebra of an alternative algebra is alternative: both laws are checked on
elements of the ambient algebra. -/
instance NonAssocSubalgebra.isAlternative {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A]
    [Module k A] [IsAlternative A] (B : NonAssocSubalgebra k A) : IsAlternative B :=
  isAlternative_of_injective (fun x ↦ (x : A)) Subtype.val_injective fun _ _ ↦ rfl

namespace Module

/-- Over a field, `Module.rankAtStalk` is the dimension. -/
theorem finrank_of_rankAtStalk_eq {F : Type u} [Field F] {X : Type v} [AddCommGroup X]
    [Module F X] {s : ℕ} (h : Module.rankAtStalk (R := F) X = fun _ ↦ s) :
    Module.finrank F X = s := by
  have hb := congrFun h ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hb

/-- Over a field, the dimension is `Module.rankAtStalk`. -/
theorem rankAtStalk_eq_of_finrank_eq {F : Type u} [Field F] {X : Type v} [AddCommGroup X]
    [Module F X] {s : ℕ} (h : Module.finrank F X = s) :
    Module.rankAtStalk (R := F) X = fun _ ↦ s := by
  rw [Module.rankAtStalk_eq_finrank_of_free, h]
  rfl

end Module

namespace ConicAlgebra

variable {F : Type u} {A : Type v} [Field F] [NonAssocRing A] [Module F A]
  [SMulCommClass F A A] [IsScalarTower F A A] [Module.Finite F A] [Module.Projective F A]
  {C : ConicAlgebra F A}

/-- Over a field a unital subalgebra of a finite-dimensional algebra is finite-dimensional. The
corresponding statement for its underlying submodule is found by instance search; this moves it
across `ConicAlgebra.toSubmoduleEquiv`, which instance search will not do on its own. -/
instance finite_nonAssocSubalgebra (B : NonAssocSubalgebra F A) : Module.Finite F B :=
  Module.Finite.equiv (toSubmoduleEquiv B)

/-- **`GPR 19.17` over a field, in dimensions.** A composition algebra of dimension `r > 2` over a
field is a Cayley–Dickson double of a composition subalgebra of dimension `r / 2`.

This is `ConicAlgebra.IsComposition.exists_bijective_cayToAlgebra` with `Module.rankAtStalk`
traded for `Module.finrank` — over a field the two agree — and with the subalgebra packaged as a
composition algebra in its own right, which is what lets the statement be applied to it again. -/
theorem IsComposition.exists_isComposition_finrank_of_two_lt (h : C.IsComposition.{u, v, u})
    {r : ℕ} (hr : Module.finrank F A = r) (h2 : 2 < r) :
    ∃ (B : NonAssocSubalgebra F A) (v : A) (s : ℕ),
      2 * s = r ∧ Module.finrank F B = s ∧ (C.restrict B).IsComposition.{u, v, u} ∧
      Function.Injective (cayToAlgebra C B v) ∧
      (∀ p q, cayToAlgebra C B v (p * q) = cayToAlgebra C B v p * cayToAlgebra C B v q) := by
  have := h.isAlternative
  obtain ⟨B, v, s, hs2, hsrank, hunit, hBreg, hbij, -, hmulmap, -⟩ :=
    h.exists_bijective_cayToAlgebra (isLGRing_of_field F) (Module.rankAtStalk_eq_of_finrank_eq hr)
      h2
  refine ⟨B, v, s, hs2, ?_, ⟨hBreg.isGPRNonsingular, h.isMultiplicative.restrict⟩, hbij.1,
    hmulmap⟩
  exact Module.finrank_of_rankAtStalk_eq ((rankAtStalk_toSubmodule B) ▸ hsrank)

/-! ### The bottom of the tower: trivial conjugation forces dimension one -/

omit [SMulCommClass F A A] [IsScalarTower F A A] [Module.Finite F A] [Module.Projective F A] in
/-- A conic algebra over a nontrivial base is nonzero, because `n(1) = 1`. -/
theorem nontrivial_of_conicAlgebra (C : ConicAlgebra F A) : Nontrivial A := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have h1 : (1 : A) = 0 := Subsingleton.elim _ _
  have := C.norm_one
  rw [h1, map_zero] at this
  exact zero_ne_one this

/-- **The last step of the descent.** A composition algebra over a field whose conjugation is the
identity has dimension at most one.

The two characteristics are genuinely different. When `2 ≠ 0`, `conj x = x` reads `2x = t(x) · 1`,
so every element is a scalar multiple of `1` outright. When `2 = 0` it reads `t(x) · 1 = 0`, hence
`t ≡ 0` since `1 ≠ 0`; then `n(1, y) = t(y) = 0` for every `y`, so `1` is a nonzero vector in the
kernel of the polar form, the norm is not regular, and `GPR 19.11` leaves only dimension one. -/
theorem IsComposition.finrank_le_one_of_conj_eq_id (h : C.IsComposition.{u, v, u})
    (hconj : ∀ x : A, C.conj x = x) : Module.finrank F A ≤ 1 := by
  have := nontrivial_of_conicAlgebra C
  have hkey : ∀ x : A, x + x = C.trace x • (1 : A) := fun x ↦ by
    calc x + x = x + C.conj x := by rw [hconj]
      _ = C.trace x • (1 : A) := C.add_conj x
  by_cases h2 : (2 : F) = 0
  · by_contra hgt
    replace hgt : 1 < Module.finrank F A := Nat.not_le.mp hgt
    have htrace : ∀ x : A, C.trace x = 0 := by
      intro x
      have hx : C.trace x • (1 : A) = 0 := by
        rw [← hkey x, ← two_smul F x, h2, zero_smul]
      rcases smul_eq_zero.mp hx with h' | h'
      · exact h'
      · exact absurd h' one_ne_zero
    have hmem : QuadraticMap.polarBilin C.norm 1 = 0 := by
      ext y
      rw [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply, ← C.trace_apply, htrace]
    have hnotreg : ¬ C.norm.IsGPRRegular := fun hreg ↦
      one_ne_zero ((injective_iff_map_eq_zero _).mp hreg.1 1 hmem)
    rcases h.isGPRRegular_or_finrank_eq_one with hreg | ⟨hdim, -⟩
    · exact hnotreg hreg
    · omega
  · have hinv : ∀ x : A, ((2 : F)⁻¹ * C.trace x) • (1 : A) = x := by
      intro x
      rw [mul_smul, ← hkey x, ← two_smul F x, inv_smul_smul₀ h2]
    exact finrank_le_one (1 : A) fun x ↦ ⟨(2 : F)⁻¹ * C.trace x, hinv x⟩

/-! ### Climbing back up: commutative, then associative -/

/-- **A commutative composition algebra over a field has dimension at most two.** If it were
larger it would be a double `Cay(B, μ)`, and a commutative double forces the conjugation of `B` to
be the identity (`ConicAlgebra.exists_mul_ne_mul_cay`, contrapositive), which caps `B` at
dimension one and so the algebra itself at dimension two. -/
theorem IsComposition.finrank_le_two_of_mul_comm (h : C.IsComposition.{u, v, u})
    (hcomm : ∀ a b : A, a * b = b * a) : Module.finrank F A ≤ 2 := by
  by_contra hgt
  replace hgt : 2 < Module.finrank F A := Nat.not_le.mp hgt
  obtain ⟨B, v, s, hs2, hBrank, hBcomp, hinj, hmulmap⟩ :=
    h.exists_isComposition_finrank_of_two_lt rfl hgt
  have hcay : ∀ p q : Cay (C.restrict B) (-C.norm v), p * q = q * p :=
    mul_comm_of_injective _ hinj hmulmap hcomm
  have hid : ∀ b : B, (C.restrict B).conj b = b := by
    intro b
    by_contra hne
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_cay (C.restrict B) (-C.norm v) hne
    exact hxy (hcay x y)
  have hle := hBcomp.finrank_le_one_of_conj_eq_id hid
  omega

/-- **An associative composition algebra over a field has dimension at most four.** The same
descent one rung higher: an associative double forces its input to be commutative
(`ConicAlgebra.exists_mul_mul_ne_mul_mul_cay`, contrapositive), which caps the input at dimension
two. This is what rules out an associative rank-eight algebra, and hence a ninth rung. -/
theorem IsComposition.finrank_le_four_of_mul_assoc (h : C.IsComposition.{u, v, u})
    (hassoc : ∀ a b c : A, a * b * c = a * (b * c)) : Module.finrank F A ≤ 4 := by
  by_contra hgt
  replace hgt : 4 < Module.finrank F A := Nat.not_le.mp hgt
  obtain ⟨B, v, s, hs2, hBrank, hBcomp, hinj, hmulmap⟩ :=
    h.exists_isComposition_finrank_of_two_lt rfl (by omega)
  have := hBcomp.isAlternative
  have hcay : ∀ p q r : Cay (C.restrict B) (-C.norm v), p * q * r = p * (q * r) :=
    mul_assoc_of_injective _ hinj hmulmap hassoc
  have hcomm : ∀ a b : B, a * b = b * a := by
    intro a b
    by_contra hne
    obtain ⟨x, y, z, hxyz⟩ := exists_mul_mul_ne_mul_mul_cay (C.restrict B) (-C.norm v)
      (C.restrict B).conjIsInvolution_of_projective hne
    exact hxyz (hcay x y z)
  have hle := hBcomp.finrank_le_two_of_mul_comm hcomm
  omega

/-! ### `GPR 19.18` over a field -/

variable (F) in
/-- The induction behind `GPR 19.18` over a field, with an explicit fuel parameter `n` bounding
the dimension. The type varies from step to step — each rung is a subalgebra of the previous one —
so the induction quantifies over the carrier as well. -/
private theorem finrank_mem_aux (n : ℕ) :
    ∀ {X : Type v} [NonAssocRing X] [Module F X] [SMulCommClass F X X] [IsScalarTower F X X]
      [Module.Finite F X] [Module.Projective F X] (D : ConicAlgebra F X),
      D.IsComposition.{u, v, u} → Module.finrank F X ≤ n →
      Module.finrank F X = 1 ∨ Module.finrank F X = 2 ∨ Module.finrank F X = 4 ∨
        Module.finrank F X = 8 := by
  induction n with
  | zero =>
    intro X _ _ _ _ _ _ D hD hle
    have := nontrivial_of_conicAlgebra D
    have := Module.finrank_pos (R := F) (M := X)
    omega
  | succ n ih =>
    intro X _ _ _ _ _ _ D hD hle
    have := nontrivial_of_conicAlgebra D
    have hpos := Module.finrank_pos (R := F) (M := X)
    by_cases hsmall : Module.finrank F X ≤ 2
    · omega
    · replace hsmall : 2 < Module.finrank F X := Nat.not_le.mp hsmall
      obtain ⟨B, v, s, hs2, hBrank, hBcomp, hinj, hmulmap⟩ :=
        hD.exists_isComposition_finrank_of_two_lt rfl hsmall
      have := hD.isAlternative
      have : IsAlternative (Cay (D.restrict B) (-D.norm v)) :=
        isAlternative_of_injective _ hinj hmulmap
      have hle4 := hBcomp.finrank_le_four_of_mul_assoc
        (mul_assoc_of_isAlternative_cay (D.restrict B) (-D.norm v) inferInstance)
      have hih := ih (D.restrict B) hBcomp (by omega)
      omega

/-- **`GPR 19.18` over a field.** A composition algebra over a field has dimension `1`, `2`, `4`
or `8`.

The tower of `GPR 19.17` halves the dimension at every step, so it is a power of two; what stops
it at eight is the converse half of `GPR 18.14(c)`. A ninth rung would make the eight-dimensional
one associative (`ConicAlgebra.mul_assoc_of_isAlternative_cay`, applied to the alternativity that
every composition algebra over a field has), and
`ConicAlgebra.IsComposition.finrank_le_four_of_mul_assoc` says no associative composition algebra
gets past dimension four. -/
theorem IsComposition.finrank_eq_one_or_two_or_four_or_eight (h : C.IsComposition.{u, v, u}) :
    Module.finrank F A = 1 ∨ Module.finrank F A = 2 ∨ Module.finrank F A = 4 ∨
      Module.finrank F A = 8 :=
  finrank_mem_aux F (Module.finrank F A) C h le_rfl

end ConicAlgebra

/-! ### `GPR 19.18` over a commutative ring

The rank is a fibrewise invariant, so the general case is the field case read off at a single
residue field. In particular **no LG hypothesis is needed**: the tower that proves the field case
runs over a field, and every field is an LG ring. -/

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A] [Module.Projective k A]
  {C : ConicAlgebra k A}

/-- Over an LG ring, a rank-four composition algebra is associative. It is a double of its
rank-two associative commutative subalgebra, so `GPR 18.14(b)` applies. -/
theorem IsComposition.mul_assoc_of_isLGRing_of_rankAtStalk_eq_four [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) (hLG : IsLGRing k)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) (x y z : A) :
    x * y * z = x * (y * z) := by
  obtain ⟨B, a, s, hs, hB, ha, hreg, hbij, -, hmul, -⟩ :=
    h.exists_bijective_cayToAlgebra hLG hA (by omega)
  have hs2 : s = 2 := by omega
  subst s
  let : Module.Finite k B := by
    have := QuadraticForm.finite_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Finite.equiv (toSubmoduleEquiv B)
  let : Module.Projective k B := by
    have := QuadraticForm.projective_of_comp_isGPRRegular (Q := C.norm) hreg
    exact Module.Projective.of_equiv (toSubmoduleEquiv B)
  have hBassoc := (C.restrict B).mul_assoc_of_isLGRing_of_rankAtStalk_eq_two hLG
    ((rankAtStalk_toSubmodule B).symm.trans hB)
  have hBcomm := (C.restrict B).mul_comm_of_isLGRing_of_rankAtStalk_eq_two hLG
    ((rankAtStalk_toSubmodule B).symm.trans hB)
  let : CommRing B :=
    { (inferInstance : NonAssocRing B) with mul_assoc := hBassoc, mul_comm := hBcomm }
  let : Algebra k B := Algebra.ofModule
    (fun r (p q : B) ↦ by exact smul_mul_assoc r p q)
    (fun r (p q : B) ↦ by
      rw [hBcomm p (r • q), hBcomm p q]
      exact smul_mul_assoc r q p)
  obtain ⟨px, hpx⟩ := hbij.2 x
  obtain ⟨py, hpy⟩ := hbij.2 y
  obtain ⟨pz, hpz⟩ := hbij.2 z
  rw [← hpx, ← hpy, ← hpz, ← hmul, ← hmul, ← hmul, ← hmul]
  exact congrArg (cayToAlgebra C B a)
    (mul_assoc_cay (C.restrict B) (-C.norm a)
      (C.restrict B).conjIsInvolution_of_projective px py pz)

omit [SMulCommClass k A A] [IsScalarTower k A A] [Module.Finite k A]
  [Module.Projective k A] in
/-- Equality in a module can be checked after localizing at every maximal ideal, using tensor
product models for the localized modules. -/
theorem eq_of_forall_localization_maximal (x y : A)
    (hxy : ∀ (P : Ideal k) [P.IsMaximal],
      (1 : Localization.AtPrime P) ⊗ₜ[k] x =
        (1 : Localization.AtPrime P) ⊗ₜ[k] y) : x = y :=
  Module.eq_of_localization_maximal
    (fun P _ ↦ Localization.AtPrime P ⊗[k] A)
    (fun P _ ↦ TensorProduct.mk k (Localization.AtPrime P) A 1)
    x y hxy

/-- A finitely generated projective conic algebra of constant rank two over an arbitrary
commutative ring is commutative (`GPR 16.4`); for composition algebras this is the positive part of
`GPR 19.18(b)`. It is checked at each localization at a maximal ideal, where the algebra is `k[u]`
(`ConicAlgebra.mul_comm_of_isLGRing_of_rankAtStalk_eq_two`). -/
theorem mul_comm_of_rankAtStalk_eq_two (C : ConicAlgebra k A)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) (x y : A) : x * y = y * x := by
  apply eq_of_forall_localization_maximal (k := k)
  intro P hP
  let S := Localization.AtPrime P
  have hSrank := Module.rankAtStalk_baseChange_of_eq S hA
  have hLG : IsLGRing S := isLGRing_of_isLocalRing S
  simpa only [one_tmul_mul] using
    (C.baseChangeOfProjective S).mul_comm_of_isLGRing_of_rankAtStalk_eq_two hLG hSrank
      (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)

/-- A finitely generated projective conic algebra of constant rank two over an arbitrary
commutative ring is associative (`GPR 16.4`); for composition algebras this is the positive part of
`GPR 19.18(b)`. It is checked at each localization at a maximal ideal, where the algebra is `k[u]`
(`ConicAlgebra.mul_assoc_of_isLGRing_of_rankAtStalk_eq_two`). -/
theorem mul_assoc_of_rankAtStalk_eq_two (C : ConicAlgebra k A)
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) (x y z : A) : x * y * z = x * (y * z) := by
  apply eq_of_forall_localization_maximal (k := k)
  intro P hP
  let S := Localization.AtPrime P
  have hSrank := Module.rankAtStalk_baseChange_of_eq S hA
  have hLG : IsLGRing S := isLGRing_of_isLocalRing S
  simpa only [one_tmul_mul] using
    (C.baseChangeOfProjective S).mul_assoc_of_isLGRing_of_rankAtStalk_eq_two hLG hSrank
      (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y) (1 ⊗ₜ[k] z)

/-- A constant-rank-four composition algebra over an arbitrary commutative ring is
associative. This is the positive part of `GPR 19.18(c)`. -/
theorem IsComposition.mul_assoc_of_rankAtStalk_eq_four
    (h : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4)
    (x y z : A) : x * y * z = x * (y * z) := by
  apply eq_of_forall_localization_maximal (k := k)
  intro P hP
  let S := Localization.AtPrime P
  have hSrank := Module.rankAtStalk_baseChange_of_eq S hA
  have hLG : IsLGRing S := isLGRing_of_isLocalRing S
  simpa only [one_tmul_mul] using
    (h.baseChangeOfProjective S).mul_assoc_of_isLGRing_of_rankAtStalk_eq_four hLG hSrank
      (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y) (1 ⊗ₜ[k] z)

/-- A constant-rank-two composition algebra over a nonzero ring has nontrivial conjugation. -/
theorem IsComposition.exists_conj_ne_of_rankAtStalk_eq_two [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 2) :
    ∃ x : A, C.conj x ≠ x := by
  by_contra hn
  push Not at hn
  obtain ⟨P, hP⟩ := Ideal.exists_maximal k
  let : P.IsMaximal := hP
  let F := k ⧸ P
  let : Field F := Ideal.Quotient.field P
  let CF := C.baseChangeOfProjective F
  have hconjF : ∀ x : F ⊗[k] A, CF.conj x = x := by
    intro x
    induction x with
    | tmul r a => simp [CF, hn]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hdim : Module.finrank F (F ⊗[k] A) = 2 :=
    Module.finrank_baseChange_of_rankAtStalk_eq hA F
  have hle := (h.baseChangeOfProjective F).finrank_le_one_of_conj_eq_id hconjF
  omega

/-- A constant-rank-four composition algebra over a nonzero ring is not commutative. -/
theorem IsComposition.not_mul_comm_of_rankAtStalk_eq_four [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 4) :
    ¬ ∀ x y : A, x * y = y * x := by
  intro hcomm
  have hassoc := h.mul_assoc_of_rankAtStalk_eq_four hA
  let : CommRing A :=
    { (inferInstance : NonAssocRing A) with mul_assoc := hassoc, mul_comm := hcomm }
  let : Algebra k A := Algebra.ofModule
    (fun r (x y : A) ↦ by exact smul_mul_assoc r x y)
    (fun r (x y : A) ↦ by exact (smul_comm r x y).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal k
  let : P.IsMaximal := hP
  let F := k ⧸ P
  let : Field F := Ideal.Quotient.field P
  have hdim : Module.finrank F (F ⊗[k] A) = 4 :=
    Module.finrank_baseChange_of_rankAtStalk_eq hA F
  have hle := (h.baseChangeOfProjective F).finrank_le_two_of_mul_comm fun x y ↦ mul_comm x y
  omega

/-- A constant-rank-eight composition algebra over a nonzero ring is not associative. -/
theorem IsComposition.not_mul_assoc_of_rankAtStalk_eq_eight [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    ¬ ∀ x y z : A, x * y * z = x * (y * z) := by
  intro hassoc
  let : Ring A := { (inferInstance : NonAssocRing A) with mul_assoc := hassoc }
  let : Algebra k A := Algebra.ofModule
    (fun r (x y : A) ↦ by exact smul_mul_assoc r x y)
    (fun r (x y : A) ↦ by exact (smul_comm r x y).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal k
  let : P.IsMaximal := hP
  let F := k ⧸ P
  let : Field F := Ideal.Quotient.field P
  have hdim : Module.finrank F (F ⊗[k] A) = 8 :=
    Module.finrank_baseChange_of_rankAtStalk_eq hA F
  have hle := (h.baseChangeOfProjective F).finrank_le_four_of_mul_assoc fun x y z ↦
    mul_assoc x y z
  omega

/-- A constant-rank-one conic algebra is isomorphic, as a unital non-associative algebra, to its
base ring. This is `GPR 19.18(a)` in the project's unbundled isomorphism convention. -/
theorem exists_linearEquiv_map_one_map_mul_of_rankAtStalk_eq_one [Nontrivial k]
    (C : ConicAlgebra k A) (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 1) :
    ∃ e : A ≃ₗ[k] k, e (1 : A) = 1 ∧ ∀ x y, e (x * y) = e x * e y := by
  let e : A ≃ₗ[k] k :=
    { toLinearMap := C.unitForm
      invFun := fun r ↦ r • (1 : A)
      left_inv := fun x ↦ (C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA x).symm
      right_inv := fun r ↦ by simp }
  refine ⟨e, C.unitForm_one, fun x y ↦ ?_⟩
  change C.unitForm (x * y) = C.unitForm x * C.unitForm y
  rw [C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA x,
    C.eq_unitForm_smul_one_of_rankAtStalk_eq_one hA y]
  simp only [smul_mul_smul_comm, map_smul, C.unitForm_one, smul_eq_mul, mul_one]

/-- **`GPR 19.18`.** A composition algebra of constant rank over a nontrivial commutative ring has
rank `1`, `2`, `4` or `8`.

Base change to the residue field at any maximal ideal is a composition algebra over a field of the
same dimension (`ConicAlgebra.finrank_quotient_tensor_eq_rankAtStalk`), so this is
`ConicAlgebra.IsComposition.finrank_eq_one_or_two_or_four_or_eight` read at one point of
`Spec k`. -/
theorem IsComposition.rankAtStalk_eq_one_or_two_or_four_or_eight [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hrank : Module.rankAtStalk (R := k) A = fun _ ↦ r) :
    r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal k
  have : 𝔪.IsMaximal := h𝔪
  let : Field (k ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hdim : Module.finrank (k ⧸ 𝔪) ((k ⧸ 𝔪) ⊗[k] A) = r := by
    rw [finrank_quotient_tensor_eq_rankAtStalk, hrank]
  have hfield := (h.baseChangeOfProjective (k ⧸ 𝔪)).finrank_eq_one_or_two_or_four_or_eight
  rwa [hdim] at hfield

/-- **Full `GPR 19.18`.** Besides the rank restriction, this records the algebraic structure in
each possible constant rank: rank one is the base ring; rank two is commutative associative with
nontrivial conjugation; rank four is associative but not commutative; and rank eight is
alternative but not associative. -/
theorem IsComposition.rankAtStalk_classification [Nontrivial k]
    (h : C.IsComposition.{u, v, u}) {r : ℕ}
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ r) :
    (r = 1 ∧ ∃ e : A ≃ₗ[k] k, e (1 : A) = 1 ∧ ∀ x y, e (x * y) = e x * e y) ∨
      (r = 2 ∧ (∀ x y : A, x * y = y * x) ∧
        (∀ x y z : A, x * y * z = x * (y * z)) ∧ ∃ x, C.conj x ≠ x) ∨
      (r = 4 ∧ (∀ x y z : A, x * y * z = x * (y * z)) ∧
        ¬ ∀ x y : A, x * y = y * x) ∨
      (r = 8 ∧ IsAlternative A ∧ ¬ ∀ x y z : A, x * y * z = x * (y * z)) := by
  rcases h.rankAtStalk_eq_one_or_two_or_four_or_eight hA with h1 | h2 | h4 | h8
  · subst r
    exact Or.inl ⟨rfl, exists_linearEquiv_map_one_map_mul_of_rankAtStalk_eq_one C hA⟩
  · subst r
    exact Or.inr <| Or.inl ⟨rfl, C.mul_comm_of_rankAtStalk_eq_two hA,
      C.mul_assoc_of_rankAtStalk_eq_two hA, h.exists_conj_ne_of_rankAtStalk_eq_two hA⟩
  · subst r
    exact Or.inr <| Or.inr <| Or.inl
      ⟨rfl, h.mul_assoc_of_rankAtStalk_eq_four hA, h.not_mul_comm_of_rankAtStalk_eq_four hA⟩
  · subst r
    exact Or.inr <| Or.inr <| Or.inr
      ⟨rfl, h.isAlternative_general, h.not_mul_assoc_of_rankAtStalk_eq_eight hA⟩

end ConicAlgebra

namespace ConicAlgebra

variable {F : Type u} {A : Type v} [Field F] [NonAssocRing A] [Module F A]
  [SMulCommClass F A A] [IsScalarTower F A A] [Module.Finite F A] [Module.Projective F A]

/-- **The dimension obstruction.** A conic algebra over a field whose dimension is none of
`1, 2, 4, 8` is not a composition algebra — no choice of conic norm on it permits composition.

Applied to the sixteen-dimensional double of an octonion algebra this says the **sedenions** are
not a composition algebra (`GPR 19.23`), with no computation of an associator: the dimension alone
rules it out. -/
theorem not_isComposition_of_finrank_notMem (C : ConicAlgebra F A) (h1 : Module.finrank F A ≠ 1)
    (h2 : Module.finrank F A ≠ 2) (h4 : Module.finrank F A ≠ 4)
    (h8 : Module.finrank F A ≠ 8) :
    ¬ C.IsComposition.{u, v, u} := fun h ↦ by
  rcases h.finrank_eq_one_or_two_or_four_or_eight with h' | h' | h' | h'
  exacts [h1 h', h2 h', h4 h', h8 h']

end ConicAlgebra
