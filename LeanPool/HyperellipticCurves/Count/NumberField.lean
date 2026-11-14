/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.Main
public import LeanPool.HyperellipticCurves.Count.NumberFieldFactor
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

import LeanPool.HyperellipticCurves.ForMathlib.Ideal
import LeanPool.HyperellipticCurves.ForMathlib.Resultant
import LeanPool.HyperellipticCurves.ForMathlib.SetCard
import LeanPool.HyperellipticCurves.ForMathlib.Squarefree
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# The Chabauty–Coleman bound over number fields

The assembly of blueprint `lem:factor-arithmetic`, `thm:main-nf` and `cor:finiteness-nf`:
for a prime `v` of `A` over `p` with ramification index `e`, the certificates of
`LeanPool.HyperellipticCurves.Count.NumberFieldRing` and
`LeanPool.HyperellipticCurves.Count.NumberFieldFactor` are
produced (the embedding `σ` of the residue field into `𝔽_barp`, the factorization `p·A = 𝔭^e·J`, the
uniformizer certificate `(ϖ) = 𝔭·C`, and the idempotent `ε`), the ring of `v`-integers
`O₀ = A_v ⊆ K` (Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`) is
mapped into the factor, and the abstract theorems of `LeanPool.HyperellipticCurves.Count.Main` are
instantiated for a polynomial `f : K[X]` with `v`-integral coefficients — given as the image of a
polynomial `fA` over `A_v`, whose reduction modulo the maximal ideal is the reduction of `f`
at `v`. The prime-free finiteness corollary (blueprint `cor:finiteness-nf`) chooses the
prime itself: any rational prime beyond `2r + rank + 1` and beyond the norm of an element of
`A` collecting a denominator of `f` and the numerator and denominator of the resultant of `f`
with `f'` admits a good prime `v` of `A` above it, since the ramification index is at most
the rank.

Throughout, `A` is any Dedekind domain that is finite free over `ℤ`, with fraction field
`K` — the ring of integers of a number field, or `ℤ` itself at `K = ℚ` (this is how
`LeanPool.HyperellipticCurves.Count.Arithmetic` derives the statements over `ℚ` and `ℤ`). The public
statements mention no residue characteristic: it is read off `v` as the characteristic of its
residue field, and the ramification index as `Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal`.
The versions for polynomials with coefficients in `A`, with the reduction taken in `A ⧸ 𝔭`
at a maximal ideal `𝔭` (`main_affine_numberField_int`, `ratPoints_finite_numberField_int`),
are corollaries.

## Main statements

* `ChabautyColeman.NumberFieldBase.main_affine_numberField` (blueprint `thm:main-nf`): the
  point-count bound over `K` at a prime `v` of `A` at which `f` is integral.
* `ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField` (blueprint
  `cor:finiteness-nf`): finiteness of the affine `K`-solution set of `y² = f(x)` for a monic
  squarefree `f : K[X]` of odd degree, with no prime occurring in the statement.
* `ChabautyColeman.NumberFieldBase.exists_prime_squarefree_reduction`: a monic squarefree
  polynomial over `K` is integral, with squarefree reduction, at a prime of `A` above an
  arbitrarily large rational prime.
* `ChabautyColeman.NumberFieldBase.exists_factorData`: the certificates collected in
  `ChabautyColeman.NumberFieldBase.FactorData` all exist at a maximal ideal above `p`.
* `ChabautyColeman.NumberFieldBase.resO_injective` and
  `ChabautyColeman.NumberFieldBase.exists_algebraMap_eq` (blueprint `lem:factor-arithmetic`):
  `A` embeds into the local factor, and integrality there descends to `A_v`.
-/

@[expose] public section

open Polynomial IsLocalRing IsDedekindDomain

open scoped TensorProduct

-- `Ideal.Quotient.field` is not a global instance; it is enabled here for the residue fields.
attribute [local instance] Ideal.Quotient.field

namespace ChabautyColeman

namespace NumberFieldBase

variable {K : Type*} [Field K] {A : Type*} [CommRing A]
variable (p : ℕ) [Fact p.Prime] (𝔭 : Ideal A) [𝔭.IsMaximal]

local notation "k" => AlgebraicClosure (ZMod p)

/-! ### Point counts over the residue field -/

/-- The affine solution counts of `y² = g(x)` agree along a bijective ring
homomorphism. -/
theorem encard_solutionPairs_map {F F' : Type*} [Semiring F] [Semiring F'] {φ : F →+* F'}
    (hφ : Function.Bijective φ) (g : F[X]) :
    {q : F' × F' | q.2 ^ 2 = (g.map φ).eval q.1}.encard
      = {q : F × F | q.2 ^ 2 = g.eval q.1}.encard := by
  have himg : {q : F' × F' | q.2 ^ 2 = (g.map φ).eval q.1}
      = (Prod.map φ φ) '' {q : F × F | q.2 ^ 2 = g.eval q.1} := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_ofPred_eq, Prod.map_apply, Prod.mk.injEq, Prod.exists]
    refine ⟨fun hab ↦ ?_, ?_⟩
    · obtain ⟨a₀, rfl⟩ := hφ.2 a
      obtain ⟨b₀, rfl⟩ := hφ.2 b
      rw [eval_map_apply] at hab
      exact ⟨a₀, b₀, hφ.1 (by rwa [map_pow]), rfl, rfl⟩
    · rintro ⟨a₀, b₀, hq, rfl, rfl⟩
      rw [eval_map_apply, ← map_pow, hq]
  rw [himg, (Prod.map_injective.mpr ⟨hφ.1, hφ.1⟩).encard_image]

/-- A nontrivial ring that is free as a `ℤ`-module has characteristic zero. -/
theorem charZero_of_free (B : Type*) [CommRing B] [Nontrivial B] [Module.Free ℤ B] :
    CharZero B :=
  have : HasUniqueDiv B := .of_isTorsionFree ℤ _
  CharZero.of_hasUniqueDiv B B

section

variable [Module.Free ℤ A]

section

variable [Module.Finite ℤ A] [IsDomain A]

/-! ### The residue field at `𝔭` -/

/-- The quotient of `A` by a maximal ideal is finite: a domain that is finite free over `ℤ`
has characteristic zero, so a maximal ideal is nonzero and its quotient is finite. -/
theorem finite_quotient : Finite (A ⧸ 𝔭) :=
  have : CharZero A := charZero_of_free A
  Ideal.finiteQuotientOfFreeOfNeBot 𝔭 (Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭)

/-- An embedding of the residue field of `𝔭` into `𝔽_barp` exists. -/
theorem nonempty_ringHom_algebraicClosure (hp𝔭 : (p : A) ∈ 𝔭) :
    Nonempty ((A ⧸ 𝔭) →+* AlgebraicClosure (ZMod p)) := by
  have hchar : CharP (A ⧸ 𝔭) p := charP_quotient p (Ideal.IsMaximal.ne_top ‹_›) hp𝔭
  let : Algebra (ZMod p) (A ⧸ 𝔭) := ZMod.algebra _ p
  have := finite_quotient 𝔭
  have : Module.Finite (ZMod p) (A ⧸ 𝔭) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ZMod p) (A ⧸ 𝔭) := Algebra.IsAlgebraic.of_finite _ _
  exact ⟨(IsAlgClosed.lift (M := k) : (A ⧸ 𝔭) →ₐ[ZMod p] k).toRingHom⟩

/-- The residue characteristic of `𝔭` is a prime number: `A ⧸ 𝔭` is a finite field. -/
theorem ringChar_quotient_prime : (ringChar (A ⧸ 𝔭)).Prime := by
  have := finite_quotient 𝔭
  exact CharP.char_is_prime (A ⧸ 𝔭) _

/-- The ideal of `ℤ` below `𝔭` is generated by the residue characteristic. -/
theorem under_eq_span_ringChar : 𝔭.under ℤ = Ideal.span {(ringChar (A ⧸ 𝔭) : ℤ)} := by
  have hmax : (Ideal.span {(ringChar (A ⧸ 𝔭) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp (ringChar_quotient_prime 𝔭)).irreducible
  refine (hmax.eq_of_le (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)) ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine Ideal.mem_comap.mpr ?_
  rw [map_natCast]
  exact Ideal.natCast_mem_of_charP_quotient (ringChar (A ⧸ 𝔭)) 𝔭

end

variable [IsDedekindDomain A]

/-! ### Existence of the certificates -/

/-- The factorization of `p·A` at `𝔭`: `p·A = 𝔭^e·J` with `J` prime to `𝔭`, and `e` the
ramification index, which is positive because `𝔭` lies above `p`. -/
theorem exists_pow_mul (hp𝔭 : (p : A) ∈ 𝔭) :
    ∃ J : Ideal A, 0 < Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) 𝔭 ∧
      Ideal.span {(p : A)}
        = 𝔭 ^ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) 𝔭 * J ∧ ¬ J ≤ 𝔭 := by
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ A) = Ideal.span {(p : A)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hp0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ A) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    have : CharZero A := charZero_of_free A
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hle : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ A) ≤ 𝔭 := by
    rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
    exact hp𝔭
  have hfin : FiniteMultiplicity 𝔭 ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ A)) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu ↦ (Ideal.IsMaximal.ne_top ‹_›) (Ideal.isUnit_iff.mp hu)) hp0
  obtain ⟨J, hJ, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hp0 inferInstance, hmap] at hJ
  exact ⟨J, Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero hp0 inferInstance hle), hJ,
    fun h ↦ hnd (Ideal.dvd_iff_le.mpr h)⟩

variable [Module.Finite ℤ A]

-- A nontrivial free `ℤ`-module is infinite; this supplies the `Infinite A` that `Ideal.absNorm`
-- assumes (Mathlib does the same, locally, in its `Free` section).
local instance : Infinite A := Module.Free.infinite ℤ A

/-- All certificates of `FactorData` exist at a maximal ideal above `p`. -/
theorem exists_factorData (hp𝔭 : (p : A) ∈ 𝔭) :
    ∃ (σ : (A ⧸ 𝔭) →+* AlgebraicClosure (ZMod p))
      (ε : TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A) (J C : Ideal A) (ϖ : A),
      FactorData p 𝔭 σ ε (Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) 𝔭) J C ϖ := by
  have : CharZero A := charZero_of_free A
  obtain ⟨σ⟩ := nonempty_ringHom_algebraicClosure p 𝔭 hp𝔭
  obtain ⟨J, hepos, hpJ, hJ𝔭⟩ := exists_pow_mul p 𝔭 hp𝔭
  obtain ⟨ϖ, C, hϖC, hC⟩ :=
    Ideal.exists_span_singleton_eq_mul_of_ne_bot 𝔭 (Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭)
  have hcop : 𝔭 ⊔ J = ⊤ := (Ideal.isMaximal_def.mp ‹_›).2 _ (left_lt_sup.mpr hJ𝔭)
  have := finite_quotient 𝔭
  obtain ⟨ε, hidem, hεJ, hker⟩ := exists_isIdempotentElem_ker_rho p 𝔭 σ hp𝔭 hepos hpJ hcop
  exact ⟨σ, ε, J, C, ϖ, hidem, hepos, hpJ, hεJ, hker, hϖC, hC⟩

/-- The residue characteristic divides the absolute norm of `𝔭`. -/
theorem dvd_absNorm (hp𝔭 : (p : A) ∈ 𝔭) : p ∣ 𝔭.absNorm := by
  have := finite_quotient 𝔭
  have hchar : CharP (A ⧸ 𝔭) p := charP_quotient p (Ideal.IsMaximal.ne_top ‹_›) hp𝔭
  cases nonempty_fintype (A ⧸ 𝔭)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (A ⧸ 𝔭) p
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self p n.pos.ne'

/-- The ramification index of `𝔭` over `p` is at most the rank of `A` over `ℤ` (the degree
`[K : ℚ]`): taking absolute norms in `p·A = 𝔭^e·J` gives `p^rank = N(𝔭)^e·N(J)` with
`p ∣ N(𝔭)`. -/
theorem ramificationIdx'_le_finrank (hp𝔭 : (p : A) ∈ 𝔭) :
    Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) 𝔭 ≤ Module.finrank ℤ A := by
  obtain ⟨J, -, hpJ, -⟩ := exists_pow_mul p 𝔭 hp𝔭
  have habs := congrArg Ideal.absNorm hpJ
  rw [Ideal.absNorm_span_natCast, map_mul, map_pow] at habs
  have hdvd : p ^ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) 𝔭
      ∣ p ^ Module.finrank ℤ A := by
    rw [habs]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_absNorm p 𝔭 hp𝔭) _) _
  exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd

end


/-! ### The arithmetic valuation ring `A_[v]` and its maps -/

variable {ε : TensorProduct ℤ (WittVector p (AlgebraicClosure (ZMod p))) A}
variable [Algebra A K] [IsFractionRing A K]

/-- Oddness of the degree transports along the fraction-field map: the Jacobian of `y² = f(x)`
over `K` is available whenever `f : A[X]` has odd degree. -/
instance instFactOddMapAlgebraMap {f : A[X]} [Fact (Odd f.natDegree)] :
    Fact (Odd (f.map (algebraMap A K)).natDegree) :=
  ⟨by rw [natDegree_map_eq_of_injective (IsFractionRing.injective A K)]; exact Fact.out⟩

variable [IsDedekindDomain A] (v : HeightOneSpectrum A)

/-- The ring of `v`-integers `A_v ⊆ K`, the localization of `A` at the prime `v` as a valuation
subring of `K` (Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`). -/
local notation "A_[" v "]" => HeightOneSpectrum.valuationSubringAtPrime K v

variable (K) in
/-- The residue field of `A_[v]` is the residue field `A ⧸ v` of `A` at `v`: the map induced by
`A → A_[v] → A_[v] ⧸ 𝔪` is a ring isomorphism. -/
noncomputable def residueFieldEquiv : (A ⧸ v.asIdeal) ≃+* ResidueField A_[v] :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift v.asIdeal ((residue A_[v]).comp (algebraMap A A_[v])) fun a ha ↦ by
      rw [RingHom.comp_apply, residue_eq_zero_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A_[v] v.asIdeal a).mpr ha)
    ⟨RingHom.injective _, fun x ↦ by
      obtain ⟨y, rfl⟩ := residue_surjective x
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl y
      have hs : residue A_[v] (algebraMap A A_[v] s) ≠ 0 := by
        rw [ne_eq, residue_eq_zero_iff,
          IsLocalization.AtPrime.to_map_mem_maximal_iff A_[v] v.asIdeal]
        exact s.2
      refine ⟨Ideal.Quotient.mk _ a / Ideal.Quotient.mk _ (s : A), ?_⟩
      rw [map_div₀, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, RingHom.comp_apply,
        RingHom.comp_apply, div_eq_iff hs, ← map_mul, IsLocalization.mk'_spec]⟩

theorem residueFieldEquiv_mk (a : A) :
    residueFieldEquiv K v (Ideal.Quotient.mk _ a) = residue A_[v] (algebraMap A A_[v] a) := rfl

variable (K) in
theorem ringChar_residueField : ringChar (ResidueField A_[v]) = ringChar (A ⧸ v.asIdeal) :=
  have := charP_of_injective_ringHom (f := (residueFieldEquiv K v).toRingHom)
    (residueFieldEquiv K v).injective (ringChar (A ⧸ v.asIdeal))
  ringChar.eq _ _

theorem map_algebraMap_map_residue (g : A[X]) : (g.map (algebraMap A A_[v])).map (residue A_[v])
    = (g.map (Ideal.Quotient.mk v.asIdeal)).map
      (residueFieldEquiv K v : (A ⧸ v.asIdeal) →+* ResidueField A_[v]) := by
  rw [map_map, map_map]
  rfl

/-- The affine residue count over `A_[v]` is the count over `A ⧸ v`. -/
theorem encard_residuePairs_nf (g : A[X]) :
    {q : ResidueField A_[v] × ResidueField A_[v]
        | q.2 ^ 2 = ((g.map (algebraMap A A_[v])).map (residue A_[v])).eval q.1}.encard
      = {q : (A ⧸ v.asIdeal) × (A ⧸ v.asIdeal)
          | q.2 ^ 2 = (g.map (Ideal.Quotient.mk v.asIdeal)).eval q.1}.encard := by
  rw [map_algebraMap_map_residue, encard_solutionPairs_map
    (φ := (residueFieldEquiv K v : (A ⧸ v.asIdeal) →+* ResidueField A_[v]))
    (residueFieldEquiv K v).bijective]

theorem algebraMap_mk'_one (s : v.asIdeal.primeCompl) :
    algebraMap A_[v] K (IsLocalization.mk' A_[v] 1 s) = (algebraMap A K s)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [IsScalarTower.algebraMap_apply A A_[v] K, ← map_mul, IsLocalization.mk'_spec, map_one,
      map_one]

theorem residue_mk'_one (s : v.asIdeal.primeCompl) :
    residue A_[v] (IsLocalization.mk' A_[v] 1 s) = (residue A_[v] (algebraMap A A_[v] s))⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]

variable {v}

variable (K) in
/-- The `v`-integral model of a polynomial over `K` cut out by an integral multiple `g = b·f`
of it with `b ∉ v`: the polynomial `b⁻¹·g` over `A_[v]`. -/
noncomputable def integralModel (g : A[X]) {b : A} (hb : b ∉ v.asIdeal) : A_[v][X] :=
  C (IsLocalization.mk' A_[v] 1 (⟨b, hb⟩ : v.asIdeal.primeCompl)) * g.map (algebraMap A A_[v])

theorem integralModel_map_algebraMap {g : A[X]} {b : A} (hb : b ∉ v.asIdeal) {f : K[X]}
    (hg : g.map (algebraMap A K) = C (algebraMap A K b) * f) :
    (integralModel K g hb).map (algebraMap A_[v] K) = f := by
  have hb0 : algebraMap A K b ≠ 0 := fun h0 ↦ hb (by
    rw [IsFractionRing.to_map_eq_zero_iff.mp h0]
    exact zero_mem _)
  rw [integralModel, Polynomial.map_mul, map_C, map_map, ← IsScalarTower.algebraMap_eq, hg,
    algebraMap_mk'_one, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]

theorem integralModel_map_residue (g : A[X]) {b : A} (hb : b ∉ v.asIdeal) :
    (integralModel K g hb).map (residue A_[v])
      = C (residue A_[v] (algebraMap A A_[v] b))⁻¹
        * g.map ((residue A_[v]).comp (algebraMap A A_[v])) := by
  rw [integralModel, Polynomial.map_mul, map_C, map_map, residue_mk'_one]

variable (v) [Module.Free ℤ A] [Module.Finite ℤ A]

-- A nontrivial free `ℤ`-module is infinite; this supplies the `Infinite A` that `Ideal.absNorm`
-- assumes (Mathlib does the same, locally, in its `Free` section).
local instance : Infinite A := Module.Free.infinite ℤ A

variable (K) in
theorem finite_residueField : Finite (ResidueField A_[v]) :=
  have := finite_quotient v.asIdeal
  Finite.of_injective _ (residueFieldEquiv K v).symm.injective

section Factor

variable {v} {σ : (A ⧸ v.asIdeal) →+* AlgebraicClosure (ZMod p)}
variable {e : ℕ} {J C : Ideal A} {ϖ : A}

variable (K) {p} in
/-- The inclusion of `A_[v]` into the local factor: `resO` sends the elements outside `v` to
units (`ChabautyColeman.NumberFieldBase.FactorData.isUnit_resO_of_notMem`), so it factors
through the localization. -/
noncomputable def locFactor (h : FactorData p v.asIdeal σ ε e J C ϖ) :
    A_[v] →+* Factor p ε :=
  IsLocalization.lift (M := v.asIdeal.primeCompl) (g := resO p ε) fun ⟨_, hs⟩ ↦
    h.isUnit_resO_of_notMem hs

variable {p}
variable (h : FactorData p v.asIdeal σ ε e J C ϖ)

theorem locFactor_algebraMap (a : A) :
    locFactor K h (algebraMap A A_[v] a) = resO p ε a :=
  IsLocalization.lift_eq ..

variable (K) in
/-- The inclusion into the factor is a local homomorphism. -/
theorem isLocalHom_locFactor : IsLocalHom (locFactor K h) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl a
  refine (IsLocalization.AtPrime.isUnit_mk'_iff _ _ r s).mpr fun hr𝔭 ↦ ?_
  have hspec : locFactor K h (IsLocalization.mk' _ r s) * resO p ε s = resO p ε r := by
    have h1 := congrArg (locFactor K h) (IsLocalization.mk'_spec A_[v] r s)
    rwa [map_mul, locFactor_algebraMap, locFactor_algebraMap] at h1
  have hrunit : IsUnit (resO p ε r) :=
    hspec ▸ ha.mul (h.isUnit_resO_of_notMem s.2)
  have hmax : (v.asIdeal.map (resO p ε)).IsMaximal := h.isMaximal_map
  exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hr𝔭) hrunit)

/-- The two inclusions agree in the fraction field of the factor, for any `K`-algebra
structure compatible with `resO` on `A`. -/
theorem comp_algebraMap_eq_comp_locFactor [Algebra K (FractionRing (Factor p ε))]
    (halg : ∀ a : A, algebraMap K (FractionRing (Factor p ε)) (algebraMap A K a)
      = algebraMap (Factor p ε) (FractionRing (Factor p ε)) (resO p ε a)) :
    (algebraMap K (FractionRing (Factor p ε))).comp (algebraMap A_[v] K)
      = (algebraMap (Factor p ε) (FractionRing (Factor p ε))).comp (locFactor K h) := by
  refine IsLocalization.ringHom_ext v.asIdeal.primeCompl ?_
  ext a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, locFactor_algebraMap]
  exact halg a

include h in
/-- `A` embeds into the local factor (blueprint `lem:factor-arithmetic`): the kernel of
`resO` is a prime ideal, and a maximal kernel would force a positive characteristic on the
factor, contradicting `CharZero`; in a Dedekind domain there is nothing in between. -/
theorem resO_injective : Function.Injective (resO p ε) := by
  have hdom : IsDomain (Factor p ε) := h.isDomain
  have hCZ : CharZero (Factor p ε) := h.charZero
  rcases eq_or_ne (RingHom.ker (resO p ε)) ⊥ with hbot | hne
  · exact (RingHom.injective_iff_ker_eq_bot _).mpr hbot
  · exfalso
    have hkerP : (RingHom.ker (resO p ε)).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker (resO p ε)).IsMaximal := hkerP.isMaximal hne
    have := finite_quotient (RingHom.ker (resO p ε))
    obtain ⟨ℓ, hℓ⟩ := CharP.exists (A ⧸ RingHom.ker (resO p ε))
    have hℓ0 : ℓ ≠ 0 :=
      CharP.char_ne_zero_of_finite (A ⧸ RingHom.ker (resO p ε)) ℓ
    have hmem : ((ℓ : ℕ) : A) ∈ RingHom.ker (resO p ε) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero _ ℓ
    rw [RingHom.mem_ker, map_natCast] at hmem
    exact hℓ0 (Nat.cast_eq_zero.mp hmem)

include h in
/-- **Integrality descends to `A_[v]`** (blueprint `lem:factor-arithmetic`): an element of `K`
that is integral in the local factor lies in `A_[v]`. Otherwise its inverse is a non-unit of
the valuation ring `A_[v]`, whose image in the factor is a non-unit (the inclusion is a local
homomorphism) — but the integral lift of the element inverts it. -/
theorem exists_algebraMap_eq [IsDomain (Factor p ε)] [IsDiscreteValuationRing (Factor p ε)]
    [Algebra K (FractionRing (Factor p ε))]
    (halg : ∀ a : A, algebraMap K (FractionRing (Factor p ε)) (algebraMap A K a)
      = algebraMap (Factor p ε) (FractionRing (Factor p ε)) (resO p ε a))
    (x : K)
    (hx : (IsDiscreteValuationRing.maximalIdeal (Factor p ε)).valuation
        (FractionRing (Factor p ε)) (algebraMap K (FractionRing (Factor p ε)) x) ≤ 1) :
    ∃ a : A_[v], algebraMap A_[v] K a = x := by
  rcases ValuationSubring.mem_or_inv_mem A_[v] x with hxm | hxm
  · exact ⟨⟨x, hxm⟩, rfl⟩
  by_contra! hne
  have hx0 : x ≠ 0 := fun h0 ↦ hne 0 (by rw [h0, map_zero])
  -- `x⁻¹` is a non-unit of `A_[v]`
  have hnu : ¬ IsUnit (⟨x⁻¹, hxm⟩ : A_[v]) := fun hu ↦ by
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have := congrArg (algebraMap A_[v] K) hy
    rw [map_mul, map_one] at this
    exact hne y ((inv_mul_eq_one₀ hx0).mp this).symm
  -- its image in the factor is a non-unit, but the integral lift of `x` inverts it
  have := isLocalHom_locFactor K h
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
  refine hnu ((isUnit_map_iff (locFactor K h) _).mp (.of_mul_eq_one_right z ?_))
  refine IsFractionRing.injective (Factor p ε) (FractionRing (Factor p ε)) ?_
  rw [map_mul, hz, map_one, ← RingHom.comp_apply, ← comp_algebraMap_eq_comp_locFactor h halg,
    RingHom.comp_apply, ← map_mul]
  change algebraMap K _ (x * x⁻¹) = 1
  rw [mul_inv_cancel₀ hx0, map_one]

/-- Squarefreeness of the reduction transports from the residue field of `A_[v]` to the
residue field of the local factor: the finite field `A ⧸ v` is perfect, so squarefree means
separable, and separability survives the extension of scalars. -/
theorem squarefree_map_locFactor [IsLocalRing (Factor p ε)] {fA : A_[v][X]}
    (hsq : Squarefree (fA.map (residue A_[v]))) :
    Squarefree ((fA.map (locFactor K h)).map (residue (Factor p ε))) := by
  have := finite_residueField K v
  have := isLocalHom_locFactor K h
  have hfac : (fA.map (locFactor K h)).map (residue (Factor p ε))
      = (fA.map (residue A_[v])).map (ResidueField.map (locFactor K h)) := by
    rw [map_map, map_map]
    exact congrArg fA.map (RingHom.ext fun a ↦ (ResidueField.map_residue _ a).symm)
  rw [hfac]
  exact (PerfectField.separable_iff_squarefree.mpr hsq).map.squarefree

/-! ### The main theorems over a number field -/

-- the workhorse behind `main_affine_numberField`, with the residue characteristic `p`
-- explicit; the public statement reads it off `v` as the characteristic of its residue field
private theorem main_affine_aux [CharZero K] (hp𝔭 : (p : A) ∈ v.asIdeal)
    (C : HyperellipticCurve K) [C.IsOdd] {fA : A_[v][X]} (hfA : fA.map (algebraMap A_[v] K) = C.f)
    (hsq : Squarefree (fA.map (residue A_[v]))) {r : ℕ}
    (hpr : 2 * r + Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal + 1 < p)
    (hrk : HypJac.rank K C.f ≤ r) (hrg : r < C.genus) :
    {q : K × K | q.2 ^ 2 = C.f.eval q.1}.encard + 1
      ≤ ({q : ResidueField A_[v] × ResidueField A_[v]
            | q.2 ^ 2 = (fA.map (residue A_[v])).eval q.1}.encard + 1)
        + 2 * r := by
  classical
  have : CharZero A := charZero_of_free A
  have hf : C.f.Monic := C.monic_f
  -- the certificates
  obtain ⟨σ, ε, J, I, ϖ, h⟩ := exists_factorData p v.asIdeal hp𝔭
  have := finite_residueField K v
  -- ring structure of the factor
  have h1ε := rho_one_sub_eq_zero h.ker
  have hdom : IsDomain (Factor p ε) := h.isDomain
  have hdvr : IsDiscreteValuationRing (Factor p ε) := h.isDiscreteValuationRing
  have hCZ : CharZero (Factor p ε) := h.charZero
  have hmaxid : maximalIdeal (Factor p ε) = v.asIdeal.map (resO p ε) := h.maximalIdeal_eq
  have hmax_ker : maximalIdeal (Factor p ε) = RingHom.ker (rhoO p v.asIdeal σ h1ε) := by
    rw [hmaxid, ker_rhoO p v.asIdeal σ h.ker]
  -- the adic topology
  have : Fact (IsAdic (maximalIdeal (Factor p ε))) := ⟨hmaxid ▸ h.isAdic_map⟩
  have : T2Space (Factor p ε) := h.t2Space
  have : CompleteSpace (Factor p ε) := h.completeSpace
  -- the residue field
  have : IsAlgClosed (ResidueField (Factor p ε)) :=
    isAlgClosed_residueField p v.asIdeal σ h1ε hmax_ker
  have hp2 : p ≠ 2 := by have := h.epos; lia
  have : NeZero (2 : ResidueField (Factor p ε)) :=
    neZero_two_residueField p v.asIdeal σ h1ε hmax_ker hp2
  -- the polynomial over `A_[v]` and the curve over the factor
  have hfAm : fA.Monic := monic_of_injective (IsFractionRing.injective A_[v] K) (hfA ▸ hf)
  have hfO : (fA.map (locFactor K h)).Monic := hfAm.map _
  have hnd : (fA.map (locFactor K h)).natDegree = C.f.natDegree := by
    rw [hfAm.natDegree_map, ← hfA, hfAm.natDegree_map]
  have hd0' : 0 < (fA.map (locFactor K h)).natDegree := by
    rw [hnd]; exact C.natDegree_pos
  have hsqO : Squarefree ((fA.map (locFactor K h)).map (residue (Factor p ε))) :=
    squarefree_map_locFactor h hsq
  let : Invertible (2 : Factor p ε) :=
    ((residue_ne_zero_iff_isUnit 2).mp (by rw [map_ofNat]; exact NeZero.ne _)).invertible
  have hsepO : (fA.map (locFactor K h)).Separable := by
    simpa using separable_map_of_separable_residue (RingHom.id _) hfO hd0'
      (PerfectField.separable_iff_squarefree.mpr hsqO)
  have hoddO : Odd (fA.map (locFactor K h)).natDegree := hnd ▸ C.odd_natDegree_f
  -- `K` maps into the fraction field of the factor
  have hψinj : Function.Injective
      ((algebraMap (Factor p ε) (FractionRing (Factor p ε))).comp (resO p ε)) :=
    (IsFractionRing.injective _ _).comp (resO_injective h)
  let : Algebra K (FractionRing (Factor p ε)) := (IsFractionRing.lift hψinj).toAlgebra
  have halg (a : A) : algebraMap K (FractionRing (Factor p ε)) (algebraMap A K a)
      = algebraMap (Factor p ε) (FractionRing (Factor p ε)) (resO p ε a) :=
    IsFractionRing.lift_algebraMap hψinj a
  have hcomm := comp_algebraMap_eq_comp_locFactor h halg
  have hfrac_eq : C.baseChange (FractionRing (Factor p ε))
      = (HyperellipticCurve.ofMonicOdd hfO hoddO hsepO).baseChange (FractionRing (Factor p ε)) := by
    refine HyperellipticCurve.ext ?_ ?_
    · have := C.natDegree_f
      change C.genus = (fA.map (locFactor K h)).natDegree / 2
      lia
    · change C.f.map (algebraMap K (FractionRing (Factor p ε)))
        = (fA.map (locFactor K h)).map (algebraMap (Factor p ε) (FractionRing (Factor p ε)))
      rw [← hfA, map_map, map_map, hcomm]
  -- the arithmetic valuation ring
  have : IsLocalHom (locFactor K h) := isLocalHom_locFactor K h
  exact ChabautyColeman.main_affine_arith (C := .ofMonicOdd hfO hoddO hsepO) (C₀ := C)
    h.isUniformizer hpr hfrac_eq hrk hrg (locFactor K h) (algebraMap A_[v] K) hcomm
    (exists_algebraMap_eq h halg) rfl

end Factor

variable {v}

/-- **The Chabauty–Coleman bound over a number field** (blueprint `thm:main-nf`; Stoll,
Compositio Math. 142 (2006), Cor. 6.7): let `C : y² = f(x)` be an odd-degree hyperelliptic
curve over `K` with coefficients integral at the prime `v` of `A` — `f` is the image of `fA`
over the valuation ring `A_[v]` — such that the reduction of `fA` modulo `v` is squarefree. If
the rank of `Cl(K[x][y]/(y² - f))` is at most `r < g` and `p > 2r + e + 1` for the
residue characteristic `p` and the ramification index `e = e(v ∣ p)`, then the number of
affine `K`-points of `y² = f(x)`, plus one for the point at infinity, is at most the
corresponding count over the residue field of `v` plus `2r`.

The ring `A` is any Dedekind domain that is finite free over `ℤ` with fraction field `K` —
the ring of integers of a number field, or `ℤ` itself at `K = ℚ`. The prime data is read
off `v`: the residue characteristic is the characteristic of the residue field
`A_[v] ⧸ 𝔪 ≅ A ⧸ v` and the ramification index is
`Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal`; the rank is
`ChabautyColeman.HypJac.rank` of the curve over `K`. -/
theorem main_affine_numberField [CharZero K] (C : HyperellipticCurve K) [C.IsOdd]
    {fA : A_[v][X]} (hfA : fA.map (algebraMap A_[v] K) = C.f)
    (hsq : Squarefree (fA.map (residue A_[v]))) {r : ℕ}
    (hpr : 2 * r + Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal + 1
      < ringChar (ResidueField A_[v]))
    (hrk : HypJac.rank K C.f ≤ r) (hrg : r < C.genus) :
    {q : K × K | q.2 ^ 2 = C.f.eval q.1}.encard + 1
      ≤ ({q : ResidueField A_[v] × ResidueField A_[v]
            | q.2 ^ 2 = (fA.map (residue A_[v])).eval q.1}.encard + 1)
        + 2 * r := by
  rw [ringChar_residueField, under_eq_span_ringChar v.asIdeal] at hpr
  have : Fact (ringChar (A ⧸ v.asIdeal)).Prime := ⟨ringChar_quotient_prime v.asIdeal⟩
  exact main_affine_aux (Ideal.natCast_mem_of_charP_quotient (ringChar (A ⧸ v.asIdeal)) _) C
    hfA hsq hpr hrk hrg

/-- **Good reduction at one prime makes the polynomial separable**: a monic `f : K[X]` with an
integral model `fA` at `v` whose reduction is squarefree is separable, hence defines a curve
over `K` (`HyperellipticCurve.ofMonicOdd`). -/
theorem separable_of_squarefree_map_residue {f : K[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    {fA : A_[v][X]} (hfA : fA.map (algebraMap A_[v] K) = f)
    (hsq : Squarefree (fA.map (residue A_[v]))) : f.Separable := by
  have := finite_residueField K v
  have hfAm : fA.Monic := monic_of_injective (IsFractionRing.injective A_[v] K) (hfA ▸ hf)
  have hdA : 0 < fA.natDegree := by rwa [← hfAm.natDegree_map (algebraMap A_[v] K), hfA]
  exact hfA ▸ separable_map_of_separable_residue (algebraMap A_[v] K) hfAm hdA
    (PerfectField.separable_iff_squarefree.mpr hsq)

/-- **The Chabauty–Coleman bound for an integral polynomial**: the case of
`ChabautyColeman.NumberFieldBase.main_affine_numberField` where `f` has coefficients in `A`,
with the reduction taken in `A ⧸ 𝔭` and the prime given as a maximal ideal `𝔭` of `A`. -/
theorem main_affine_numberField_int {𝔭 : Ideal A} [𝔭.IsMaximal] {f : A[X]} (hf : f.Monic)
    [Fact (Odd f.natDegree)] (hsq : Squarefree (f.map (Ideal.Quotient.mk 𝔭))) {r : ℕ}
    (hpr : 2 * r + Ideal.ramificationIdx' (𝔭.under ℤ) 𝔭 + 1 < ringChar (A ⧸ 𝔭))
    (hrk : HypJac.rank K (f.map (algebraMap A K)) ≤ r) (hrg : r < genus f) :
    {q : K × K | q.2 ^ 2 = (f.map (algebraMap A K)).eval q.1}.encard + 1
      ≤ ({q : (A ⧸ 𝔭) × (A ⧸ 𝔭)
            | q.2 ^ 2 = (f.map (Ideal.Quotient.mk 𝔭)).eval q.1}.encard + 1)
        + 2 * r := by
  have : CharZero A := charZero_of_free A
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let v : HeightOneSpectrum A := ⟨𝔭, inferInstance, Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭⟩
  have hsq' : Squarefree ((f.map (algebraMap A A_[v])).map (residue A_[v])) := by
    rw [map_algebraMap_map_residue]
    exact hsq.map (Polynomial.mapEquiv (residueFieldEquiv K v))
  have hfAK : (f.map (algebraMap A A_[v])).map (algebraMap A_[v] K) = f.map (algebraMap A K) := by
    rw [map_map, ← IsScalarTower.algebraMap_eq]
  have hodd : Odd (f.map (algebraMap A K)).natDegree := by
    rw [hf.natDegree_map]; exact Fact.out
  let C : HyperellipticCurve K := .ofMonicOdd (hf.map _) hodd
    (separable_of_squarefree_map_residue (hf.map _) hodd.pos hfAK hsq')
  have hrg' : r < C.genus := by
    change r < (f.map (algebraMap A K)).natDegree / 2
    rwa [hf.natDegree_map]
  have h := main_affine_numberField C hfAK hsq' (by rwa [ringChar_residueField]) hrk hrg'
  rwa [encard_residuePairs_nf] at h

variable (A) in
/-- **Good primes exist**: a monic squarefree polynomial over `K` has coefficients integral at,
and squarefree reduction modulo, some prime `v` of `A` above an arbitrarily large rational
prime — any prime beyond the bound `B` and beyond the absolute norm of `a·s·b` works, where
`b·f` has coefficients in `A` and the resultant of `f` with `f'` is `a / s`: a maximal ideal
above such a prime contains none of `a`, `s`, `b`, so `f` has the integral model `b⁻¹·(b·f)`
there, whose resultant with its derivative is the unit `a / s` of `A_[v]`, and Bézout
certifies separability of the reduction. -/
theorem exists_prime_squarefree_reduction {f : K[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hsq : Squarefree f) (B : ℕ) :
    ∃ (p : ℕ) (v : HeightOneSpectrum A) (fA : A_[v][X]), p.Prime ∧ B < p ∧
      (p : A) ∈ v.asIdeal ∧ fA.map (algebraMap A_[v] K) = f ∧
      Squarefree (fA.map (residue A_[v])) := by
  set d := f.natDegree
  have : CharZero A := charZero_of_free A
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  -- an integral multiple `g = b·f` of `f`
  obtain ⟨b, hb, hbf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) f
  set g := IsLocalization.integerNormalization (nonZeroDivisors A) f
  have hgf : g.map (algebraMap A K) = C (algebraMap A K b) * f := by
    rw [hbf, ← algebraMap_smul K b f, smul_eq_C_mul]
  -- the resultant of `f` with `f'` is a nonzero element `a / s` of `K`
  have hres : IsUnit (f.resultant f.derivative d d) :=
    isUnit_resultant_of_isCoprime hf ((natDegree_derivative_le _).trans (Nat.sub_le _ _))
      (PerfectField.separable_iff_squarefree.mpr hsq)
  obtain ⟨a, s, hs, has⟩ := IsFractionRing.div_surjective (A := A) (f.resultant f.derivative d d)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at has
    exact hres.ne_zero has.symm
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  -- a prime beyond `B` and the norm of `a·s·b`, and a maximal ideal above it
  set N := Ideal.absNorm (Ideal.span {a * s * b}) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (mul_ne_zero ha0 hs0) hb0
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max (B + 1) (N + 1))
  have : Fact p.Prime := ⟨hp⟩
  have hrank0 : 0 < Module.finrank ℤ A := Module.finrank_pos
  obtain ⟨𝔭, hmax, -, hdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp
    (Ideal.span {(p : A)}) (by
      rw [Ideal.absNorm_span_natCast]
      exact dvd_pow_self p hrank0.ne')
  have : 𝔭.IsMaximal := hmax
  have hp𝔭 : (p : A) ∈ 𝔭 := Ideal.le_of_dvd hdvd (Ideal.mem_span_singleton_self _)
  -- `a`, `s` and `b` lie outside `𝔭`, since their product does
  have hasb : a * s * b ∉ 𝔭 := fun hmem ↦ by
    have h1 : Ideal.absNorm 𝔭 ∣ N :=
      Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    lia [Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) ((dvd_absNorm p 𝔭 hp𝔭).trans h1)]
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum A, v.asIdeal = 𝔭 :=
    ⟨⟨𝔭, hmax.isPrime, Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭⟩, rfl⟩
  have ha : a ∉ v.asIdeal := fun h ↦ hasb (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
  have hs' : s ∉ v.asIdeal := fun h ↦ hasb (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
  have hb' : b ∉ v.asIdeal := fun h ↦ hasb (Ideal.mul_mem_left _ _ h)
  set fA := integralModel K g hb'
  have hfA : fA.map (algebraMap A_[v] K) = f := integralModel_map_algebraMap hb' hgf
  refine ⟨p, v, fA, hp, by lia, hp𝔭, hfA, ?_⟩
  -- the reduction is squarefree: the resultant of the model with its derivative is a unit
  have hmon : fA.Monic := monic_of_injective (IsFractionRing.injective A_[v] K) (hfA ▸ hf)
  have hdeg : fA.natDegree = d := (hmon.natDegree_map _).symm.trans (congrArg natDegree hfA)
  have hunit : IsUnit (fA.resultant fA.derivative d d) := by
    have heq : fA.resultant fA.derivative d d
        = algebraMap A A_[v] a * IsLocalization.mk' A_[v] 1 (⟨s, hs'⟩ : v.asIdeal.primeCompl) := by
      refine IsFractionRing.injective A_[v] K ?_
      rw [← resultant_map_map, ← derivative_map, hfA, ← has, map_mul,
        ← IsScalarTower.algebraMap_apply, algebraMap_mk'_one, div_eq_mul_inv]
    rw [heq]
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff A_[v] v.asIdeal a).mpr ha).mul
      (.of_mul_eq_one _ (by rw [IsLocalization.mk'_spec, map_one]))
  refine (separable_of_isUnit_resultant (natDegree_map_le.trans hdeg.le) hd.ne' ?_).squarefree
  rw [derivative_map, resultant_map_map]
  exact hunit.map _

include A in
variable (A) in
/-- **Finiteness of the rational points over a number field** (blueprint
`cor:finiteness-nf`): for an odd-degree hyperelliptic curve `C : y² = f(x)` over `K` with the
rank of `Cl(K[x][y]/(y² - f))` below the genus, the affine `K`-solution set of `y² = f(x)` is
finite. No prime appears in the statement: writing `r` for that rank, the proof chooses a
rational prime `p > 2r + Module.finrank ℤ A + 1` and a prime `v` of `A` above it at which `f`
is integral with squarefree reduction (`exists_prime_squarefree_reduction`), where the count
bound behind `main_affine_numberField` applies because the ramification index at `v` is at
most `Module.finrank ℤ A = [K : ℚ]`.

The ring `A` is any Dedekind domain that is finite free over `ℤ` with fraction field `K` —
the ring of integers of a number field, or `ℤ` itself at `K = ℚ`; it does not occur in the
statement and is therefore an explicit argument. -/
theorem ratPoints_finite_numberField [CharZero K] (C : HyperellipticCurve K) [C.IsOdd]
    (hrk : HypJac.rank K C.f < C.genus) : {q : K × K | q.2 ^ 2 = C.f.eval q.1}.Finite := by
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp (hrk.trans Cardinal.natCast_lt_aleph0)
  rw [hr, Nat.cast_lt] at hrk
  obtain ⟨p, v, fA, hp, hBp, hp𝔭, hfA, hsqred⟩ := exists_prime_squarefree_reduction A C.monic_f
    C.natDegree_pos C.squarefree_f (2 * r + Module.finrank ℤ A + 1)
  have : Fact p.Prime := ⟨hp⟩
  have hpr : 2 * r + Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal + 1 < p := by
    lia [ramificationIdx'_le_finrank p v.asIdeal hp𝔭]
  have h := main_affine_aux hp𝔭 C hfA hsqred hpr hr.le hrk
  have := finite_residueField K v
  have hfin : {q : ResidueField A_[v] × ResidueField A_[v]
      | q.2 ^ 2 = (fA.map (residue A_[v])).eval q.1}.Finite := Set.toFinite _
  refine Set.Finite.of_encard_le_add hfin (c := 1 + 2 * r) ?_
  refine le_self_add.trans (h.trans_eq ?_)
  push_cast
  ring

/-- **Finiteness for an integral polynomial**: the case of
`ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField` where `f` has coefficients
in `A`. -/
theorem ratPoints_finite_numberField_int {f : A[X]} (hf : f.Monic) [Fact (Odd f.natDegree)]
    (hsq : Squarefree f) (hrk : HypJac.rank K (f.map (algebraMap A K)) < genus f) :
    {q : K × K | q.2 ^ 2 = (f.map (algebraMap A K)).eval q.1}.Finite := by
  have : CharZero A := charZero_of_free A
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have hodd : Odd (f.map (algebraMap A K)).natDegree := by
    rw [hf.natDegree_map]; exact Fact.out
  refine ratPoints_finite_numberField A (.ofMonicOdd (hf.map _) hodd
    (PerfectField.separable_iff_squarefree.mpr (hf.squarefree_map_fraction_map hsq))) ?_
  change HypJac.rank K (f.map (algebraMap A K)) < ((f.map (algebraMap A K)).natDegree / 2 : ℕ)
  rwa [hf.natDegree_map]

end NumberFieldBase

end ChabautyColeman

end
