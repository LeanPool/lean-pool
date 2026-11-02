/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Jacobson
public import LeanPool.CompositionAlgebrasOverRings.LGRing.ValueIdeal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Von Neumann regular and zero-dimensional rings are LG

`GN 2.2` (from `EG`): von Neumann regular rings are LG-rings, and more generally so are
zero-dimensional rings.

## Main definitions

* `IsVonNeumannRegular R` : every `a : R` satisfies `a * x * a = a` for some `x`. mathlib has no
  such predicate, so we introduce one; see the implementation notes.
* `MvPolynomial.RepresentsUnitOn p e` : local scaffolding — `p` takes a value that is invertible
  "on the idempotent `e`", i.e. invertible in the ring `eR`, without leaving `R`.

## Main results

* `isLGRing_of_forall_exists_idempotent` : the shared criterion. If every `a : R` admits an
  idempotent `f` such that `a` is invertible on `f` and some power of `a` lies in `(f)`, then `R`
  is an LG-ring.
* `IsVonNeumannRegular.isLGRing` : **`GN 2.2`**, von Neumann regular implies LG.
* `isLGRing_of_isVonNeumannRegular_quotient_jacobson` : the same with `R ⧸ Jac(R)` von Neumann
  regular, which is how `GN` states it.
* `Ring.exists_pow_eq_pow_succ_mul` : in a zero-dimensional ring every `a` satisfies
  `aᵐ = aᵐ⁺¹ x` for some `m` and `x`.
* `isLGRing_of_krullDimLE_zero` : **`GN 2.2`**, `Ring.KrullDimLE 0` implies LG.

## Proof idea

By the value-ideal criterion (`LGRing/ValueIdeal.lean`), being LG amounts to: from
`1 = Σⱼ cⱼ · p(tⱼ)` produce a *single* point where `p` is a unit. The `tⱼ` each work somewhere but
nowhere in particular; the idempotents are what let their witnesses be spliced together.

Write `aⱼ := p(tⱼ)` and let `fⱼ` be the idempotent supplied by the hypothesis, so that `aⱼ` is
invertible on `fⱼ`. Since a power of `aⱼ` lies in `(fⱼ)`, a maximal ideal containing every `fⱼ`
would contain every `aⱼ` and hence `1`; so the `fⱼ` generate the unit ideal and `∏ⱼ (1 - fⱼ) = 0`.
Orthogonalising, `1 = Σⱼ eⱼ` with `eⱼ ≤ fⱼ`, and the point `s := Σⱼ eⱼ tⱼ` restricts to `tⱼ` on the
`j`-th block: `eⱼ · s = eⱼ · tⱼ`, hence `eⱼ · p(s) = eⱼ · p(tⱼ)` — the key step
`MvPolynomial.mul_aeval_eq_of_mul_eq`, proved by induction on `p`, using only that multiplication
by an idempotent is "the projection onto `eR`". So `p(s)` is invertible on every block, and the
blocks exhaust `R`.

The two examples differ only in producing the idempotent. Von Neumann regularity gives it at once
(`f = ax`, with `a` invertible on `f` and `a ∈ (f)`). For a zero-dimensional ring one first shows
`aᵐ = aᵐ⁺¹ x`, which produces `f = aᵐ xᵐ` with `aᵐ ∈ (f)` — the power is genuinely needed here,
which is why the criterion is stated with `a ^ m ∈ (f)` rather than `a ∈ (f)`.

## Implementation notes

`IsVonNeumannRegular` is a new definition, which overview §0 asks us to justify: mathlib (as
pinned in `lake-manifest.json`) has no von Neumann regular *ring* predicate — its only
`VonNeumann` namespace is `Analysis.VonNeumannAlgebra`, an unrelated notion. The definition is
stated for `CommRing` because that is all this file needs and all the LG theory ever uses; the
usual definition makes sense for any ring.

`MvPolynomial.RepresentsUnitOn` is deliberately phrased inside `R`, as `∃ s c, e * p(s) * c = e`,
rather than as `MvPolynomial.RepresentsUnit` over the ring `eR` or `R ⧸ (1 - e)`. Every proof here
is an identity between elements of `R`, and routing through a quotient or a subtype would force
transporting polynomials back and forth for no gain.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Example 2.2.
* [EG] Estes, Guralnick, *Module equivalences: local to global when primitive polynomials represent
  units*, Journal of Algebra **77** (1982), 138–157.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ### Evaluation only sees a point through an idempotent -/

namespace MvPolynomial

/-- **Multiplication by an idempotent is a ring map onto `eR`,** so it cannot tell two points
apart that agree after multiplication by `e`. This is the splicing lemma: it is what allows a
witness assembled block by block to be evaluated block by block.

The proof is a direct induction on `p`; the multiplicative step is
`e·(AB) = (e·e)·(AB) = (e·A)(e·B)`. -/
theorem mul_aeval_eq_of_mul_eq {e : R} (he : IsIdempotentElem e) {s t : Fin n → R}
    (h : ∀ i, e * s i = e * t i) (p : MvPolynomial (Fin n) R) :
    e * aeval s p = e * aeval t p := by
  have hsplit : ∀ (u : Fin n → R) (q : MvPolynomial (Fin n) R) (i : Fin n),
      e * aeval u (q * X i) = (e * aeval u q) * (e * u i) := by
    intro u q i
    rw [map_mul, aeval_X]
    calc e * (aeval u q * u i) = e * e * (aeval u q * u i) := by rw [he]
      _ = e * aeval u q * (e * u i) := by ring
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add q r hq hr => rw [map_add, map_add, mul_add, mul_add, hq, hr]
  | mul_X q i hq => rw [hsplit s q i, hsplit t q i, hq, h i]

/-- `p` **represents a unit on the idempotent `e`**: some value `p(s)` is invertible in the ring
`eR`, expressed without leaving `R`. For `e = 1` this is `MvPolynomial.RepresentsUnit`
(`MvPolynomial.RepresentsUnitOn.representsUnit`), and for `e = 0` it is vacuous. -/
def RepresentsUnitOn (p : MvPolynomial (Fin n) R) (e : R) : Prop :=
  ∃ (s : Fin n → R) (c : R), e * aeval s p * c = e

theorem representsUnitOn_zero (p : MvPolynomial (Fin n) R) : p.RepresentsUnitOn 0 :=
  ⟨0, 0, by simp⟩

/-- Representing a unit on `e` is inherited by any `e'` below `e` (`e' * e = e'`): the same witness
works, since `e'` factors through `e`. -/
theorem RepresentsUnitOn.mono {p : MvPolynomial (Fin n) R} {e e' : R} (h : p.RepresentsUnitOn e)
    (hle : e' * e = e') : p.RepresentsUnitOn e' := by
  obtain ⟨s, c, hsc⟩ := h
  refine ⟨s, c, ?_⟩
  calc e' * aeval s p * c = e' * e * aeval s p * c := by rw [hle]
    _ = e' * (e * aeval s p * c) := by ring
    _ = e' * e := by rw [hsc]
    _ = e' := hle

/-- **Gluing over orthogonal idempotents.** Witnesses on `e₁` and on `e₂` splice into a witness on
`e₁ + e₂`: take `s := e₁ s₁ + e₂ s₂`, which agrees with `sₖ` after multiplication by `eₖ`, so that
`eₖ · p(s) = eₖ · p(sₖ)` by `MvPolynomial.mul_aeval_eq_of_mul_eq`; the inverses glue as
`e₁ c₁ + e₂ c₂`, all cross terms being killed by orthogonality. -/
theorem RepresentsUnitOn.add {p : MvPolynomial (Fin n) R} {e₁ e₂ : R}
    (h₁ : IsIdempotentElem e₁)
    (h₂ : IsIdempotentElem e₂) (horth : e₁ * e₂ = 0) (hr₁ : p.RepresentsUnitOn e₁)
    (hr₂ : p.RepresentsUnitOn e₂) : p.RepresentsUnitOn (e₁ + e₂) := by
  obtain ⟨s₁, c₁, hs₁⟩ := hr₁
  obtain ⟨s₂, c₂, hs₂⟩ := hr₂
  have horth' : e₂ * e₁ = 0 := by rw [mul_comm]; exact horth
  refine ⟨fun x ↦ e₁ * s₁ x + e₂ * s₂ x, e₁ * c₁ + e₂ * c₂, ?_⟩
  have k₁ : e₁ * aeval (fun x ↦ e₁ * s₁ x + e₂ * s₂ x) p = e₁ * aeval s₁ p :=
    mul_aeval_eq_of_mul_eq h₁ (fun i ↦ by
      calc
        e₁ * (e₁ * s₁ i + e₂ * s₂ i) =
            e₁ * e₁ * s₁ i + e₁ * e₂ * s₂ i := by ring
        _ = e₁ * s₁ i := by rw [h₁, horth]; ring) p
  have k₂ : e₂ * aeval (fun x ↦ e₁ * s₁ x + e₂ * s₂ x) p = e₂ * aeval s₂ p :=
    mul_aeval_eq_of_mul_eq h₂ (fun i ↦ by
      calc
        e₂ * (e₁ * s₁ i + e₂ * s₂ i) =
            e₂ * e₁ * s₁ i + e₂ * e₂ * s₂ i := by ring
        _ = e₂ * s₂ i := by rw [h₂, horth']; ring) p
  set v := aeval (fun x ↦ e₁ * s₁ x + e₂ * s₂ x) p with hv
  calc (e₁ + e₂) * v * (e₁ * c₁ + e₂ * c₂)
      = e₁ * e₁ * (v * c₁) + e₁ * e₂ * (v * c₂) +
          (e₂ * e₁ * (v * c₁) + e₂ * e₂ * (v * c₂)) := by
        ring
    _ = e₁ * v * c₁ + e₂ * v * c₂ := by rw [h₁, h₂, horth, horth']; ring
    _ = e₁ * aeval s₁ p * c₁ + e₂ * aeval s₂ p * c₂ := by rw [k₁, k₂]
    _ = e₁ + e₂ := by rw [hs₁, hs₂]

theorem RepresentsUnitOn.representsUnit {p : MvPolynomial (Fin n) R} (h : p.RepresentsUnitOn 1) :
    p.RepresentsUnit R := by
  obtain ⟨s, c, hsc⟩ := h
  exact ⟨s, IsUnit.of_mul_eq_one c (by simpa using hsc)⟩

/-- Orthogonalisation, in the form the induction needs: for a family of idempotents `f` each of
which supports a witness for `p`, the idempotent `1 - ∏_{i ∈ T} (1 - fᵢ)` — the "union" of the
blocks indexed by `T` — again supports one.

The step from `T` to `insert j T` writes `1 - ∏_{insert j T}(1 - fᵢ) = e + fⱼ(1 - e)` with
`e := 1 - ∏_T (1 - fᵢ)`, a sum of *orthogonal* idempotents to which
`MvPolynomial.RepresentsUnitOn.add` applies; the second summand lies below `fⱼ`, so it inherits a
witness by `MvPolynomial.RepresentsUnitOn.mono`. -/
theorem representsUnitOn_one_sub_prod {ι : Type*} {p : MvPolynomial (Fin n) R}
    (f : ι → R) (hf : ∀ i, IsIdempotentElem (f i)) (hrep : ∀ i, p.RepresentsUnitOn (f i))
    (T : Finset ι) :
    IsIdempotentElem (1 - ∏ i ∈ T, (1 - f i)) ∧
      p.RepresentsUnitOn (1 - ∏ i ∈ T, (1 - f i)) := by
  classical
  induction T using Finset.induction with
  | empty => simpa using ⟨IsIdempotentElem.zero, representsUnitOn_zero p⟩
  | insert j T hj ih =>
    obtain ⟨hidem, hrepT⟩ := ih
    set e : R := 1 - ∏ i ∈ T, (1 - f i) with he
    have hnew : 1 - ∏ i ∈ insert j T, (1 - f i) = e + f j * (1 - e) := by
      rw [Finset.prod_insert hj, he]; ring
    have h2 : IsIdempotentElem (f j * (1 - e)) := by
      change f j * (1 - e) * (f j * (1 - e)) = f j * (1 - e)
      calc f j * (1 - e) * (f j * (1 - e))
          = f j * f j * (1 - e - (e - e * e)) := by ring
        _ = f j * (1 - e) := by rw [hf j, hidem]; ring
    have horth : e * (f j * (1 - e)) = 0 := by
      calc e * (f j * (1 - e)) = f j * (e - e * e) := by ring
        _ = 0 := by rw [hidem]; ring
    have hsum : IsIdempotentElem (e + f j * (1 - e)) := by
      change (e + f j * (1 - e)) * (e + f j * (1 - e)) = e + f j * (1 - e)
      calc (e + f j * (1 - e)) * (e + f j * (1 - e))
          = e * e + (e * (f j * (1 - e)) + e * (f j * (1 - e)))
            + f j * (1 - e) * (f j * (1 - e)) := by ring
        _ = e + f j * (1 - e) := by rw [hidem, horth, h2]; ring
    refine ⟨hnew ▸ hsum, hnew ▸ hrepT.add hidem h2 horth ((hrep j).mono ?_)⟩
    calc f j * (1 - e) * f j = f j * f j * (1 - e) := by ring
      _ = f j * (1 - e) := by rw [hf j]

end MvPolynomial

/-! ### The shared criterion -/

/-- **The idempotent criterion for `IsLGRing`.** Suppose every `a : R` admits an idempotent `f`
together with a `c` making `a` invertible on `f` (`a·c·f = f`), and some power `aᵐ` lying in the
ideal `(f)`. Then `R` is an LG-ring.

The two hypotheses on `f` play complementary roles: `a·c·f = f` supplies the witness *on the block
`f`*, and `aᵐ ∈ (f)` forces the blocks to cover `Spec R`, since a maximal ideal containing all the
`fⱼ` would contain all the `aⱼ` and hence `1 = Σⱼ cⱼ aⱼ`. -/
theorem isLGRing_of_forall_exists_idempotent
    (h : ∀ a : R, ∃ f c : R, IsIdempotentElem f ∧ a * c * f = f ∧ ∃ m : ℕ,
      a ^ m ∈ Ideal.span {f}) : IsLGRing R := by
  classical
  rw [isLGRing_iff_forall_valueIdeal_eq_top]
  intro n p htop
  obtain ⟨k, c, t, hsum⟩ := MvPolynomial.exists_sum_mul_aeval_eq_one htop
  choose F C hFidem hFinv m hFpow using fun j : Fin k ↦ h (MvPolynomial.aeval (t j) p)
  -- Each block carries a witness, namely `t j` itself.
  have hrep : ∀ j, p.RepresentsUnitOn (F j) := fun j ↦
    ⟨t j, C j, by
      calc F j * MvPolynomial.aeval (t j) p * C j
          = MvPolynomial.aeval (t j) p * C j * F j := by ring
        _ = F j := hFinv j⟩
  -- The blocks cover: no maximal ideal contains every `F j`.
  have hspan : Ideal.span (Set.range F) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have : 𝔪.IsPrime := h𝔪.isPrime
    refine h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr ?_)
    rw [← hsum]
    refine Submodule.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ ?_
    refine Ideal.IsPrime.mem_of_pow_mem (n := m j) inferInstance ?_
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (hle (Ideal.subset_span ⟨j, rfl⟩))) (hFpow j)
  -- Hence the complementary idempotents multiply to zero, so the blocks exhaust `R`.
  have hprod : ∏ j : Fin k, (1 - F j) = 0 := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Submodule.mem_top)
    calc
      ∏ j : Fin k, (1 - F j) =
          (∏ j : Fin k, (1 - F j)) * ∑ j, d j * F j := by
        rw [hd, mul_one]
      _ = ∑ j, d j * ((∏ i ∈ Finset.univ.erase j, (1 - F i)) * ((1 - F j) * F j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ 1 - F i) (Finset.mem_univ j)]
        ring
      _ = 0 := by
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        have : (1 - F j) * F j = 0 := by rw [sub_mul, one_mul, hFidem j, sub_self]
        rw [this, mul_zero, mul_zero]
  have := (MvPolynomial.representsUnitOn_one_sub_prod F hFidem hrep Finset.univ).2
  rw [hprod, sub_zero] at this
  exact this.representsUnit

/-! ### Von Neumann regular rings -/

/-- A commutative ring is **von Neumann regular** if every element `a` satisfies `a * x * a = a`
for some `x` — equivalently, if every principal ideal is generated by an idempotent.

⚠ mathlib has no von Neumann regular ring predicate at the pinned revision (its only `VonNeumann`
namespace is the unrelated `Analysis.VonNeumannAlgebra`), which is why this is defined here rather
than imported. If one is added upstream, this definition should be replaced by it. -/
def IsVonNeumannRegular (R : Type u) [CommRing R] : Prop :=
  ∀ a : R, ∃ x : R, a * x * a = a

/-- **`GN 2.2`: a von Neumann regular ring is an LG-ring.**

The support idempotent of `a` is `f = a·x`: it is idempotent because `axax = (axa)x = ax`, the
element `a` is invertible on it with `c = x` for the same reason, and `a = a·(ax)` lies in `(f)`
outright — no power is needed. -/
theorem IsVonNeumannRegular.isLGRing (h : IsVonNeumannRegular R) : IsLGRing R := by
  refine isLGRing_of_forall_exists_idempotent fun a ↦ ?_
  obtain ⟨x, hx⟩ := h a
  refine ⟨a * x, x, ?_, ?_, 1, ?_⟩
  · change a * x * (a * x) = a * x
    calc a * x * (a * x) = a * x * a * x := by ring
      _ = a * x := by rw [hx]
  · calc a * x * (a * x) = a * x * a * x := by ring
      _ = a * x := by rw [hx]
  · rw [pow_one, Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    calc a * (a * x) = a * x * a := by ring
      _ = a := hx

/-- **`GN 2.2`, in the form the source states it:** it is enough that `R ⧸ Jac(R)` be von Neumann
regular. Combine `IsVonNeumannRegular.isLGRing` with `GPR 11.21(i)`
(`isLGRing_iff_isLGRing_quotient_jacobson`). -/
theorem isLGRing_of_isVonNeumannRegular_quotient_jacobson
    (h : IsVonNeumannRegular (R ⧸ Ring.jacobson R)) : IsLGRing R :=
  isLGRing_iff_isLGRing_quotient_jacobson.mpr h.isLGRing

/-! ### Zero-dimensional rings -/

/-- In a zero-dimensional ring every element satisfies `aᵐ = aᵐ⁺¹ x` for some `m` and `x`.

The ideal `J = ⋃ₘ Ann(aᵐ)` together with `(a)` generates everything: were both inside a maximal
ideal `𝔪`, then — `𝔪` being *minimal* prime, `R` having dimension zero — the multiplicative set
`{aⁱ s : s ∉ 𝔪}` would miss `0`, and a prime disjoint from it would be a prime strictly inside
`𝔪` (it omits `a ∈ 𝔪`) yet still maximal, which is absurd. So `0 = aⁱ s` for some `s ∉ 𝔪`, putting
`s` in `J ⊆ 𝔪`. Writing `1 = c·a + z` with `z·aᵐ = 0` and multiplying by `aᵐ` gives the claim. -/
theorem Ring.exists_pow_eq_pow_succ_mul [Ring.KrullDimLE 0 R] (a : R) :
    ∃ (m : ℕ) (x : R), a ^ m = a ^ (m + 1) * x := by
  classical
  set A : ℕ → Ideal R := fun i ↦ (Ideal.span {a ^ i}).annihilator with hA
  have hmemA : ∀ (i : ℕ) (r : R), r ∈ A i ↔ r * a ^ i = 0 := fun i r ↦ by
    rw [hA]; simpa using Submodule.mem_annihilator_span_singleton (a ^ i) r
  have hmono : Monotone A := by
    intro i i' hii r hr
    rw [hmemA] at hr ⊢
    rw [← Nat.add_sub_cancel' hii, pow_add, ← mul_assoc, hr, zero_mul]
  have hdir : Directed (· ≤ ·) A := hmono.directed_le
  have hmemJ : ∀ r : R, r ∈ ⨆ i, A i ↔ ∃ i, r * a ^ i = 0 := fun r ↦ by
    rw [Submodule.mem_iSup_of_directed A hdir]
    exact exists_congr fun i ↦ hmemA i r
  have hkey : Ideal.span {a} ⊔ (⨆ i, A i) = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have hprime : 𝔪.IsPrime := h𝔪.isPrime
    have ha𝔪 : a ∈ 𝔪 := hle (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))
    have hone : (1 : R) ∉ 𝔪 := fun hcon ↦ h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr hcon)
    set S : Submonoid R :=
      { carrier := {y | ∃ (i : ℕ) (s : R), s ∉ 𝔪 ∧ y = a ^ i * s}
        one_mem' := ⟨0, 1, hone, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨i, s, hs, rfl⟩ ⟨i', s', hs', rfl⟩
          exact ⟨i + i', s * s', fun hcon ↦ (hprime.mem_or_mem hcon).elim hs hs',
            by rw [pow_add]; ring⟩ } with hS
    have hzero : (0 : R) ∈ S := by
      by_contra h0
      obtain ⟨q, hq, -, hdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) S (by
        rw [Set.disjoint_left]
        intro x hx
        rw [SetLike.mem_coe, Ideal.mem_bot] at hx
        exact hx ▸ h0)
      have haq : a ∉ q := fun hcon ↦
        Set.disjoint_left.mp hdisj hcon ⟨1, 1, hone, by simp⟩
      refine haq ?_
      have : q.IsMaximal := hq.isMaximal'
      have hqle : q ≤ 𝔪 := fun x hx ↦ by
        by_contra hxm
        exact Set.disjoint_left.mp hdisj hx ⟨0, x, hxm, by simp⟩
      rw [Ideal.IsMaximal.eq_of_le ‹q.IsMaximal› h𝔪.ne_top hqle]
      exact ha𝔪
    obtain ⟨i, s, hs, hsi⟩ := hzero
    exact hs (hle (Submodule.mem_sup_right ((hmemJ s).mpr ⟨i, by rw [mul_comm, ← hsi]⟩)))
  have h1 : (1 : R) ∈ Ideal.span {a} ⊔ (⨆ i, A i) := by rw [hkey]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨i, hzi⟩ := (hmemJ z).mp hz
  refine ⟨i, cc, ?_⟩
  have haz : a ^ i * z = 0 := by rw [mul_comm]; exact hzi
  calc a ^ i = a ^ i * (y + z) := by rw [hyz, mul_one]
    _ = a ^ i * y + a ^ i * z := by ring
    _ = a ^ i * (cc * a) := by rw [haz, ← hcc]; ring
    _ = a ^ (i + 1) * cc := by rw [pow_succ]; ring

/-- **`GN 2.2`: a zero-dimensional ring is an LG-ring.**

From `aᵐ = aᵐ⁺¹ x` (`Ring.exists_pow_eq_pow_succ_mul`) one gets, by iterating, `aᵐ = aᵐ⁺ᵏ xᵏ` for
every `k`; taking `k = m` shows `f := aᵐ xᵐ` is idempotent, that `a·x·f = f`, and that
`aᵐ = aᵐ · f ∈ (f)`. This is the case the criterion's `a ^ m ∈ (f)` clause was written for: unlike
the von Neumann regular case, `a` itself need not lie in `(f)`. -/
theorem isLGRing_of_krullDimLE_zero (R : Type u) [CommRing R] [Ring.KrullDimLE 0 R] :
    IsLGRing R := by
  refine isLGRing_of_forall_exists_idempotent fun a ↦ ?_
  obtain ⟨m, x, hmx⟩ := Ring.exists_pow_eq_pow_succ_mul a
  have hstep : ∀ j : ℕ, a ^ (m + j) = a ^ (m + j + 1) * x := fun j ↦
    calc a ^ (m + j) = a ^ j * a ^ m := by rw [pow_add]; ring
      _ = a ^ j * (a ^ (m + 1) * x) := by rw [← hmx]
      _ = a ^ (m + j + 1) * x := by rw [pow_add, pow_add, pow_add]; ring
  have hiter : ∀ k : ℕ, a ^ m = a ^ (m + k) * x ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hstep k, show m + (k + 1) = m + k + 1 from rfl, pow_succ]
      ring
  refine ⟨a ^ m * x ^ m, x, ?_, ?_, m, ?_⟩
  · change a ^ m * x ^ m * (a ^ m * x ^ m) = a ^ m * x ^ m
    calc a ^ m * x ^ m * (a ^ m * x ^ m) = (a ^ (m + m) * x ^ m) * x ^ m := by rw [pow_add]; ring
      _ = a ^ m * x ^ m := by rw [← hiter m]
  · calc a * x * (a ^ m * x ^ m) = a ^ (m + 1) * x * x ^ m := by rw [pow_succ]; ring
      _ = a ^ m * x ^ m := by rw [← hmx]
  · rw [Ideal.mem_span_singleton']
    refine ⟨a ^ m, ?_⟩
    calc a ^ m * (a ^ m * x ^ m) = a ^ (m + m) * x ^ m := by rw [pow_add]; ring
      _ = a ^ m := (hiter m).symm
