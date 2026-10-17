/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Module.IdempotentDecomposition
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The rank decomposition of a finitely generated projective module (`GPR Exc. 9.31`)

A finitely generated projective module `M` over a commutative ring `R` takes only finitely many
ranks, and `R` splits — uniquely — into a finite product of rings on each factor of which `M`
becomes of constant rank.

This is the tool that lets constant-rank hypotheses be assumed without loss of generality: `GPR`
uses it repeatedly, in the form "by the rank decomposition we may assume `M` (or the composition
algebra `C`) has constant rank `r`".

## Main definitions

* `Module.rankIdempotent R M i` : the unique idempotent of `R` cutting out
  `{p ∈ Spec R | rankAtStalk M p = i}`.

## Main results

* `Module.finite_range_rankAtStalk` : **`GPR Exc. 9.31(a)`** — the set of ranks of `M` is finite.
* `Module.completeOrthogonalIdempotents_rankIdempotent` : the `rankIdempotent R M i`, for `i`
  ranging over any finite set containing all the ranks, form a complete orthogonal system of
  idempotents. With `CompleteOrthogonalIdempotents.bijective_pi` this is the ring decomposition
  `R ≃ ∏ᵢ R ⧸ (1 - εᵢ)` of **`GPR Exc. 9.31(b)`**(1), and with
  `CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor`
  (`Module/IdempotentDecomposition.lean`) the module decomposition (2).
* `Module.rankAtStalk_quotientTensor_rankIdempotent` : on the `i`th factor, `M` has constant
  rank `i`. This is the point of the whole construction.
* `Module.rankAtStalk_baseChange_of_eq` : constant rank survives base change.
* `Module.nonempty_basis_atPrime_of_rankAtStalk_eq` : a module of constant rank `n` is free of
  rank `n` at every prime.
* `Module.eq_rankIdempotent_of_completeOrthogonalIdempotents` : **uniqueness** — any complete
  orthogonal system with pairwise distinct constant ranks on its factors is the one above.

## Proof idea

`Module.rankAtStalk` is locally constant on `Spec R` for a finitely presented flat module
(mathlib's `Module.isLocallyConstant_rankAtStalk`), and `Spec R` is quasi-compact, so the range is
finite — that is (a). Each fibre `Uᵢ := {p | rankAtStalk M p = i}` is then clopen, so by
`GPR Exc. 9.29` — mathlib's `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` —
there is a unique idempotent `εᵢ` with `D(εᵢ) = Uᵢ`. Orthogonality and completeness are read off
from the fact that the `Uᵢ` partition `Spec R`, via the observation that an idempotent whose
basic open set is empty is nilpotent, hence zero.

That the `i`th factor has constant rank `i` is `Module.rankAtStalk_baseChange`: a prime of
`R ⧸ (1 - εᵢ)` pulls back to a prime of `R` at which `εᵢ` is a unit — indeed `εᵢ ↦ 1` — hence to
a point of `D(εᵢ) = Uᵢ`.

Uniqueness follows because a competing system's basic opens are contained in the corresponding
`Uᵢ` (same base-change computation, in the other direction, using that `Spec (R ⧸ (1 - ηⱼ))`
surjects onto `D(ηⱼ)`) and both families cover `Spec R`.

## Implementation notes

`GPR` indexes the decomposition by all of `ℕ`, with `εᵢ = 0` for `i` outside the (finite) set of
ranks. `Module.rankIdempotent` is likewise defined for every `i : ℕ` and is `0` off the range
(`Module.rankIdempotent_eq_zero_of_notMem_range`), but the complete-orthogonal-system statement is
indexed by a `Finset ℕ` containing the ranks, since mathlib's `CompleteOrthogonalIdempotents`
requires a `Fintype`.

The rank is mathlib's `Module.rankAtStalk`, not a bespoke rank function; `GPR` writes `rk_p(M)`
for the same thing.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 9.29,
  Exc. 9.31.
-/

@[expose] public section

universe u v

open scoped TensorProduct

open PrimeSpectrum

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- An idempotent whose basic open set is empty is zero: it is nilpotent, and a nilpotent
idempotent vanishes. This is how orthogonality and completeness of the rank idempotents get
proved — both reduce to a basic open set being empty. -/
private theorem eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot {S : Type u} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (h : basicOpen e = ⊥) : e = 0 :=
  he.eq_zero_of_isNilpotent ((basicOpen_eq_bot_iff e).mp h)

/-- **`GPR Exc. 9.31(a)`.** A finitely generated projective module takes only finitely many ranks.

`Module.rankAtStalk` is locally constant and `Spec R` is quasi-compact. -/
theorem Module.finite_range_rankAtStalk :
    (Set.range (Module.rankAtStalk (R := R) M)).Finite := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).range_finite

/-- The locus where `M` has rank `i` is clopen. -/
theorem Module.isClopen_setOf_rankAtStalk_eq (i : ℕ) :
    IsClopen {p : PrimeSpectrum R | Module.rankAtStalk (R := R) M p = i} := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).isClopen_fiber i

/-- The idempotent of `R` cutting out the locus where `M` has rank `i` (`GPR Exc. 9.31(b)`,
`GPR Exc. 9.29`). It is `0` exactly when `M` has rank `i` nowhere. -/
noncomputable def Module.rankIdempotent (i : ℕ) : R :=
  (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (Module.isClopen_setOf_rankAtStalk_eq R M i)).choose

theorem Module.isIdempotentElem_rankIdempotent (i : ℕ) :
    IsIdempotentElem (Module.rankIdempotent R M i) :=
  (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (Module.isClopen_setOf_rankAtStalk_eq R M i)).choose_spec.1

theorem Module.coe_basicOpen_rankIdempotent (i : ℕ) :
    (basicOpen (Module.rankIdempotent R M i) : Set (PrimeSpectrum R)) =
      {p | Module.rankAtStalk (R := R) M p = i} :=
  ((PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (Module.isClopen_setOf_rankAtStalk_eq R M i)).choose_spec.2).symm

theorem Module.rankAtStalk_eq_of_mem_basicOpen_rankIdempotent {i : ℕ} {p : PrimeSpectrum R}
    (hp : p ∈ basicOpen (Module.rankIdempotent R M i)) :
    Module.rankAtStalk (R := R) M p = i := by
  rw [← Set.mem_ofPred_eq (p := fun p ↦ Module.rankAtStalk (R := R) M p = i),
    ← Module.coe_basicOpen_rankIdempotent R M i]
  exact hp

/-- The rank idempotents are characterized by their basic open sets: an idempotent cutting out the
rank-`i` locus *is* `Module.rankIdempotent R M i` (`GPR Exc. 9.29(b)`). -/
theorem Module.eq_rankIdempotent_of_coe_basicOpen_eq {e : R} (he : IsIdempotentElem e) (i : ℕ)
    (h : (basicOpen e : Set (PrimeSpectrum R)) =
      {p | Module.rankAtStalk (R := R) M p = i}) :
    e = Module.rankIdempotent R M i :=
  PrimeSpectrum.basicOpen_injOn_isIdempotentElem he (Module.isIdempotentElem_rankIdempotent R M i)
    (SetLike.ext' (by rw [h, Module.coe_basicOpen_rankIdempotent]))

/-- Distinct ranks give orthogonal idempotents: the rank loci are disjoint. -/
theorem Module.rankIdempotent_mul_rankIdempotent {i j : ℕ} (h : i ≠ j) :
    Module.rankIdempotent R M i * Module.rankIdempotent R M j = 0 := by
  refine eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot
    ((Module.isIdempotentElem_rankIdempotent R M i).mul
      (Module.isIdempotentElem_rankIdempotent R M j)) ?_
  refine SetLike.ext' (Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_)
  rw [PrimeSpectrum.basicOpen_mul] at hp
  exact h ((Module.rankAtStalk_eq_of_mem_basicOpen_rankIdempotent R M hp.1).symm.trans
    (Module.rankAtStalk_eq_of_mem_basicOpen_rankIdempotent R M hp.2))

/-- Ranks that do not occur give the zero idempotent. -/
theorem Module.rankIdempotent_eq_zero_of_notMem_range {i : ℕ}
    (h : i ∉ Set.range (Module.rankAtStalk (R := R) M)) :
    Module.rankIdempotent R M i = 0 := by
  refine eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot
    (Module.isIdempotentElem_rankIdempotent R M i) (SetLike.ext' ?_)
  rw [Module.coe_basicOpen_rankIdempotent]
  exact Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ h ⟨p, hp⟩

/-- **`GPR Exc. 9.31(b)`, existence.** For any finite set of naturals containing every rank of
`M`, the corresponding rank idempotents form a complete orthogonal system.

Feeding this to `CompleteOrthogonalIdempotents.bijective_pi` gives the ring decomposition
`R ≃ ∏ᵢ R ⧸ (1 - εᵢ)`, and to
`CompleteOrthogonalIdempotents.linearEquivPiQuotientTensor` the module decomposition
`M ≃ ∏ᵢ (R ⧸ (1 - εᵢ)) ⊗[R] M`. -/
theorem Module.completeOrthogonalIdempotents_rankIdempotent (s : Finset ℕ)
    (hs : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p ∈ s) :
    CompleteOrthogonalIdempotents (fun i : s ↦ Module.rankIdempotent R M i) := by
  refine CompleteOrthogonalIdempotents.of_prod_one_sub
    ⟨fun i ↦ Module.isIdempotentElem_rankIdempotent R M i, fun i j hij ↦
      Module.rankIdempotent_mul_rankIdempotent R M (Subtype.coe_ne_coe.mpr hij)⟩ ?_
  -- The product of the `1 - εᵢ` is an idempotent whose basic open set is empty, since the rank
  -- loci for `i ∈ s` cover `Spec R`.
  refine eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot
    (Finset.prod_induction _ IsIdempotentElem (fun _ _ ↦ IsIdempotentElem.mul)
      (IsIdempotentElem.one) fun i _ ↦ (Module.isIdempotentElem_rankIdempotent R M i).one_sub) ?_
  refine SetLike.ext' (Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_)
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp
  set i₀ : s := ⟨Module.rankAtStalk (R := R) M p, hs p⟩ with hi₀
  -- `1 - ε_{i₀}` divides the product, so it too is outside `p`.
  have hone : (1 : R) - Module.rankIdempotent R M i₀ ∉ p.asIdeal := by
    intro hmem
    obtain ⟨c, hc⟩ :=
      Finset.dvd_prod_of_mem (fun i : s ↦ 1 - Module.rankIdempotent R M i) (Finset.mem_univ i₀)
    exact hp (hc ▸ p.asIdeal.mul_mem_right c hmem)
  -- But `ε_{i₀}` is also outside `p`, since `p` lies in the rank-`i₀` locus.
  have hidem : Module.rankIdempotent R M (i₀ : ℕ) ∉ p.asIdeal := by
    have : p ∈ (basicOpen (Module.rankIdempotent R M (i₀ : ℕ)) : Set (PrimeSpectrum R)) := by
      rw [Module.coe_basicOpen_rankIdempotent]; rfl
    rwa [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at this
  have hzero :
      Module.rankIdempotent R M (i₀ : ℕ) * (1 - Module.rankIdempotent R M i₀) = 0 := by
    rw [mul_sub, mul_one, (Module.isIdempotentElem_rankIdempotent R M i₀).eq, sub_self]
  rcases p.isPrime.mem_or_mem (hzero ▸ p.asIdeal.zero_mem) with h | h
  · exact hidem h
  · exact hone h

/-- In `R ⧸ (1 - ε)`, an idempotent `ε` becomes `1`. -/
private theorem algebraMap_quotient_one_sub_eq_one {e : R} :
    algebraMap R (R ⧸ Ideal.span {1 - e}) e = 1 := by
  rw [Ideal.Quotient.algebraMap_eq]
  have h : (Ideal.Quotient.mk (Ideal.span {1 - e})) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

/-- **The point of the rank decomposition.** On the factor `R ⧸ (1 - εᵢ)`, the module `M` has
constant rank `i`.

Every prime of the factor pulls back to a prime of `R` at which `εᵢ` is invertible — it maps to
`1` — hence to a point of `D(εᵢ)`, which is exactly the rank-`i` locus. -/
theorem Module.rankAtStalk_quotientTensor_rankIdempotent (i : ℕ) :
    Module.rankAtStalk (R := R ⧸ Ideal.span {1 - Module.rankIdempotent R M i})
      ((R ⧸ Ideal.span {1 - Module.rankIdempotent R M i}) ⊗[R] M) = fun _ ↦ i := by
  funext p
  rw [Module.rankAtStalk_baseChange]
  refine Module.rankAtStalk_eq_of_mem_basicOpen_rankIdempotent R M ?_
  rw [PrimeSpectrum.mem_basicOpen]
  intro hmem
  refine p.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
  rw [← algebraMap_quotient_one_sub_eq_one R (e := Module.rankIdempotent R M i)]
  exact hmem

/-- **`GPR Exc. 9.31(b)`, uniqueness.** A complete orthogonal system of idempotents whose factors
give `M` pairwise distinct constant ranks consists of rank idempotents.

Injectivity of `r` is needed: without it two factors could carry the same rank, and their
idempotents would sum to — rather than equal — the corresponding rank idempotent. -/
theorem Module.eq_rankIdempotent_of_completeOrthogonalIdempotents {ι : Type*} [Fintype ι]
    (η : ι → R) (hη : CompleteOrthogonalIdempotents η) (r : ι → ℕ)
    (hr : Function.Injective r)
    (h : ∀ j, Module.rankAtStalk (R := R ⧸ Ideal.span {1 - η j})
      ((R ⧸ Ideal.span {1 - η j}) ⊗[R] M) = fun _ ↦ r j) (j : ι) :
    η j = Module.rankIdempotent R M (r j) := by
  -- Each `D(η j)` sits inside the rank-`r j` locus.
  have hsub : ∀ k : ι, ∀ p ∈ basicOpen (η k),
      Module.rankAtStalk (R := R) M p = r k := by
    intro k p hp
    -- `η k ∉ p` forces `1 - η k ∈ p`, so `p` comes from a prime of `R ⧸ (1 - η k)`.
    have hone : (1 : R) - η k ∈ p.asIdeal := by
      rcases p.isPrime.mem_or_mem (show η k * (1 - η k) ∈ p.asIdeal by
        rw [mul_sub, mul_one, (hη.idem k).eq, sub_self]; exact p.asIdeal.zero_mem) with hk | hk
      · exact absurd hk (PrimeSpectrum.mem_basicOpen _ _ |>.mp hp)
      · exact hk
    have hrange : p ∈ Set.range
        (PrimeSpectrum.comap (algebraMap R (R ⧸ Ideal.span {1 - η k}))) := by
      rw [Ideal.Quotient.algebraMap_eq,
        range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hone)
    obtain ⟨q, rfl⟩ := hrange
    rw [← Module.rankAtStalk_baseChange (M := M) q, h k]
  -- The `D(η k)` cover `Spec R`, because the `η k` sum to `1`.
  have hcover : ∀ p : PrimeSpectrum R, ∃ k, p ∈ basicOpen (η k) := by
    intro p
    by_contra hcon
    simp only [not_exists, PrimeSpectrum.mem_basicOpen, not_not] at hcon
    exact p.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr
      (hη.complete ▸ Ideal.sum_mem _ fun k _ ↦ hcon k))
  refine Module.eq_rankIdempotent_of_coe_basicOpen_eq R M (hη.idem j) (r j) (Set.ext fun p ↦ ?_)
  refine ⟨fun hp ↦ hsub j p hp, fun hp ↦ ?_⟩
  obtain ⟨k, hk⟩ := hcover p
  have : r k = r j := (hsub k p hk).symm.trans hp
  exact hr this ▸ hk

/-! ### The decomposition, packaged

Indexing by the set of ranks itself, so that no `Finset` has to be supplied at the call site. -/

/-- The set of ranks of `M`, as a `Finset` — finite by `GPR Exc. 9.31(a)`. `GPR` writes
`Rk(M)`. -/
noncomputable def Module.rankFinset : Finset ℕ :=
  (Module.finite_range_rankAtStalk R M).toFinset

@[simp]
theorem Module.mem_rankFinset {i : ℕ} :
    i ∈ Module.rankFinset R M ↔ i ∈ Set.range (Module.rankAtStalk (R := R) M) :=
  Set.Finite.mem_toFinset _

theorem Module.rankAtStalk_mem_rankFinset (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) M p ∈ Module.rankFinset R M :=
  (Module.mem_rankFinset R M).mpr ⟨p, rfl⟩

/-- The rank idempotents indexed by `Rk(M)` form a complete orthogonal system. -/
theorem Module.completeOrthogonalIdempotents_rankIdempotent_rankFinset :
    CompleteOrthogonalIdempotents
      (fun i : Module.rankFinset R M ↦ Module.rankIdempotent R M i) :=
  Module.completeOrthogonalIdempotents_rankIdempotent R M _ (Module.rankAtStalk_mem_rankFinset R M)

/-- **`GPR Exc. 9.31(b)`(1), the rank decomposition of the ring.** `R` is the product of the
rings `R ⧸ (1 - εᵢ)`, one for each rank `i` of `M`. -/
noncomputable def Module.rankDecompositionRingEquiv :
    R ≃+* ∀ i : Module.rankFinset R M, R ⧸ Ideal.span {1 - Module.rankIdempotent R M i} :=
  RingEquiv.ofBijective _
    (Module.completeOrthogonalIdempotents_rankIdempotent_rankFinset R M).bijective_pi

/-- **`GPR Exc. 9.31(b)`(2), the rank decomposition of the module.** `M` is the product of its
base changes to the factor rings, and by
`Module.rankAtStalk_quotientTensor_rankIdempotent` the `i`th of these has **constant rank `i`**.

This is what licenses "by the rank decomposition we may assume `M` has constant rank". -/
noncomputable def Module.rankDecompositionLinearEquiv :
    M ≃ₗ[R] ∀ i : Module.rankFinset R M,
      (R ⧸ Ideal.span {1 - Module.rankIdempotent R M i}) ⊗[R] M :=
  (Module.completeOrthogonalIdempotents_rankIdempotent_rankFinset R M).linearEquivPiQuotientTensor
    M _

/-! ### The rank-zero idempotent

`ε₀ = Module.rankIdempotent R M 0` cuts out the locus where `M` vanishes. Two facts about it are
used, without ever performing the product decomposition of `R` that it induces:

* it **annihilates** `M` (`Module.rankIdempotent_zero_smul`), and
* it is a **unit** at every maximal ideal where `M` has trivial residue space
  (`Module.notMem_rankIdempotent_zero`).

Together they let an argument treat the vanishing locus of `M` separately while staying over `R`:
multiplying by `ε₀` kills everything coming from `M`, and reducing modulo a maximal ideal in the
vanishing locus turns `ε₀` into `1`. -/

/-- **The rank-zero idempotent annihilates `M`.**

Checked one maximal ideal `P` at a time. If `ε₀ ∈ P` then `1 - ε₀ ∉ P` annihilates `ε₀ • x`; if
`ε₀ ∉ P` then `M` has rank `0` at `P`, so `P` is outside the support of `M` and some `r ∉ P`
already annihilates `x`. An element annihilated modulo every maximal ideal is zero. -/
theorem Module.rankIdempotent_zero_smul (x : M) : Module.rankIdempotent R M 0 • x = 0 := by
  set e := Module.rankIdempotent R M 0 with he
  by_contra hx
  have hne : (R ∙ (e • x)).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ (R ∙ (e • x)).annihilator := by rw [h]; exact Submodule.mem_top
    exact hx (by simpa using (Submodule.mem_annihilator_span_singleton _ _).mp h1)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hann : ∃ r ∉ P, r • (e • x) = 0 := by
    by_cases hmem : e ∈ P
    · refine ⟨1 - e, fun hc ↦ hP.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_), ?_⟩
      · simpa using P.add_mem hc hmem
      · rw [smul_smul, sub_mul, one_mul, (Module.isIdempotentElem_rankIdempotent R M 0).eq,
          sub_self, zero_smul]
    · have hrank : Module.rankAtStalk (R := R) M ⟨P, hP.isPrime⟩ = 0 :=
        Module.rankAtStalk_eq_of_mem_basicOpen_rankIdempotent R M
          ((PrimeSpectrum.mem_basicOpen _ _).mpr hmem)
      obtain ⟨r, hr, hr0⟩ := Module.notMem_support_iff'.mp
        ((Module.rankAtStalk_eq_zero_iff_notMem_support _).mp hrank) x
      exact ⟨r, hr, by rw [smul_comm, hr0, smul_zero]⟩
  obtain ⟨r, hr, hr0⟩ := hann
  exact hr (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr hr0))

/-- **The rank-zero idempotent is a unit where `M` vanishes.** If `M ⊗ κ(𝔪)` is trivial at a
maximal ideal `𝔪` then `ε₀ ∉ 𝔪`.

`M ⊗ R⧸𝔪` is `M ⧸ 𝔪 M`, whose support is `Supp M ∩ V(𝔪)`; triviality makes that empty, and `𝔪`
lies in `V(𝔪)`, so `𝔪 ∉ Supp M` — that is, `M` has rank `0` at `𝔪`, which is exactly membership
in `D(ε₀)`. -/
theorem Module.notMem_rankIdempotent_zero (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (h : Subsingleton ((R ⧸ 𝔪) ⊗[R] M)) : Module.rankIdempotent R M 0 ∉ 𝔪 := by
  have : Subsingleton (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M 𝔪).symm.toEquiv.subsingleton
  have hsupp : Module.support R M ∩ PrimeSpectrum.zeroLocus (𝔪 : Set R) = ∅ := by
    rw [← Module.support_quotient (M := M) 𝔪]
    exact Module.support_eq_empty_iff.mpr ‹_›
  have hns : (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum R) ∉ Module.support R M := fun hc ↦
    Set.eq_empty_iff_forall_notMem.mp hsupp _
      ⟨hc, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  refine (PrimeSpectrum.mem_basicOpen _ (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum R)).mp ?_
  rw [← SetLike.mem_coe, Module.coe_basicOpen_rankIdempotent]
  exact (Module.rankAtStalk_eq_zero_iff_notMem_support _).mpr hns

/-! ### Detecting vanishing on the factors

The two lemmas the phrase "by the rank decomposition we may assume constant rank" needs when the
statement to be transported is an *equation* rather than a structure: an element of `M` vanishes as
soon as it vanishes in each `(R ⧸ (1 - εᵢ)) ⊗ M`. They are stated separately because the second is
about a single factor and carries no finiteness. -/

/-- An element killed by every rank idempotent is zero, the idempotents summing to `1`. -/
theorem Module.eq_zero_of_forall_rankIdempotent_smul_eq_zero {x : M}
    (h : ∀ i : Module.rankFinset R M, Module.rankIdempotent R M i • x = 0) : x = 0 := by
  have hsum := (Module.completeOrthogonalIdempotents_rankIdempotent_rankFinset R M).complete
  calc x = (∑ i : Module.rankFinset R M, Module.rankIdempotent R M i) • x := by rw [hsum, one_smul]
  _ = ∑ i : Module.rankFinset R M, Module.rankIdempotent R M i • x := Finset.sum_smul ..
  _ = 0 := by simp [h]

/-- If `x` dies in the `i`th factor `(R ⧸ (1 - εᵢ)) ⊗ M` of the rank decomposition, then `εᵢ`
kills it.

Reducing `M` modulo an ideal is tensoring with the quotient ring
(`TensorProduct.quotTensorEquivQuotSMul`), so the hypothesis says `x ∈ span{1 - εᵢ} • ⊤`; and `εᵢ`
annihilates that submodule, since `εᵢ(1 - εᵢ) = 0`. -/
theorem Module.rankIdempotent_smul_eq_zero_of_one_tmul_eq_zero (i : ℕ) {x : M}
    (h : (1 : R ⧸ Ideal.span {1 - Module.rankIdempotent R M i}) ⊗ₜ[R] x = 0) :
    Module.rankIdempotent R M i • x = 0 := by
  set e := Module.rankIdempotent R M i with he
  set I : Ideal R := Ideal.span {1 - e} with hI
  have hmk : (Submodule.Quotient.mk x : M ⧸ (I • ⊤ : Submodule R M)) = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := M) I x, h, map_zero]
  have hmem : x ∈ (I • ⊤ : Submodule R M) := by
    rwa [Submodule.Quotient.mk_eq_zero] at hmk
  refine Submodule.smul_induction_on hmem ?_ ?_
  · intro r hr n _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hidem : e * e = e := Module.isIdempotentElem_rankIdempotent R M i
    rw [smul_smul, show e * (c * (1 - e)) = c * (e - e * e) by ring, hidem, sub_self, mul_zero,
      zero_smul]
  · intro a b ha hb
    rw [smul_add, ha, hb, add_zero]

/-! ### Constant rank means locally free of that rank -/

/-- Constant rank survives base change: if `M` has rank `n` at every prime of `R`, then `S ⊗[R] M`
has rank `n` at every prime of `S`. -/
theorem Module.rankAtStalk_baseChange_of_eq {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] [Module.Finite R M] (S : Type*) [CommRing S]
    [Algebra R S] {n : ℕ} (hM : Module.rankAtStalk (R := R) M = fun _ ↦ n) :
    Module.rankAtStalk (R := S) (S ⊗[R] M) = fun _ ↦ n := by
  funext p
  rw [Module.rankAtStalk_baseChange, hM]

/-- A finitely generated projective module of constant rank `n` becomes free of rank `n` at every
prime. -/
theorem Module.nonempty_basis_atPrime_of_rankAtStalk_eq {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (hM : Module.rankAtStalk (R := R) M = fun _ ↦ n) (J : Ideal R) [J.IsPrime] :
    Nonempty (Module.Basis (Fin n) (Localization.AtPrime J) (Localization.AtPrime J ⊗[R] M)) := by
  let S := Localization.AtPrime J
  have : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have hfin : Module.finrank S (S ⊗[R] M) = n := by
    have h := congrFun hM ⟨J, inferInstance⟩
    rw [Module.rankAtStalk_eq_finrank_tensorProduct] at h
    simpa [S] using h
  exact ⟨Module.finBasisOfFinrankEq S (S ⊗[R] M) hfin⟩
