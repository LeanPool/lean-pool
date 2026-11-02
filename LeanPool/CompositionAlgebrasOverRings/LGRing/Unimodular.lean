/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs
public import LeanPool.CompositionAlgebrasOverRings.Module.Unimodular
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Faithfully projective modules over an LG-ring contain a unimodular element (`GN 2.6(a)`)

Over an LG-ring `R`, a finitely generated projective module `M` that is nonzero at every residue
field contains a unimodular element.

## Main definitions

* `MvPolynomial.bilinearPairing E` : for a square array `E : Fin n → Fin n → R`, the polynomial
  `∑ᵢ ∑ⱼ C (E i j) * X (castAdd n j) * X (natAdd n i)` in `n + n` variables. The first block of
  variables is a column vector `t`, the second a row vector `c`, and the polynomial is the
  pairing `cᵀ E t`.

## Main results

* `IsLGRing.exists_isUnimodular` : **`GN 2.6(a)`**. If `R` is an LG-ring and `M` is finitely
  generated projective with `(R ⧸ 𝔪) ⊗[R] M ≠ 0` for every maximal `𝔪`, then `M` contains a
  unimodular element.

## Proof idea

Write `M` as a retract of a finite free module: `π : Rⁿ ↠ M` and `σ : M ↪ Rⁿ` with `π ∘ σ = id`
(`Module.Finite.exists_comp_eq_id_of_projective`). Put `e := σ ∘ π`, an idempotent endomorphism of
`Rⁿ`, and let `E i j := e (Pi.single j 1) i` be its matrix in the standard basis.

For `t c : Fin n → R` set `m := π t` and `l := ∑ᵢ cᵢ · (proj i ∘ σ) : M →ₗ[R] R`. Then

  `l m = ∑ᵢ cᵢ · (e t)ᵢ = ∑ᵢ ∑ⱼ Eᵢⱼ tⱼ cᵢ`,

which is exactly `bilinearPairing E` evaluated at the point `(t, c)` — and by `GPR 9.13`
(`Module.isUnimodular_of_apply_eq_one`), a value of `1` produces a unimodular element.
So it suffices to know that `bilinearPairing E` represents a unit over `R`, and by the LG axiom
that reduces to representing a unit over every residue field `k = R ⧸ 𝔪`.

Over `k` the polynomial represents a unit as soon as some entry of `E` survives in `k`: take `t`
and `c` to be the corresponding standard basis vectors, and the double sum collapses to that
entry. And if *every* entry died in `k`, then `e ⊗ k = 0`; since `π ⊗ k` and `σ ⊗ k` still
compose to the identity of `k ⊗[R] M`, every `x` there satisfies
`σₖ x = σₖ (πₖ (σₖ x)) = eₖ (σₖ x) = 0`, hence `x = πₖ (σₖ x) = 0`, contradicting the hypothesis
that `k ⊗[R] M` is nonzero.

## Implementation notes

The hypothesis is stated as `Nontrivial ((R ⧸ 𝔪) ⊗[R] M)` for every maximal `𝔪` rather than as
`Module.HasFullSupport` (`QuadraticForm/Representation.lean`), for two reasons: it is exactly what
the proof consumes — the LG axiom quantifies over residue fields — and it keeps this file below
`QuadraticForm/` in the import order. `Module.HasFullSupport.nontrivial_quotient_tensor` supplies
it, and `Module.exists_isUnimodular_of_hasFullSupport` in `QuadraticForm/Representation.lean`
packages the combination.

Following the implementation notes of `LGRing/Defs.lean`, the residue field is handled through the
`Prop`-valued `IsField (R ⧸ 𝔪)` rather than the bundled `Field` instance from
`Ideal.Quotient.field`, which avoids the instance diamond entirely.

`GN` proves 2.6(a) by scheme theory, applying its Proposition 2.4 to the punctured affine space
`W(M) ∖ Spec(R)`, a quasi-compact open subscheme; that is a stronger form of the LG axiom than the
one taken as the definition here. The argument above is elementary and uses only the single-
polynomial axiom, at the cost of choosing a presentation of `M`.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Lemma 2.6(a).
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.13, 11.24.
-/

@[expose] public section

universe u v

open scoped TensorProduct

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The **pairing polynomial** of a square array `E`, in `n + n` variables: reading the first
block of variables as a column vector `t` and the second as a row vector `c`, this is `cᵀ E t`. -/
noncomputable def MvPolynomial.bilinearPairing (E : Fin n → Fin n → R) :
    MvPolynomial (Fin (n + n)) R :=
  ∑ i, ∑ j, MvPolynomial.C (E i j) * MvPolynomial.X (Fin.castAdd n j) *
    MvPolynomial.X (Fin.natAdd n i)

/-- Evaluating `bilinearPairing E` over an `R`-algebra `S` gives the double sum `∑ᵢ ∑ⱼ Eᵢⱼ tⱼ cᵢ`,
where `t` and `c` are the two blocks of the evaluation point. -/
theorem MvPolynomial.aeval_bilinearPairing {S : Type v} [CommRing S] [Algebra R S]
    (E : Fin n → Fin n → R) (s : Fin (n + n) → S) :
    MvPolynomial.aeval s (MvPolynomial.bilinearPairing E) =
      ∑ i, ∑ j, algebraMap R S (E i j) * s (Fin.castAdd n j) * s (Fin.natAdd n i) := by
  simp only [bilinearPairing, map_sum, map_mul, aeval_C, aeval_X]

/-- At the pair of standard basis vectors indexed by `j₀` and `i₀`, the double sum of
`aeval_bilinearPairing` collapses to the single entry `Eᵢ₀ⱼ₀`. -/
private theorem sum_sum_mul_single_mul_single {S : Type v} [CommRing S] (a : Fin n → Fin n → S)
    (i₀ j₀ : Fin n) :
    ∑ i, ∑ j, a i j * (Pi.single j₀ 1 : Fin n → S) j * (Pi.single i₀ 1 : Fin n → S) i =
      a i₀ j₀ := by
  classical
  rw [Finset.sum_eq_single i₀ (fun i _ hi ↦ Finset.sum_eq_zero fun j _ ↦ by
    simp [Pi.single_eq_of_ne hi]) (fun h ↦ absurd (Finset.mem_univ i₀) h)]
  rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun h ↦ absurd (Finset.mem_univ j₀) h)]
  simp

/-- Every vector of `Fin n → R` is the sum of its coordinates against the standard basis. -/
private theorem sum_smul_single_eq_self (t : Fin n → R) :
    ∑ j, t j • (Pi.single j 1 : Fin n → R) = t := by
  classical
  simpa using (Pi.basisFun R (Fin n)).sum_repr t

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- **`GN 2.6(a)`.** Over an LG-ring, a finitely generated projective module that is nonzero at
every residue field contains a unimodular element.

See the module docstring for the construction; `Module.HasFullSupport.nontrivial_quotient_tensor`
supplies the hypothesis from the more geometric formulation. -/
theorem IsLGRing.exists_isUnimodular [Module.Finite R M] [Module.Projective R M]
    (hLG : IsLGRing R)
    (hM : ∀ (𝔪 : Ideal R), 𝔪.IsMaximal → Nontrivial ((R ⧸ 𝔪) ⊗[R] M)) :
    ∃ m : M, Module.IsUnimodular R m := by
  classical
  obtain ⟨n, π, σ, -, -, hσ⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set e : (Fin n → R) →ₗ[R] (Fin n → R) := σ ∘ₗ π with he
  set E : Fin n → Fin n → R := fun i j ↦ e (Pi.single j 1) i with hE
  -- The matrix `E` computes `e` on every vector.
  have hcoord : ∀ (t : Fin n → R) (i : Fin n), e t i = ∑ j, E i j * t j := by
    intro t i
    conv_lhs => rw [← sum_smul_single_eq_self t]
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hE]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  -- The pairing polynomial of `E` represents a unit over every residue field, hence over `R`.
  have hrep : (MvPolynomial.bilinearPairing E).RepresentsUnit R := by
    refine (hLG (n + n) _).mpr fun 𝔪 hmax ↦ ?_
    have hfield : IsField (R ⧸ 𝔪) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp hmax
    -- Some entry of `E` survives in the residue field: otherwise `e` dies there, and with it
    -- the retract `(R ⧸ 𝔪) ⊗[R] M`.
    have hne : ∃ i j, algebraMap R (R ⧸ 𝔪) (E i j) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hek :
          ∀ y : (R ⧸ 𝔪) ⊗[R] (Fin n → R), LinearMap.baseChange (R ⧸ 𝔪) e y = 0 := by
        intro y
        induction y using TensorProduct.inductionOn with
        | tmul a t =>
          rw [LinearMap.baseChange_tmul]
          conv_lhs => rw [← sum_smul_single_eq_self (e t)]
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          have hzero : (e t i) • a = 0 := by
            rw [Algebra.smul_def, hcoord t i, map_sum]
            simp only [map_mul, hcon, zero_mul, Finset.sum_const_zero, zero_mul]
          rw [hzero, TensorProduct.zero_tmul]
        | add x y hx hy => rw [map_add, hx, hy, add_zero]
      have hid : ∀ x : (R ⧸ 𝔪) ⊗[R] M,
          LinearMap.baseChange (R ⧸ 𝔪) π (LinearMap.baseChange (R ⧸ 𝔪) σ x) = x := by
        have h : LinearMap.baseChange (R ⧸ 𝔪) π ∘ₗ LinearMap.baseChange (R ⧸ 𝔪) σ =
            LinearMap.id := by
          rw [← LinearMap.baseChange_comp, hσ, LinearMap.baseChange_id]
        exact fun x ↦ DFunLike.congr_fun h x
      have hzero : ∀ x : (R ⧸ 𝔪) ⊗[R] M, x = 0 := by
        intro x
        have hσx : LinearMap.baseChange (R ⧸ 𝔪) σ x = 0 := by
          conv_lhs => rw [← hid x]
          have := hek (LinearMap.baseChange (R ⧸ 𝔪) σ x)
          rwa [he, LinearMap.baseChange_comp] at this
        rw [← hid x, hσx, map_zero]
      obtain ⟨x, y, hxy⟩ := (hM 𝔪 hmax).exists_pair_ne
      exact hxy (by rw [hzero x, hzero y])
    obtain ⟨i₀, j₀, hij⟩ := hne
    refine
      ⟨Fin.addCases (motive := fun _ ↦ R ⧸ 𝔪) (Pi.single j₀ 1) (Pi.single i₀ 1), ?_⟩
    rw [MvPolynomial.aeval_bilinearPairing]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [sum_sum_mul_single_mul_single]
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hij
    exact IsUnit.of_mul_eq_one b hb
  -- Descend the witness: it is a functional taking the value `1` on a point of `M`.
  obtain ⟨s, hs⟩ := hrep
  set t : Fin n → R := fun j ↦ s (Fin.castAdd n j) with ht
  set c : Fin n → R := fun i ↦ s (Fin.natAdd n i) with hc
  have htj : ∀ j, t j = s (Fin.castAdd n j) := fun _ ↦ rfl
  have hci : ∀ i, c i = s (Fin.natAdd n i) := fun _ ↦ rfl
  set l : M →ₗ[R] R :=
    ∑ i, c i • ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ σ) with hl
  have hlm : l (π t) = MvPolynomial.aeval s (MvPolynomial.bilinearPairing E) := by
    rw [MvPolynomial.aeval_bilinearPairing, hl]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      smul_eq_mul, Algebra.algebraMap_self_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hei : σ (π t) i = ∑ j, E i j * t j := hcoord t i
    rw [LinearMap.proj_apply, hei, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [htj, hci]; ring
  rw [← hlm] at hs
  refine ⟨π t, Module.isUnimodular_of_apply_eq_one (f := (hs.unit⁻¹ : Rˣ) • l) ?_⟩
  rw [LinearMap.smul_apply, Units.smul_def, smul_eq_mul]
  exact hs.val_inv_mul
