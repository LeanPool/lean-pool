/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.HorrocksLattice
public import LeanPool.QuillenSuslin.MonicLocalization

import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integer

/-!
# Horrocks' theorem over a local ring

For a local ring `A`, a finitely generated projective `A[X]`-module `P` that becomes free over
`A⟨X⟩`, the localisation of `A[X]` at the monic polynomials, is free (Lombardi–Quitté,
Theorem XVI.4.3; Horrocks 1964 for a local Noetherian `A`; Quillen 1976, Theorem 3). A basis of
`A⟨X⟩ ⊗[A[X]] P`, after clearing denominators, gives a monic lattice in `P`
(`exists_lattice_of_free`), and `free_of_lattice` concludes.

## Main results

* `exists_lattice_of_free`: a finitely generated `A[X]`-module that is free over `A⟨X⟩` contains a
  monic lattice.
* `free_of_free_monicLocalization_of_isLocalRing`: the local Horrocks theorem.

## References

* G. Horrocks, *Projective modules over an extension of a local ring*, Proc. London Math. Soc.
  (3) 14 (1964), 714–718.
* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

/-- A finitely generated `A[X]`-module `P` that becomes free over `A⟨X⟩` contains a monic
lattice: an injective `F : A[X]ⁿ → P` whose image contains `s • P` for a monic `s`. The lattice
vectors are the numerators of a basis of `A⟨X⟩ ⊗[A[X]] P` over a common monic denominator. -/
theorem exists_lattice_of_free [Nontrivial A] (P : Type v) [AddCommGroup P] [Module A[X] P]
    [Module.Finite A[X] P]
    (h : Module.Free (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid A) ⊗[A[X]] P)) :
    ∃ (n : ℕ) (F : (Fin n → A[X]) →ₗ[A[X]] P) (s : A[X]), Function.Injective F ∧ s.Monic ∧
      ∀ p, s • p ∈ LinearMap.range F := by
  classical
  set S := monicSubmonoid A
  set L := Localization S
  let μ := TensorProduct.mk A[X] L P 1
  have hinjL : Function.Injective (algebraMap A[X] L) :=
    IsLocalization.injective L monicSubmonoid_le_nonZeroDivisors
  have : Nontrivial L := hinjL.nontrivial
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) L (L ⊗[A[X]] P)) :=
    ⟨_, ⟨Module.finBasis L _⟩⟩
  obtain ⟨σ, hσ⟩ := IsLocalizedModule.exist_integer_multiples S μ Finset.univ b
  choose y hy using fun i => hσ i (Finset.mem_univ i)
  have hli : ∀ g : Fin n → L, ∑ i, g i • b i = 0 → ∀ i, g i = 0 := by
    intro g hg i
    have := congrArg (fun x => b.repr x i) hg
    simpa [map_sum, Finsupp.single_apply] using this
  let F := Fintype.linearCombination A[X] y
  have hμF : ∀ c, μ (F c) = ∑ i, algebraMap A[X] L (c i * σ) • b i := by
    intro c
    simp only [F, Fintype.linearCombination_apply, map_sum, map_smul, hy, smul_smul,
      algebraMap_smul]
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∑ i, algebraMap A[X] L (c i * σ) • b i = 0 := by rw [← hμF, hc, map_zero]
    funext i
    have := hli (fun i => algebraMap A[X] L (c i * σ)) h0 i
    rw [← map_zero (algebraMap A[X] L)] at this
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (monicSubmonoid_le_nonZeroDivisors σ.2)).mp (hinjL this)
  have hpt : ∀ p, ∃ u : S, (u : A[X]) • p ∈ LinearMap.range F := by
    intro p
    obtain ⟨τ, hτ⟩ := IsLocalization.exist_integer_multiples S Finset.univ (b.repr (μ p))
    choose β hβ using fun i => hτ i (Finset.mem_univ i)
    have heq : μ (((τ : A[X]) * σ) • p) = μ (F β) := by
      rw [hμF, map_smul, ← b.sum_repr (μ p), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul L, smul_smul, map_mul, map_mul, hβ, Algebra.smul_def]
      congr 1
      ring
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := S) heq
    refine ⟨u * τ * σ, (u : A[X]) • β, ?_⟩
    rw [map_smul, ← Submonoid.smul_def, ← hu, Submonoid.smul_def, smul_smul, Submonoid.coe_mul,
      Submonoid.coe_mul, ← mul_assoc]
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := A[X]) (M := P)
  choose u hu using fun j => hpt (g j)
  refine ⟨n, F, ∏ j, (u j : A[X]), hinj, monic_prod_of_monic _ _ fun j _ => (u j).2, ?_⟩
  intro p
  have hle : Submodule.span A[X] (Set.range g) ≤
      (LinearMap.range F).comap ((∏ j, (u j : A[X])) • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun i => (u i : A[X])) (Finset.mem_univ j)
    change (∏ j, (u j : A[X])) • g j ∈ LinearMap.range F
    rw [hd, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ _ (hu j)
  exact hle (hg ▸ Submodule.mem_top)

/-- **4.2.** Local Horrocks: over a local ring `A`, a finitely generated projective `A[X]`-module
that becomes free over `A⟨X⟩` is free (Lombardi–Quitté, Theorem XVI.4.3). -/
theorem free_of_free_monicLocalization_of_isLocalRing [IsLocalRing A] (P : Type v)
    [AddCommGroup P] [Module A[X] P] [Module.Finite A[X] P] [Module.Projective A[X] P]
    (h : Module.Free (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid A) ⊗[A[X]] P)) :
    Module.Free A[X] P := by
  obtain ⟨n, F, s, hF, hs, hsF⟩ := exists_lattice_of_free P h
  exact free_of_lattice n F s hF hs hsF

end LeanPool.QuillenSuslin
