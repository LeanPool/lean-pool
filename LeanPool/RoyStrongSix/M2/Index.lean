/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.CM.Unmixedness
public import LeanPool.RoyStrongSix.M2.Dims
public import LeanPool.RoyStrongSix.M2.DimsData

/-!
# The connected component of `V × T_Λ` has finite index

* `qspan Λ`: the `ℚ`-span of a lattice `Λ ⊆ ℤ^{d₁}`. `G⁰ = V × T_{lsat (qspan Λ)}` is the connected
  component of `G′ = V × T_Λ`, and it is contained in `G′` (`prodSet_sat_subset`).
* `exists_nsmul_mem`: every element of `lsat (qspan Λ)` has a positive multiple in `Λ`.
* **`finite_cosets`**: `G′` is covered by finitely many cosets `a·G⁰` with `a ∈ G′`. Generators of
  `lsat (qspan Λ)` have a common multiple `N` landing in `Λ`, so the characters take values in the
  finite
  set of `N`-th roots of unity.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

/-- The `ℚ`-span of a lattice. -/
def qspan (Λ : AddSubgroup (Fin d1 → ℤ)) : Submodule ℚ (Fin d1 → ℚ) :=
  Submodule.span ℚ ((fun m : Fin d1 → ℤ => fun j => (m j : ℚ)) '' (Λ : Set (Fin d1 → ℤ)))

theorem le_lsat_qspan (Λ : AddSubgroup (Fin d1 → ℤ)) : Λ ≤ lsat (qspan Λ) :=
  fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩

omit [CharZero K] in
theorem prodSet_antitone (V : Submodule K (Fin d0 → K)) {Λ Λ' : AddSubgroup (Fin d1 → ℤ)}
    (h : Λ ≤ Λ') : prodSet V Λ' ⊆ prodSet V Λ :=
  fun _ hg => ⟨hg.1, fun l hl => hg.2 l (h hl)⟩

omit [CharZero K] in
theorem prodSet_sat_subset (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    prodSet V (lsat (qspan Λ)) ⊆ prodSet V Λ := prodSet_antitone V (le_lsat_qspan Λ)

omit [CharZero K] in
theorem chr_zsmul (y : Fin d1 → Kˣ) (c : ℤ) (l : Fin d1 → ℤ) : chr y (c • l) = chr y l ^ c := by
  simp only [chr, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm, zpow_mul]

omit [CharZero K] in
theorem chr_inv (y : Fin d1 → Kˣ) (l : Fin d1 → ℤ) : chr y⁻¹ l = (chr y l)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← chr_mul, inv_mul_cancel]
  simp [chr]

theorem exists_nsmul_mem {Λ : AddSubgroup (Fin d1 → ℤ)} {l : Fin d1 → ℤ}
    (hl : l ∈ lsat (qspan Λ)) : ∃ N : ℕ, 0 < N ∧ (N : ℤ) • l ∈ Λ := by
  classical
  have hl' : (fun j => (l j : ℚ)) ∈ Submodule.span ℚ
      ((fun m : Fin d1 → ℤ => fun j => (m j : ℚ)) '' (Λ : Set (Fin d1 → ℤ))) := hl
  rw [Finsupp.mem_span_image_iff_linearCombination] at hl'
  obtain ⟨f, hfs, hf⟩ := hl'
  let N : ℕ := ∏ μ ∈ f.support, (f μ).den
  have hden : ∀ μ, (f μ).den ∣ N ∨ μ ∉ f.support := fun μ => by
    by_cases h : μ ∈ f.support
    · exact Or.inl (Finset.dvd_prod_of_mem _ h)
    · exact Or.inr h
  refine ⟨N, Finset.prod_pos fun μ _ => (f μ).den_pos, ?_⟩
  let c : (Fin d1 → ℤ) → ℤ := fun μ => (f μ).num * ((N / (f μ).den : ℕ) : ℤ)
  have hc : ∀ μ ∈ f.support, (c μ : ℚ) = N * f μ := by
    intro μ hμ
    have hd : (f μ).den ∣ N := Finset.dvd_prod_of_mem _ hμ
    simp only [c, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hd (by exact_mod_cast (f μ).den_nz)]
    nth_rewrite 3 [← Rat.num_div_den (f μ)]
    field_simp
  have heq : (N : ℤ) • l = ∑ μ ∈ f.support, c μ • μ := by
    funext j
    have := congrFun hf j
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply] at this
    apply Int.cast_injective (α := ℚ)
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.sum_apply,
      Int.cast_sum]
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [hc μ hμ]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact AddSubgroup.sum_mem _ fun μ hμ =>
    AddSubgroup.zsmul_mem _ ((Finsupp.mem_supported ℚ f).mp hfs hμ) _

omit [CharZero K] in
/-- **`G′` is a finite union of cosets of its connected component.** -/
theorem finite_cosets (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) :
    ∃ R : Finset (GPt K d0 d1), (∀ a ∈ R, a ∈ prodSet V Λ) ∧
      prodSet V Λ ⊆ ⋃ a ∈ R, gtransl a (prodSet V (lsat (qspan Λ))) := by
  classical
  -- generators of the saturated lattice
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (lsat (qspan Λ)).toIntSubmodule)
  have hsmem : ∀ μ ∈ s, μ ∈ lsat (qspan Λ) := fun μ hμ => by
    have : μ ∈ (lsat (qspan Λ)).toIntSubmodule := hs ▸ Submodule.subset_span hμ
    exact this
  choose! Nμ hNpos hNmem using fun μ hμ => exists_nsmul_mem (hsmem μ hμ)
  let N : ℕ := ∏ μ ∈ s, Nμ μ
  have hNpos' : 0 < N := Finset.prod_pos fun μ hμ => hNpos μ hμ
  -- the characters on generators are `N`-th roots of unity
  have hroot : ∀ g ∈ prodSet V Λ, ∀ μ ∈ s, chr g.2 μ ^ N = 1 := by
    intro g hg μ hμ
    have hdvd : Nμ μ ∣ N := Finset.dvd_prod_of_mem _ hμ
    obtain ⟨k, hk⟩ := hdvd
    rw [← zpow_natCast, ← chr_zsmul, hk, Nat.cast_mul, mul_comm, mul_smul]
    exact hg.2 _ (AddSubgroup.zsmul_mem _ (hNmem μ hμ) _)
  let ψ : GPt K d0 d1 → (s → K) := fun g μ => chr g.2 μ.1
  have hfin : (ψ '' prodSet V Λ).Finite := by
    apply Set.Finite.subset (Set.Finite.pi (t := fun _ : s => ((Polynomial.nthRootsFinset N (1 :
      K)) : Set K))
      fun _ => Finset.finite_toSet _)
    rintro _ ⟨g, hg, rfl⟩ μ _
    simp only [Finset.mem_coe, Polynomial.mem_nthRootsFinset hNpos', ψ]
    exact hroot g hg μ.1 μ.2
  have hrep : ∀ v ∈ ψ '' prodSet V Λ, ∃ a ∈ prodSet V Λ, ψ a = v := fun v hv => hv
  choose! rep hrepG hrepψ using hrep
  refine ⟨hfin.toFinset.image rep, fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact hrepG v ((Set.Finite.mem_toFinset _).mp hv)
  · have hv : ψ g ∈ ψ '' prodSet V Λ := ⟨g, hg, rfl⟩
    set a := rep (ψ g)
    have ha : a ∈ prodSet V Λ := hrepG _ hv
    have haψ : ψ a = ψ g := hrepψ _ hv
    simp only [Set.mem_iUnion]
    refine ⟨a, Finset.mem_image.mpr ⟨ψ g, (Set.Finite.mem_toFinset _).mpr hv, rfl⟩,
      gmul (ginv a) g, ⟨?_, ?_⟩, ?_⟩
    · simp only [gmul, ginv]
      exact V.add_mem (V.neg_mem ha.1) hg.1
    · intro l hl
      have hl' : l ∈ (lsat (qspan Λ)).toIntSubmodule := hl
      rw [← hs] at hl'
      clear hl
      simp only [gmul, ginv]
      induction hl' using Submodule.span_induction with
      | mem x hx =>
        rw [chr_mul, chr_inv]
        have := congrFun haψ ⟨x, hx⟩
        simp only [ψ] at this
        rw [this, inv_mul_cancel₀ (chr_ne_zero _ _)]
      | zero => simp [chr]
      | add x y _ _ hx hy => rw [chr_add, hx, hy, one_mul]
      | smul c x _ hx => rw [chr_zsmul, hx, one_zpow]
    · rw [← gmul_assoc, gmul_ginv', gzero_gmul]

end StrongSix.M2

end LeanPool
