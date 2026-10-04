/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.DomainSmooth
public import LeanPool.EllipticPDE.Embedding.HolderGeneral


/-!
# Sobolev embedding at order `k`

For `Ω ⊆ ℝⁿ` open and bounded with `∂Ω` of class `C¹`, `p ∈ [1, ∞)`, `k ∈ ℕ` and
`u ∈ W^{k,p}(Ω)`,

* if `k < n/p` then `u ∈ L^q(Ω)` with `1/q = 1/p - k/n` and `‖u‖_{L^q} ≤ C‖u‖_{W^{k,p}}`;
* if `k > n/p` then `u ∈ C^{k-1-⌊n/p⌋,γ}(closure Ω)` with `γ` any value in `(0,1)` when
  `n/p ∈ ℕ` and `γ = ⌊n/p⌋ - n/p + 1` otherwise, and `‖u‖_{C^{k-1-⌊n/p⌋,γ}} ≤ C‖u‖_{W^{k,p}}`.

This file states both clauses at the exponents the theorem names. Theorem IV.2.3 of the lecture
notes cited below is the form followed here.

## Reading `W^{k,p}` as a family

A member of `W^{k,p}(Ω)` is read here as a family `F : ι → ℝⁿ → ℝ` closed under weak
differentiation, `nxt i k` naming a weak `k`-derivative of `F i`, together with a depth function
`dep` recording how far an index sits above the root. The order `k` of the theorem is the supply
`m`, the uniform bound `M` on the `L^p` seminorms of the members of depth at most `m` is
`‖u‖_{W^{k,p}(Ω)}`, and `D^α u` for `|α| ≤ k` is the member at depth `|α|`. That is the
vocabulary the interior statements of this development already use, and it asks nothing of a
multi-index calculus.

## Two clauses

Clause (i) is `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal`: the strict
rung condition `p k < n` is exactly positivity of the landing reciprocal `1/p - k/n`, and the
ladder lands on the exponent naming it.

Clause (ii) splits in two. When `n/p ∉ ℕ` the rung count is `⌊n/p⌋`, the landing exponent
`P` satisfies `p k < n < p (k+1)`, and Morrey's exponent `1 - n/P` is `⌊n/p⌋ - n/p + 1`; that is
`exists_const_holderOnWith_domain_ideal`. When `n/p ∈ ℕ` the rung count `n/p` sends the landing
reciprocal to zero, the ladder reaches every finite exponent, and the Hölder exponent is free in
`(0,1)`; that is `exists_const_holderOnWith_domain_free`.

## Main declarations

* `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal`: clause (i).
* `EllipticPdes.Embedding.exists_const_holderOnWith_domain_ideal`: clause (ii) at `n/p ∉ ℕ`.
* `EllipticPdes.Embedding.exists_const_holderOnWith_domain_free`: clause (ii) at `n/p ∈ ℕ`.

## References

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem IV.2.3
(pp. 32-33); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary)

variable {d : ℕ}

/-- **Positivity of the landing reciprocal.** The strict rung condition `p₀ s < d`, which is
the condition `k < n/p`, says exactly that `1/p₀ - s/d` is positive. -/
private theorem landing_pos {p₀ : ℝ≥0} (hp₀0 : (0 : ℝ) < (p₀ : ℝ)) (hdpos : (0 : ℝ) < (d : ℝ))
    {s : ℕ} (hsd : (p₀ : ℝ) * s < (d : ℝ)) : 0 < (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := by
  have hmul := mul_lt_mul_of_pos_right hsd (mul_pos (inv_pos.mpr hdpos) (inv_pos.mpr hp₀0))
  have hc1 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by field_simp
  have hc2 : (p₀ : ℝ) * (s : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (s : ℝ) * (d : ℝ)⁻¹ := by field_simp
  rw [hc1, hc2] at hmul
  linarith

/-! ### Clause (i) -/

/-- **Clause (i) of the Sobolev embedding.** Under the strict rung condition `p₀ s < d`,
which is `k < n/p`, every member of depth at most `m - s` lies in `L^q(Ω)` at the exponent
`1/q = 1/p₀ - s/d` the theorem names, with one constant, depending on the domain, the dimension, the
base exponent and the rung count alone, bounding its seminorm by a uniform `L^{p₀}` bound on the
family. -/
theorem exists_const_memLp_of_gradClosed_domain_ideal (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) (s : ℕ)
    (hsd : (p₀ : ℝ) * s < (d : ℝ)) :
    ∃ K : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0∞, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ M) →
      ∀ i, dep i + s ≤ m →
        MemLp (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹)
            (volume.restrict Ω) ∧
          eLpNorm (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹)
            (volume.restrict Ω) ≤ (K : ℝ≥0∞) * M := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  have ht0 : 0 < (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := landing_pos hp₀0 hdpos hsd
  have ht_le : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := by
    have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
    linarith
  have hqcoe : ((Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ : ℝ≥0) : ℝ)
      = ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr ht0.le)
  have hqinv : ((Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ : ℝ≥0) : ℝ)⁻¹
      = (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := by rw [hqcoe, inv_inv]
  have hp₀q : p₀ ≤ Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ := by
    rw [← NNReal.coe_le_coe, hqcoe]
    have := inv_anti₀ ht0 ht_le
    simpa using this
  exact exists_const_memLp_of_gradClosed_domain hd hΩopen hΩb hC1 hp₀ ι s hsd.le hp₀q
    (le_of_eq hqinv.symm)

/-! ### Landing exponents of clause (ii) -/

/-- **Landing exponent when `n/p ∉ ℕ`.** The two rung conditions place the exponent
`1/P = 1/p₀ - s/d` strictly above the dimension, and Morrey's exponent there is the
`⌊n/p⌋ - n/p + 1` the clause names. -/
private theorem exists_landing_ideal (hd0 : 0 < d) {p₀ : ℝ≥0} (hp₀0 : (0 : ℝ) < (p₀ : ℝ))
    (s : ℕ) (hsd : (p₀ : ℝ) * s < (d : ℝ)) (hlt : (d : ℝ) < (p₀ : ℝ) * ((s : ℝ) + 1)) :
    ∃ P : ℝ≥0, p₀ ≤ P ∧ (d : ℝ) < (P : ℝ) ∧
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹ ∧
      morreyExponent d (P : ℝ) = Real.toNNReal ((s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have ht0 : 0 < (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := landing_pos hp₀0 hdpos hsd
  have ht_le : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := by
    have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
    linarith
  set P : ℝ≥0 := Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ with hP_def
  have hPcoe : ((P : ℝ≥0) : ℝ) = ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹ := by
    rw [hP_def]; exact Real.coe_toNNReal _ (inv_nonneg.mpr ht0.le)
  have hPinv : ((P : ℝ≥0) : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ := by rw [hPcoe, inv_inv]
  have hp₀P : p₀ ≤ P := by
    rw [← NNReal.coe_le_coe, hPcoe]
    have := inv_anti₀ ht0 ht_le
    simpa using this
  -- the upper rung condition places the landing exponent above the dimension
  have hPd : (d : ℝ) < (P : ℝ) := by
    have hstrict : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ < (d : ℝ)⁻¹ := by
      have hmul := mul_lt_mul_of_pos_right hlt (mul_pos (inv_pos.mpr hdpos) (inv_pos.mpr hp₀0))
      have hc1 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by field_simp
      have hc2 : (p₀ : ℝ) * ((s : ℝ) + 1) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹)
          = ((s : ℝ) + 1) * (d : ℝ)⁻¹ := by field_simp
      rw [hc1, hc2] at hmul
      have : (s : ℝ) * (d : ℝ)⁻¹ + (d : ℝ)⁻¹ = ((s : ℝ) + 1) * (d : ℝ)⁻¹ := by ring
      linarith
    have hPpos : (0 : ℝ) < (P : ℝ) := by rw [hPcoe]; exact inv_pos.mpr ht0
    have hinv : ((P : ℝ≥0) : ℝ)⁻¹ < (d : ℝ)⁻¹ := by rw [hPinv]; exact hstrict
    by_contra hcon
    have hle : (P : ℝ) ≤ (d : ℝ) := le_of_not_gt hcon
    exact absurd (inv_anti₀ hPpos hle) (not_le.mpr hinv)
  refine ⟨P, hp₀P, hPd, le_of_eq hPinv.symm, ?_⟩
  -- Morrey's exponent at the landing exponent is the one the theorem names
  have hval := morreyExponent_eq_ladder (d := d) (p₀ := p₀) (P := P) (s := s) hd0 hp₀0 hPd.le
    hPinv
  have hnn : (0 : ℝ) ≤ (s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ hp₀0]
    nlinarith
  refine NNReal.coe_injective ?_
  rw [hval, Real.coe_toNNReal _ hnn]

/-- **Landing exponent when `n/p ∈ ℕ`.** The rung count sends the landing reciprocal to zero, so
every finite exponent is admissible, and `d/(1-γ)` is the one whose Morrey exponent is `γ`. -/
private theorem exists_landing_free (hd0 : 0 < d) {p₀ : ℝ≥0} (hp₀0 : (0 : ℝ) < (p₀ : ℝ))
    (s : ℕ) (hsd : (p₀ : ℝ) * s = (d : ℝ)) {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ P : ℝ≥0, p₀ ≤ P ∧ (d : ℝ) < (P : ℝ) ∧
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹ ∧ morreyExponent d (P : ℝ) = γ := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hγ1R : ((γ : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hγ1
  have hγ0R : (0 : ℝ) < ((γ : ℝ≥0) : ℝ) := by exact_mod_cast hγ0
  have hden : (0 : ℝ) < 1 - (γ : ℝ) := by linarith
  set P : ℝ≥0 := Real.toNNReal ((d : ℝ) / (1 - (γ : ℝ))) with hP_def
  have hPcoe : ((P : ℝ≥0) : ℝ) = (d : ℝ) / (1 - (γ : ℝ)) := by
    rw [hP_def, Real.coe_toNNReal _ (by positivity)]
  have hPd : (d : ℝ) < (P : ℝ) := by
    rw [hPcoe, lt_div_iff₀ hden]
    nlinarith
  -- the base exponent is at most the dimension, the rung count being at least one
  have hp₀d : (p₀ : ℝ) ≤ (d : ℝ) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp at hsd; linarith
    · have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      nlinarith
  have hp₀P : p₀ ≤ P := by
    rw [← NNReal.coe_le_coe]
    linarith [hPd, hp₀d]
  have hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹ := by
    have hzero : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ = 0 := by
      field_simp
      linarith [hsd]
    rw [hzero]
    positivity
  refine ⟨P, hp₀P, hPd, hPs, ?_⟩
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hdenne : (1 : ℝ) - (γ : ℝ) ≠ 0 := ne_of_gt hden
  have h1 : (d : ℝ) / ((d : ℝ) / (1 - (γ : ℝ))) = 1 - (γ : ℝ) := by
    field_simp
  refine NNReal.coe_injective ?_
  rw [coe_morreyExponent hPd hd0, hPcoe, h1]
  ring

/-! ### Clause (ii) -/

/-- **Clause (ii) of the Sobolev embedding at `n/p ∉ ℕ`.** The rung count is
`⌊n/p⌋`, which the two hypotheses `p₀ s < d < p₀ (s + 1)` pin down, and the Hölder exponent is
`⌊n/p⌋ - n/p + 1`. One constant bounds the Hölder seminorm on the closure of the domain by a
uniform `L^{p₀}` bound on the family, and the members it applies to are those of depth at most
`m - 1 - s`, which is `k - 1 - ⌊n/p⌋`. The supremum is bounded by the same constant, so the
estimate is on the whole `C^{0,γ}` norm. -/
theorem exists_const_holderOnWith_domain_ideal (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) (s : ℕ)
    (hsd : (p₀ : ℝ) * s < (d : ℝ)) (hlt : (d : ℝ) < (p₀ : ℝ) * ((s : ℝ) + 1)) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict Ω] F i ∧
            (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
            HolderOnWith (C * M) (Real.toNNReal ((s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ)))
              w (closure Ω) := by
  have hd0 : 0 < d := by omega
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  obtain ⟨P, hp₀P, hPd, hPs, hexp⟩ := exists_landing_ideal hd0 hp₀0 s hsd hlt
  obtain ⟨C, hC⟩ := exists_const_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι hp₀
    (P := P) (s := s) hsd.le hp₀P hPd hPs
  rw [hexp] at hC
  exact ⟨C, hC⟩

/-- **Clause (ii) of the Sobolev embedding at `n/p ∈ ℕ`.** The rung count `n/p`
sends the landing reciprocal to zero, so the ladder reaches every finite exponent and the Hölder
exponent may be any value in `(0,1)`. -/
theorem exists_const_holderOnWith_domain_free (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) (s : ℕ)
    (hsd : (p₀ : ℝ) * s = (d : ℝ)) {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict Ω] F i ∧
            (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
            HolderOnWith (C * M) γ w (closure Ω) := by
  have hd0 : 0 < d := by omega
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  obtain ⟨P, hp₀P, hPd, hPs, hexp⟩ := exists_landing_free hd0 hp₀0 s hsd hγ0 hγ1
  obtain ⟨C, hC⟩ := exists_const_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι hp₀
    (P := P) (s := s) (by rw [hsd]) hp₀P hPd hPs
  rw [hexp] at hC
  exact ⟨C, hC⟩

/-! ### Clause (ii) with classical derivatives -/

/-- **Clause (ii) at `n/p ∉ ℕ` as a `C^{k-1-⌊n/p⌋,γ}` statement.** One family of representatives
serves every index at once: bounded and `γ`-Hölder on the closure of the domain under the constant
the clause names, differentiable on the domain with the next members as partial derivatives, and
`n` times continuously differentiable there whenever the supply leaves `n` orders above it. -/
theorem exists_const_contDiffOn_holderOnWith_domain_ideal (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) (s : ℕ)
    (hsd : (p₀ : ℝ) * s < (d : ℝ)) (hlt : (d : ℝ) < (p₀ : ℝ) * ((s : ℝ) + 1)) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ i, dep i + 1 + s ≤ m → v i =ᵐ[volume.restrict Ω] F i) ∧
        (∀ i, dep i + 1 + s ≤ m → ∀ y ∈ closure Ω, ‖v i y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
        (∀ i, dep i + 1 + s ≤ m →
          HolderOnWith (C * M) (Real.toNNReal ((s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ)))
            (v i) (closure Ω)) ∧
        (∀ (n : ℕ) (i : ι), dep i + n + 1 + s ≤ m → ContDiffOn ℝ (n : ℕ) (v i) Ω) ∧
        (∀ i, dep i + 2 + s ≤ m → ∀ y ∈ Ω,
          HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  have hd0 : 0 < d := by omega
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  obtain ⟨P, hp₀P, hPd, hPs, hexp⟩ := exists_landing_ideal hd0 hp₀0 s hsd hlt
  obtain ⟨C, hC⟩ := exists_const_contDiffOn_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι
    hp₀ (P := P) (s := s) hsd.le hp₀P hPd hPs
  rw [hexp] at hC
  exact ⟨C, hC⟩

/-- **Clause (ii) at `n/p ∈ ℕ` as a `C^{k-1-⌊n/p⌋,γ}` statement.** The same family of
representatives, at any Hölder exponent in `(0,1)`. -/
theorem exists_const_contDiffOn_holderOnWith_domain_free (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) (s : ℕ)
    (hsd : (p₀ : ℝ) * s = (d : ℝ)) {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ i, dep i + 1 + s ≤ m → v i =ᵐ[volume.restrict Ω] F i) ∧
        (∀ i, dep i + 1 + s ≤ m → ∀ y ∈ closure Ω, ‖v i y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
        (∀ i, dep i + 1 + s ≤ m → HolderOnWith (C * M) γ (v i) (closure Ω)) ∧
        (∀ (n : ℕ) (i : ι), dep i + n + 1 + s ≤ m → ContDiffOn ℝ (n : ℕ) (v i) Ω) ∧
        (∀ i, dep i + 2 + s ≤ m → ∀ y ∈ Ω,
          HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  have hd0 : 0 < d := by omega
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  obtain ⟨P, hp₀P, hPd, hPs, hexp⟩ := exists_landing_free hd0 hp₀0 s hsd hγ0 hγ1
  obtain ⟨C, hC⟩ := exists_const_contDiffOn_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι
    hp₀ (P := P) (s := s) (by rw [hsd]) hp₀P hPd hPs
  rw [hexp] at hC
  exact ⟨C, hC⟩

end EllipticPdes.Embedding
