/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs2
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.Real.Cardinality

/-!
# Tie-breakers exist

Graph Minors XIX, Section 8 (pages 346–347), takes a tie-breaker in a painting as given. A real
vector
space over the rationals has infinite dimension, so finitely many positive rationally independent
reals
exist, and we can shrink the weights of the edges outside `Σ` by a rational factor.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u

/-- Finitely many positive reals that are rationally independent. -/
theorem exists_independent (ι : Type*) [Finite ι] :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ LinearIndependent ℚ x := by
  classical
  let := Fintype.ofFinite ι
  have hrank : ((Fintype.card ι : ℕ) : Cardinal) ≤ Module.rank ℚ ℝ := by
    have hnf : ¬ Module.Finite ℚ ℝ := fun _ ↦ by
      have h : Countable ℝ := Countable.of_moduleFinite (R := ℚ) (M := ℝ)
      exact not_countable (α := ℝ) h
    have h₀ : Cardinal.aleph0 ≤ Module.rank ℚ ℝ := not_lt.1 fun h ↦
      hnf (Module.rank_lt_aleph0_iff.1 h)
    exact (Cardinal.natCast_lt_aleph0).le.trans h₀
  obtain ⟨s, hs, hli⟩ := le_rank_iff_exists_linearIndependent_finset.1 hrank
  let e : ι ≃ s := Fintype.equivOfCardEq (by simpa using hs.symm)
  have h₁ : LinearIndependent ℚ fun i ↦ ((e i : s) : ℝ) := hli.comp e e.injective
  have hne : ∀ i, ((e i : s) : ℝ) ≠ 0 := fun i ↦ h₁.ne_zero i
  let u : ι → ℚˣ := fun i ↦ if 0 < ((e i : s) : ℝ) then 1 else -1
  refine ⟨fun i ↦ u i • ((e i : s) : ℝ), fun i ↦ ?_, h₁.units_smul u⟩
  by_cases h : 0 < ((e i : s) : ℝ)
  · simp [u, h]
  · have hneg : ((e i : s) : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 h) (hne i)
    simpa [u, h, Units.smul_def] using hneg

variable {S : Type u} [TopologicalSpace S] {Shat : Type u} [TopologicalSpace Shat]

/-- **A tie-breaker exists** for every radial drawing. -/
theorem nonempty_tieBreaker {cap : IsCappedSurface S Shat} {Γ : Painting S}
    (rad : RadialDrawing cap Γ) : Nonempty (TieBreaker rad) := by
  classical
  have : Fintype rad.G.E := rad.G.finite_edges.fintype
  have : Fintype Γ.V := Γ.finite_V.fintype
  obtain ⟨x, hpos, hli⟩ := exists_independent (rad.G.E ⊕ Γ.V)
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℚ, 0 < q ∧ ∀ i j, (q : ℝ) * x i < x j := by
    by_cases hne : Nonempty (rad.G.E ⊕ Γ.V)
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min x
      obtain ⟨i₁, hi₁⟩ := Finite.exists_max x
      have h₁ : 0 < x i₀ / (x i₁) := div_pos (hpos _) (hpos _)
      obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn h₁
      refine ⟨q, by exact_mod_cast hq0, fun i j ↦ ?_⟩
      have hq' : (q : ℝ) * x i₁ < x i₀ := (lt_div_iff₀ (hpos _)).1 hq1
      calc (q : ℝ) * x i ≤ q * x i₁ := mul_le_mul_of_nonneg_left (hi₁ i) hq0.le
        _ < x i₀ := hq'
        _ ≤ x j := hi₀ j
    · exact ⟨1, one_pos, fun i ↦ absurd ⟨i⟩ hne⟩
  let c : rad.G.E ⊕ Γ.V → ℚˣ := fun i ↦ match i with
    | Sum.inl e => if Disjoint e.1 (range cap.emb) then Units.mk0 q hq0.ne' else 1
    | Sum.inr _ => 1
  let y : rad.G.E ⊕ Γ.V → ℝ := fun i ↦ c i • x i
  have hy : LinearIndependent ℚ y := hli.units_smul c
  have hcoe : ∀ i, c i • x i = ((c i : ℚˣ) : ℚ) * x i := fun i ↦ by
    rw [Units.smul_def, Rat.smul_def]
  have hypos : ∀ i, 0 < y i := fun i ↦ by
    change 0 < c i • x i
    rw [hcoe]
    refine mul_pos ?_ (hpos i)
    rcases i with e | v
    · by_cases h : Disjoint e.1 (range cap.emb)
      · simpa [c, h] using hq0
      · simp [c, h]
    · simp [c]
  refine ⟨{ wtE := fun e ↦ if h : e ∈ rad.G.E then y (Sum.inl ⟨e, h⟩) else 1
            wtV := fun v ↦ if h : v ∈ Γ.V then y (Sum.inr ⟨v, h⟩) else 1
            wtE_pos := fun e he ↦ by
              rw [dite_eq_left he]
              have := hypos (Sum.inl ⟨e, he⟩)
              exact_mod_cast this
            wtV_pos := fun v hv ↦ by
              rw [dite_eq_left hv]
              have := hypos (Sum.inr ⟨v, hv⟩)
              exact_mod_cast this
            rationally_independent := ?_
            cuff_lt_internal := ?_ }⟩
  · intro α β hsum
    have hE : ∑ᶠ e ∈ rad.G.E, (α e : ℝ) * (if h : e ∈ rad.G.E then y (Sum.inl ⟨e, h⟩) else 1) =
        ∑ e : rad.G.E, (α e.1 : ℝ) * y (Sum.inl e) := by
      rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      simp
    have hV : ∑ᶠ v ∈ Γ.V, (β v : ℝ) * (if h : v ∈ Γ.V then y (Sum.inr ⟨v, h⟩) else 1) =
        ∑ v : Γ.V, (β v.1 : ℝ) * y (Sum.inr v) := by
      rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      simp
    rw [hE, hV] at hsum
    let g : rad.G.E ⊕ Γ.V → ℚ := fun i ↦ match i with
      | Sum.inl e => α e.1
      | Sum.inr v => - β v.1
    have hzero : ∑ i, g i • y i = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [g, Rat.smul_def, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
      linarith
    have hall := Fintype.linearIndependent_iff.1 hy g hzero
    refine ⟨fun e he ↦ hall (Sum.inl ⟨e, he⟩), fun v hv ↦ ?_⟩
    have := hall (Sum.inr ⟨v, hv⟩)
    simpa [g] using this
  · intro e he f hf hd hsub
    have hne : ¬ Disjoint f (range cap.emb) := fun h ↦ by
      obtain ⟨z, hz⟩ := hf.1
      exact disjoint_left.1 h hz (hsub hz)
    simp only [dite_eq_left he, dite_eq_left hf]
    change c (Sum.inl ⟨e, he⟩) • x (Sum.inl ⟨e, he⟩) < c (Sum.inl ⟨f, hf⟩) • x (Sum.inl ⟨f, hf⟩)
    rw [hcoe (Sum.inl ⟨e, he⟩), hcoe (Sum.inl ⟨f, hf⟩)]
    simpa [c, hd, hne] using hq _ _

end GraphMinor.GM19
