/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialRays
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.CCDN.Hilbert.FunctionFieldRank
import LeanPool.CCDN.Hilbert.StandardMonomials
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Eventual linearity from a linear Hilbert bound

The standard monomial set eventually consists of finitely many disjoint rays.
Its sufficiently high degree shells therefore have constant cardinality.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- Full coordinate rays with uniquely normalized base points. -/
private def fullExponentRays {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Set (σ →₀ ℕ)) (B : ℕ) :=
  {p : σ × (σ → Fin B) // (p.2 p.1).val = 0 ∧
    ∀ n, exponentRay B p.1 p.2 n ∈ S}

private lemma exponentRay_degree {σ : Type*} [Fintype σ] [DecidableEq σ]
    (B : ℕ) (j : σ) (b : σ → Fin B) (n : ℕ) (hb : (b j).val = 0) :
    Finsupp.degree (exponentRay B j b n) = n + ∑ k, (b k).val := by
  have h := Finsupp.sum_update_add
    (Finsupp.equivFunOnFinite.symm (fun k => (b k).val)) j n
    (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
  change (exponentRay B j b n).sum (fun _ v => v) = _
  simpa [exponentRay, Finsupp.sum_fintype, hb, add_comm] using h

private lemma rayBase_weight_le {σ : Type*} [Fintype σ] {B : ℕ} (b : σ → Fin B) :
    (∑ k, (b k).val) ≤ Fintype.card σ * B := by
  calc
    _ ≤ ∑ _ : σ, B := Finset.sum_le_sum (fun k _ => (b k).isLt.le)
    _ = _ := by simp [Nat.mul_comm]

/-- A lower monomial set confined to coordinate rays has eventually constant
shell cardinalities. -/
private theorem lowerSet_shell_card_eventually_constant {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Set (σ →₀ ℕ)) (hS : IsLowerSet S) (B : ℕ) (hB : 0 < B)
    (hunique : ∀ a ∈ S, ∀ i j, B ≤ a i → B ≤ a j → i = j) :
    ∃ N, ∀ n ≥ N,
      Nat.card {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} =
        Nat.card (fullExponentRays S B) := by
  classical
  obtain ⟨M, hMB, hM⟩ := lowerSet_rays_eventually_full S hS B
  refine ⟨M + Fintype.card σ * B, ?_⟩
  intro n hn
  have hweight (b : σ → Fin B) : (∑ k, (b k).val) ≤ n := by
    have := rayBase_weight_le b
    omega
  have htail (b : σ → Fin B) : M ≤ n - ∑ k, (b k).val := by
    have := rayBase_weight_le b
    omega
  let φ : fullExponentRays S B → {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = n} :=
    fun p => ⟨exponentRay B p.val.1 p.val.2 (n - ∑ k, (p.val.2 k).val),
      p.property.2 _, by
        rw [exponentRay_degree B _ _ _ p.property.1]
        exact Nat.sub_add_cancel (hweight p.val.2)⟩
  have hinj : Function.Injective φ := by
    intro p q he
    have he' := congrArg Subtype.val he
    have hj : p.val.1 = q.val.1 := by
      by_contra hj
      have hh := congrArg (fun a : σ →₀ ℕ => a p.val.1) he'
      change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
      simp [hj] at hh
      have := htail p.val.2
      have := (q.val.2 p.val.1).isLt
      omega
    apply Subtype.ext
    apply Prod.ext hj
    funext k
    apply Fin.ext
    by_cases hk : k = p.val.1
    · subst k
      rw [p.property.1, hj, q.property.1]
    · have hkq : k ≠ q.val.1 := by simpa [hj] using hk
      have hh := congrArg (fun a : σ →₀ ℕ => a k) he'
      change exponentRay _ _ _ _ _ = exponentRay _ _ _ _ _ at hh
      simpa [hk, hkq] using hh
  have hsurj : Function.Surjective φ := by
    intro a
    have hex : ∃ j, B ≤ a.val j := by
      by_contra h
      push Not at h
      have hs : Finsupp.degree a.val ≤ Fintype.card σ * B := by
        rw [Finsupp.degree_eq_sum]
        exact (Finset.sum_le_sum (fun k _ => (h k).le)).trans_eq (by simp [Nat.mul_comm])
      rw [a.property.2] at hs
      omega
    obtain ⟨j, hj⟩ := hex
    have hsmall (k : σ) (hk : k ≠ j) : a.val k < B := by
      by_contra h
      have he := hunique a.val a.property.1 k j (by omega) hj
      exact hk he
    let b : σ → Fin B := fun k => if hk : k = j then ⟨0, hB⟩ else ⟨a.val k, hsmall k hk⟩
    have hbj : (b j).val = 0 := by simp [b]
    have heq : exponentRay B j b (a.val j) = a.val := by
      ext k
      simp only [exponentRay_apply]
      by_cases hk : k = j <;> simp [hk, b]
    have hdegree : a.val j + ∑ k, (b k).val = n := by
      rw [← exponentRay_degree B j b _ hbj, heq]
      exact a.property.2
    have hjM : M ≤ a.val j := by
      have := rayBase_weight_le b
      omega
    have hfull : ∀ k, exponentRay B j b k ∈ S :=
      (hM j b (a.val j) hjM).mp (heq.symm ▸ a.property.1)
    refine ⟨⟨(j, b), hbj, hfull⟩, ?_⟩
    apply Subtype.ext
    change exponentRay B j b (n - ∑ k, (b k).val) = a.val
    have ht : n - ∑ k, (b k).val = a.val j := by omega
    rw [ht, heq]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

/-- Splitting off the top degree shell gives the Hilbert-function increment. -/
private theorem standard_card_succ {K σ : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I (N + 1)) =
      Module.finrank K (filteredCoordinateSpace I N) +
      Nat.card {a : σ →₀ ℕ // a ∈ Ideal.standardExponents I MonomialOrder.degLex ∧
        Finsupp.degree a = N + 1} := by
  classical
  let := Fintype.ofFinite σ
  let S := Ideal.standardExponents I MonomialOrder.degLex
  let A := Ideal.boundedStandardExponents I MonomialOrder.degLex (N + 1)
  let B := Ideal.boundedStandardExponents I MonomialOrder.degLex N
  let E := {a : σ →₀ ℕ // a ∈ S ∧ Finsupp.degree a = N + 1}
  let φ : A → B ⊕ E := fun a =>
    if h : Finsupp.degree a.val ≤ N then Sum.inl ⟨a.val, a.property.1, h⟩
    else Sum.inr ⟨a.val, a.property.1, by
      have ha : Finsupp.degree a.val ≤ N + 1 := a.property.2
      omega⟩
  let ψ : B ⊕ E → A := fun p => match p with
    | .inl b => ⟨b.val, b.property.1, le_trans b.property.2 (by omega)⟩
    | .inr e => ⟨e.val, e.property.1, le_of_eq e.property.2⟩
  have hleft : Function.LeftInverse ψ φ := by
    intro a
    dsimp [φ]
    split_ifs <;> rfl
  have hright : Function.RightInverse ψ φ := by
    intro p
    rcases p with b | e
    · have hb : Finsupp.degree b.val ≤ N := b.property.2
      dsimp only [ψ, φ]
      rw [dite_eq_left hb]
    · have hn : ¬ Finsupp.degree e.val ≤ N := by rw [e.property.2]; omega
      dsimp only [ψ, φ]
      rw [dite_eq_right hn]
  let equiv : A ≃ B ⊕ E := ⟨φ, ψ, hleft, hright⟩
  let : Finite E := Finite.of_injective (fun e : E => ψ (Sum.inr e))
    (fun a b h => Sum.inr.inj ((Function.RightInverse.injective hright) h))
  rw [filteredCoordinateSpace_finrank_eq_standard_card,
    filteredCoordinateSpace_finrank_eq_standard_card]
  exact (Nat.card_congr equiv).trans Nat.card_sum

/-- Any linear upper bound on a filtered coordinate ring implies an eventually
affine Hilbert function, with natural slope at most that upper-bound slope. -/
theorem filteredCoordinateSpace_eventually_linear {K σ : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (C : ℕ)
    (hbound : ∀ N ≥ 14, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d ≤ C, HasFilteredCurveDegree I d := by
  classical
  let := Fintype.ofFinite σ
  let B := 2 * C + 14
  obtain ⟨N, hN⟩ := lowerSet_shell_card_eventually_constant
    (Ideal.standardExponents I MonomialOrder.degLex)
    (Ideal.isLowerSet_standardExponents I MonomialOrder.degLex)
    B (by dsimp [B]; omega)
    (fun a ha i j hi hj => standard_at_most_one_large I C hbound ha hi hj)
  let d := Nat.card (fullExponentRays (Ideal.standardExponents I MonomialOrder.degLex) B)
  have hstep (n : ℕ) (hn : N ≤ n) :
      Module.finrank K (filteredCoordinateSpace I (n + 1)) =
        Module.finrank K (filteredCoordinateSpace I n) + d := by
    rw [standard_card_succ, hN (n + 1) (by omega)]
  have hformula (k : ℕ) : Module.finrank K (filteredCoordinateSpace I (N + k)) =
      Module.finrank K (filteredCoordinateSpace I N) + d * k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, hstep (N + k) (by omega), hk]
      ring
  have hd : d ≤ C := by
    by_contra h
    have hbig := hbound (N + (C * (N + 16) + 14)) (by omega)
    rw [hformula] at hbig
    have hdc : C + 1 ≤ d := by omega
    have hm := Nat.mul_le_mul_right (C * (N + 16) + 14) hdc
    nlinarith
  refine ⟨d, hd, N, (Module.finrank K (filteredCoordinateSpace I N) : ℤ) - d * N, ?_⟩
  intro n hn
  have he := hformula (n - N)
  rw [Nat.add_sub_of_le hn] at he
  rw [he]
  push_cast
  rw [Nat.cast_sub hn]
  ring

/-- A transcendental coordinate contributes all of its powers to the filtration. -/
theorem transcendental_coordinate_filtered_lower {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) {j : σ}
    (hj : Transcendental K ((Ideal.Quotient.mk I) (MvPolynomial.X j))) (N : ℕ) :
    N + 1 ≤ Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let := Fintype.ofFinite σ
  have hlin := transcendental_powers_independent
    ((Ideal.Quotient.mk I) (MvPolynomial.X j)) hj (N + 1)
  have hmem (k : Fin (N + 1)) :
      ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val ∈ filteredCoordinateSpace I N := by
    apply Submodule.mem_map.mpr
    refine ⟨MvPolynomial.X j ^ k.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree_X_pow]
    omega
  let v : Fin (N + 1) → filteredCoordinateSpace I N :=
    fun k => ⟨((Ideal.Quotient.mk I) (MvPolynomial.X j)) ^ k.val, hmem k⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace I N).subtype hlin
  simpa using hv.fintype_card_le_finrank

end
end CCDN
