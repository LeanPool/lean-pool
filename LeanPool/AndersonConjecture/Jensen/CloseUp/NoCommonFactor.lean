/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.Jensen.NSubring
public import Mathlib.RingTheory.AdicCompletion.Basic
import LeanPool.AndersonConjecture.Jensen.Adjoin.Transcendental
import LeanPool.AndersonConjecture.Jensen.Avoidance
import LeanPool.AndersonConjecture.Jensen.CloseUp.Base
import LeanPool.AndersonConjecture.Jensen.CloseUp.TwoGen
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Close-up: no common factor

Sub-case of the well-founded close-up induction where no prime
of R divides all generators simultaneously. The key observation
is that the ideal of the generators s' cannot be contained in
any associated prime of height at most one, so the avoidance
step applies directly.
-/

@[expose] public section

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

-- Helper: a prime P of height ≤ 1 with P ∩ R ≠ ⊥ lies in Ass(T/r₀T) for some nonzero r₀ ∈ R.
include T in
theorem prime_height_le_one_mem_assoc
    {R : NSubring T}
    (P : Ideal T) (hP_prime : P.IsPrime) (hP_ht : P.height ≤ 1)
    (hPR_ne : P.comap R.carrier.subtype ≠ ⊥) :
    ∃ (r₀ : R.carrier), (r₀ : T) ≠ 0 ∧
      P ∈ associatedPrimes T (T ⧸ span {(r₀ : T)}) := by
  obtain ⟨r₀, hr₀_mem, hr₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPR_ne
  have hr₀T_ne : (r₀ : T) ≠ 0 := fun h => hr₀_ne (Subtype.val_injective h)
  have hr₀_in_P : (r₀ : T) ∈ P := Ideal.mem_comap.mp hr₀_mem
  have hP_minimal : P ∈ (Ideal.span {(r₀ : T)}).minimalPrimes := by
    refine ⟨⟨hP_prime, Ideal.span_le.mpr
      (Set.singleton_subset_iff.mpr hr₀_in_P)⟩, ?_⟩
    intro Q ⟨hQ_prime, hQ_le_span⟩ hQ_le_P
    have hQ_ne_bot : Q ≠ ⊥ := fun h => hr₀T_ne
      (Ideal.span_singleton_eq_bot.mp (bot_unique (hQ_le_span.trans_eq h)))
    exact (@eq_of_prime_le_prime_height_le_one T _ _ Q P hQ_prime hP_prime
      hQ_le_P hQ_ne_bot hP_ht).ge
  have hP_assoc : P ∈ associatedPrimes T (T ⧸ Ideal.span {(r₀ : T)}) := by
    open Module.associatedPrimes in
    have hsub :=
      minimalPrimes_annihilator_subset_associatedPrimes
        T (T ⧸ Ideal.span {(r₀ : T)})
    rw [Ideal.annihilator_quotient] at hsub
    exact hsub hP_minimal
  exact ⟨r₀, hr₀T_ne, hP_assoc⟩

-- Helper: I_s' ⊄ P for associated primes P when no common prime divides s'.
include T in
theorem no_common_I_not_le_assoc
    {R : NSubring T}
    [DecidableEq R.carrier]
    {a : R.carrier} {s : Finset R.carrier}
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hno_common_prime : ∀ (p : R.carrier), Prime p → ¬(∀ x ∈ s', p ∣ x))
    (_hI_s'_bot : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) ≠ ⊥)
    (r : R.carrier) (hr_ne : (r : T) ≠ 0)
    (P : Ideal T) (hP_mem : P ∈ associatedPrimes T (T ⧸ span {(r : T)}))
    (hle : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) ≤ P) :
    False := by
  have hgens_in_P : ∀ x ∈ s', (x : T) ∈ P := fun x hx =>
    hle (Ideal.mem_map_of_mem _ (Ideal.subset_span (Finset.mem_coe.mpr hx)))
  have hht_comap := R.height_bound (r : T) hr_ne P hP_mem
  by_cases hcomap : P.comap R.carrier.subtype = ⊥
  · have hall_zero : ∀ x ∈ s', x = (0 : R.carrier) := by
      intro x hx
      have h1 : x ∈ P.comap R.carrier.subtype :=
        Ideal.mem_comap.mpr (hgens_in_P x hx)
      simpa only [hcomap, Ideal.mem_bot] using h1
    have h_le_one : s'.card ≤ 1 :=
      Finset.card_le_one.mpr fun x hx y hy => by
        rw [hall_zero x hx, hall_zero y hy]
    rw [hs'_def, Finset.card_erase_of_mem ha_mem, hs_eq] at h_le_one
    omega
  · have : (P.comap R.carrier.subtype).IsPrime :=
      hP_mem.isPrime.comap R.carrier.subtype
    obtain ⟨q, hq_prime, hq_Q⟩ :=
      exists_prime_mem_of_ne_bot_closeup (P.comap R.carrier.subtype) hcomap
    have hspan_le : Ideal.span {q} ≤ P.comap R.carrier.subtype :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq_Q)
    have hspan_prime : (Ideal.span {q}).IsPrime :=
      (Ideal.span_singleton_prime hq_prime.ne_zero).mpr hq_prime
    have hspan_ne_bot : Ideal.span {q} ≠ ⊥ :=
      mt (Ideal.span_singleton_eq_bot (α := R.carrier)).mp hq_prime.ne_zero
    have hQ_eq : Ideal.span {q} = P.comap R.carrier.subtype :=
      @eq_of_prime_le_prime_height_le_one R.carrier _
        (NSubring.isDomain R) _ _
        hspan_prime (hP_mem.isPrime.comap R.carrier.subtype)
        hspan_le hspan_ne_bot hht_comap
    have hdvd_all : ∀ x ∈ s', q ∣ x := fun x hx => by
      have hx_Q : x ∈ P.comap R.carrier.subtype := hgens_in_P x hx
      rw [← hQ_eq] at hx_Q
      exact (Ideal.mem_span_singleton (α := R.carrier)).mp hx_Q
    exact hno_common_prime q hq_prime hdvd_all

/-- The shifted root set `{x - t | f(x) = 0}` of a nonzero polynomial over `R` is
countable. -/
private theorem shifted_aeval_roots_countable (R : NSubring T) (t : T)
    (f : Polynomial R.carrier) (hf : f ≠ 0) :
    ((fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}).Countable := by
  apply Set.Countable.image
  have hmap_ne : Polynomial.map R.carrier.subtype f ≠ 0 := by
    rw [Ne, ← Polynomial.map_zero R.carrier.subtype]
    exact (Polynomial.map_injective R.carrier.subtype
      Subtype.val_injective).ne hf
  have h_eq : {x : T | Polynomial.aeval x f = 0} =
      {x : T | (Polynomial.map R.carrier.subtype f).IsRoot x} := by
    ext x
    simp [Polynomial.IsRoot, Polynomial.aeval_def,
      Polynomial.eval_map,
      show algebraMap R.carrier T = R.carrier.subtype from rfl]
  rw [h_eq]
  exact (Polynomial.finite_setOfPred_isRoot hmap_ne).countable

/-- For infinite `R`, there are at most `|R|` associated primes of principal ideals
generated by nonzero elements of `R` (together with `⊥`). -/
private theorem card_assoc_primes_union_bot_le (R : NSubring T)
    (hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier) :
    Cardinal.mk ↑((⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
      associatedPrimes T (T ⧸ span {(r : T)})) ∪ ({⊥} : Set (Ideal T))) ≤
      Cardinal.mk R.carrier := by
  calc _
      ≤ Cardinal.mk ↑(⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
          associatedPrimes T (T ⧸ span {(r : T)})) +
        Cardinal.mk ↑({⊥} : Set (Ideal T)) := Cardinal.mk_union_le _ _
    _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 +
        Cardinal.mk R.carrier := by
        gcongr
        · exact (Cardinal.mk_iUnion_le _).trans
            (mul_le_mul_right (ciSup_le' fun r =>
              Cardinal.mk_le_aleph0_iff.mpr
                ((Set.Finite.subset (associatedPrimes.finite T _)
                  (Set.iUnion_subset fun _ =>
                    le_refl _)).countable.to_subtype)) _)
        · exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
            Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
    _ = Cardinal.mk R.carrier := by
        rw [Cardinal.mul_aleph0_eq hR_inf, Cardinal.add_eq_left hR_inf le_rfl]

/-- For infinite `R`, the set of shifted roots of nonzero polynomials over `R`
(together with `-t`) has cardinality at most `|R|`. -/
private theorem card_shifted_roots_le (R : NSubring T) (t : T)
    (hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier) :
    Cardinal.mk ↑(({-t} : Set T) ∪ ⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
      (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}) ≤ Cardinal.mk R.carrier := by
  calc _
      ≤ Cardinal.mk ↑({-t} : Set T) +
        Cardinal.mk ↑(⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
          (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}) :=
        Cardinal.mk_union_le _ _
    _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier := by
        gcongr
        · exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
            Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
        · exact (Cardinal.mk_iUnion_le _).trans ((mul_le_mul'
            (Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf))
            (ciSup_le' fun f => Cardinal.mk_le_aleph0_iff.mpr (by
              by_cases hf : f = 0
              · exact Set.Countable.to_subtype (by simp [hf])
              · exact (Set.countable_iUnion fun _ =>
                  shifted_aeval_roots_countable R t f hf).to_subtype))).trans
            (Cardinal.mul_aleph0_eq hR_inf).le)
    _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl

/-- For infinite `R`, the set of lifted, shifted roots of the reductions of
polynomials over `R` modulo the associated primes in `C_main` has cardinality at
most `|R|`. -/
private theorem card_mod_roots_le (R : NSubring T) (t : T)
    (φ : (P : Ideal T) → R.carrier →+* T ⧸ P) (liftQ : (P : Ideal T) → T ⧸ P → T)
    (C_main : Set (Ideal T))
    (hC_main : C_main = ⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
      associatedPrimes T (T ⧸ span {(r : T)}))
    (hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier) :
    Cardinal.mk ↑(⋃ (P : Ideal T) (_ : P ∈ C_main) (f : Polynomial R.carrier)
        (_ : f.map (φ P) ≠ 0),
        (fun α => liftQ P α - t) '' { α : T ⧸ P | (f.map (φ P)).IsRoot α }) ≤
      Cardinal.mk R.carrier := by
  have hCmain_le : Cardinal.mk C_main ≤ Cardinal.mk R.carrier := by
    rw [hC_main]
    calc _
        ≤ Cardinal.mk R.carrier *
            ⨆ (r : R.carrier), Cardinal.mk ↑(⋃ (_ : (r : T) ≠ 0),
              associatedPrimes T (T ⧸ Ideal.span {(r : T)})) :=
            Cardinal.mk_iUnion_le _
      _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
            gcongr
            apply ciSup_le'
            intro r
            apply Cardinal.mk_le_aleph0_iff.mpr
            by_cases hr : (r : T) = 0
            · exact Set.Countable.to_subtype (by simp [hr])
            · exact (Set.Finite.subset (associatedPrimes.finite T _)
                (Set.iUnion_subset fun _ => le_refl _)).countable.to_subtype
      _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
  have h_biUnion :
      Cardinal.mk ↑(⋃ P ∈ C_main,
        ⋃ (f : Polynomial R.carrier),
        ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
          (fun α => liftQ P α - t) ''
            {α | (Polynomial.map (φ P) f).IsRoot α})
        ≤ Cardinal.mk R.carrier := by
    apply (Cardinal.mk_biUnion_le _ _).trans
    have h_inner :
        ∀ (x : ↑C_main),
        Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
        ⋃ (_ : Polynomial.map (φ x.1) f ≠ 0),
          (fun α => liftQ x.1 α - t) ''
            {α | (Polynomial.map (φ x.1) f).IsRoot α}) ≤
        Cardinal.mk R.carrier := by
      intro ⟨P, hP⟩
      calc Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                  (fun α => liftQ P α - t) ''
                    {α | (Polynomial.map (φ P) f).IsRoot α})
            ≤ Cardinal.mk (Polynomial R.carrier) *
                ⨆ (f : Polynomial R.carrier),
                  Cardinal.mk ↑(⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                    (fun α => liftQ P α - t) ''
                      {α | (Polynomial.map (φ P) f).IsRoot α}) :=
                Cardinal.mk_iUnion_le _
          _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                gcongr
                · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
                · apply ciSup_le'
                  intro f
                  apply Cardinal.mk_le_aleph0_iff.mpr
                  by_cases hfne : Polynomial.map (φ P) f = 0
                  · exact Set.Countable.to_subtype (by simp [hfne])
                  · have : P.IsPrime := by
                      rw [hC_main, Set.mem_iUnion] at hP
                      obtain ⟨r, hP'⟩ := hP
                      rw [Set.mem_iUnion] at hP'
                      obtain ⟨_, hPmem⟩ := hP'
                      exact hPmem.isPrime
                    have : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
                    exact (Set.Finite.subset
                      ((Polynomial.rootSet_finite
                        (Polynomial.map (φ P) f)
                        (T ⧸ P)).image
                        (fun α => liftQ P α - t))
                      (Set.iUnion_subset fun _ =>
                        Set.image_mono fun α hα =>
                          Polynomial.mem_rootSet.mpr
                            ⟨hfne, hα⟩)).countable.to_subtype
          _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
    exact (mul_le_mul' hCmain_le (ciSup_le' h_inner)).trans
      (Cardinal.mul_eq_self hR_inf).le
  exact (Cardinal.mk_le_mk_of_subset fun x hx => hx).trans h_biUnion

/-- Cardinality bound needed to apply `avoidance` in the no-common-factor case: either
`C × (D ∪ D_mod)` is smaller than the residue field, or both sets are countable. -/
private theorem no_common_avoidance_bound (R : NSubring T) (t : T)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (φ : (P : Ideal T) → R.carrier →+* T ⧸ P) (liftQ : (P : Ideal T) → T ⧸ P → T)
    (C_main C : Set (Ideal T)) (D D_mod : Set T)
    (hC_main : C_main = ⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
      associatedPrimes T (T ⧸ span {(r : T)}))
    (hC : C = C_main ∪ {⊥})
    (hD : D = {-t} ∪ ⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
      (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0})
    (hD_mod : D_mod = ⋃ (P : Ideal T) (_ : P ∈ C_main) (f : Polynomial R.carrier)
      (_ : f.map (φ P) ≠ 0),
      (fun α => liftQ P α - t) '' { α : T ⧸ P | (f.map (φ P)).IsRoot α }) :
    Cardinal.mk (↑C × ↑(D ∪ D_mod)) < Cardinal.mk (IsLocalRing.ResidueField T) ∨
      (C.Countable ∧ (D ∪ D_mod).Countable) := by
  by_cases hR_le : Cardinal.mk R.carrier ≤ Cardinal.aleph0
  · have : Countable R.carrier := Cardinal.mk_le_aleph0_iff.mp hR_le
    have : Countable (Polynomial R.carrier) := by
      let : Countable (AddMonoidAlgebra R.carrier ℕ) :=
        Countable.of_equiv _ AddMonoidAlgebra.coeffEquiv.symm
      exact Polynomial.toFinsupp_injective.countable
    right
    have hCmain_countable : C_main.Countable := by
      rw [hC_main]
      exact Set.countable_iUnion fun r =>
        Set.countable_iUnion fun _ =>
          (associatedPrimes.finite T (T ⧸ span {(r : T)})).countable
    have hD_countable : D.Countable := by
      rw [hD]
      exact Set.Countable.union (Set.countable_singleton _)
        (Set.countable_iUnion fun f => Set.countable_iUnion fun hf =>
          shifted_aeval_roots_countable R t f hf)
    have hD_mod_countable : D_mod.Countable := by
      rw [hD_mod]
      exact Set.Countable.biUnion hCmain_countable fun P hPC => by
        apply Set.countable_iUnion
        intro f
        apply Set.countable_iUnion
        intro hfne
        apply Set.Finite.countable
        apply Set.Finite.image
        have : P.IsPrime := by
          rw [hC_main, Set.mem_iUnion] at hPC
          obtain ⟨r, hPC'⟩ := hPC
          rw [Set.mem_iUnion] at hPC'
          obtain ⟨_, hPmem⟩ := hPC'
          exact hPmem.isPrime
        have : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
        let : DecidableEq (T ⧸ P) := Classical.decEq _
        apply Set.Finite.subset (f.map (φ P)).roots.toFinset.finite_toSet
        intro α hα
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfne).mpr hα)
    rw [hC]
    exact ⟨hCmain_countable.union (Set.countable_singleton _),
      hD_countable.union hD_mod_countable⟩
  · left
    push Not at hR_le
    have hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier := le_of_lt hR_le
    have hC_le : Cardinal.mk C ≤ Cardinal.mk R.carrier := by
      rw [hC, hC_main]
      exact card_assoc_primes_union_bot_le R hR_inf
    have hD_le : Cardinal.mk D ≤ Cardinal.mk R.carrier := by
      rw [hD]
      exact card_shifted_roots_le R t hR_inf
    have hD_mod_le : Cardinal.mk D_mod ≤ Cardinal.mk R.carrier := by
      rw [hD_mod]
      exact card_mod_roots_le R t φ liftQ C_main hC_main hR_inf
    have hD_union_le : Cardinal.mk (D ∪ D_mod : Set T) ≤ Cardinal.mk R.carrier := by
      calc Cardinal.mk (D ∪ D_mod : Set T)
          ≤ Cardinal.mk D + Cardinal.mk D_mod := Cardinal.mk_union_le _ _
        _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier :=
            add_le_add hD_le hD_mod_le
        _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
    calc Cardinal.mk (↑C × ↑(D ∪ D_mod : Set T))
        = Cardinal.mk C * Cardinal.mk (D ∪ D_mod : Set T) := (Cardinal.mul_def _ _).symm
      _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier :=
          mul_le_mul' hC_le hD_union_le
      _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
      _ < Cardinal.mk T := hR_card
      _ = Cardinal.mk (IsLocalRing.ResidueField T) := hT_card

open scoped Pointwise in
/-- Modular transcendence of `t + δ`: if `δ` avoids every coset `P + (liftQ P α - t)`
for lifted roots `α` of reductions modulo associated primes, then a polynomial over `R`
vanishing at `t + δ` modulo a height-one prime `P` has all coefficients in `P ∩ R`. -/
private theorem no_common_modular_transcendence
    {R : NSubring T} (t δ : T) (C_main C : Set (Ideal T)) (D' : Set T)
    (hC_main : C_main = ⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
      associatedPrimes T (T ⧸ span {(r : T)}))
    (hC_main_le : C_main ⊆ C)
    (liftQ : (P : Ideal T) → T ⧸ P → T)
    (hliftQ : ∀ (P : Ideal T) (α : T ⧸ P), Ideal.Quotient.mk P (liftQ P α) = α)
    (hD_mod_le : ∀ P ∈ C_main, ∀ f : Polynomial R.carrier,
      f.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) ≠ 0 → ∀ α : T ⧸ P,
      (f.map ((Ideal.Quotient.mk P).comp R.carrier.subtype)).IsRoot α →
      liftQ P α - t ∈ D')
    (hδ_avoid : ∀ P ∈ C, ∀ r ∈ D', δ ∉ (P : Set T) + ({r} : Set T)) :
    ∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
      P.comap R.carrier.subtype ≠ ⊥ →
      ∀ (f : Polynomial R.carrier),
        (Polynomial.aeval (t + δ) f : T) ∈ (P : Set T) →
        ∀ i, f.coeff i ∈ P.comap R.carrier.subtype := by
  intro P hP_prime hP_ht hPR_ne f hf_in i
  by_contra h_neg
  have hf_bar_ne : f.map ((Ideal.Quotient.mk P).comp R.carrier.subtype) ≠ 0 := by
    intro h_eq
    apply h_neg
    have h := congr_arg (fun p => Polynomial.coeff p i) h_eq
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hP_in_C_main : P ∈ C_main := by
    obtain ⟨r₀, hr₀T_ne, hP_assoc⟩ :=
      prime_height_le_one_mem_assoc P hP_prime hP_ht hPR_ne
    rw [hC_main]
    exact Set.mem_iUnion.mpr ⟨r₀, Set.mem_iUnion.mpr ⟨hr₀T_ne, hP_assoc⟩⟩
  -- mk P (t+δ) is a root of the reduction of f in T/P
  have := hP_prime
  have ht_root : (f.map ((Ideal.Quotient.mk P).comp R.carrier.subtype)).IsRoot
      (Ideal.Quotient.mk P (t + δ)) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.hom_eval₂ f R.carrier.subtype (Ideal.Quotient.mk P) (t + δ)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf_in
  have hlift_in_D' : liftQ P (Ideal.Quotient.mk P (t + δ)) - t ∈ D' :=
    hD_mod_le P hP_in_C_main f hf_bar_ne _ ht_root
  -- δ - (liftQ P (mk P (t+δ)) - t) = (t+δ) - liftQ P (mk P (t+δ)) ∈ P
  have hlift_in_P : (t + δ) - liftQ P (Ideal.Quotient.mk P (t + δ)) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hliftQ]
    exact sub_self _
  -- So δ ∈ P + {liftQ P (mk P (t+δ)) - t}, contradicting avoidance
  have h_in_sum : δ ∈ (P : Set T) +
      ({liftQ P (Ideal.Quotient.mk P (t + δ)) - t} : Set T) := by
    refine ⟨(t + δ) - liftQ P (Ideal.Quotient.mk P (t + δ)), hlift_in_P,
      liftQ P (Ideal.Quotient.mk P (t + δ)) - t, rfl, ?_⟩
    ring
  exact absurd h_in_sum (hδ_avoid P (hC_main_le hP_in_C_main) _ hlift_in_D')

open scoped Pointwise in
/-- Heitmann reparametrization in the no-common-factor case: find `t'` transcendental
over `R`, avoiding all associated primes, modularly transcendental, and with
`c - t' * a ∈ s'·T`. -/
private theorem no_common_exists_transcendental
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_bot : ¬IsLocalRing.maximalIdeal T = ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    {n'' : ℕ}
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier} {s : Finset R.carrier}
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    {c : R.carrier}
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hno_common_prime : ∀ (p : R.carrier), Prime p → ¬(∀ x ∈ s', p ∣ x))
    (t : T) (u : T) (v : T)
    (hv : v ∈ Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)))
    (ht_eq : u = R.carrier.subtype a * t)
    (huv : u + v = (c : T))
    (hI_s'_bot : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) ≠ ⊥) :
    ∃ (t' : T),
      Transcendental R.carrier t' ∧
      (∀ (r : R.carrier), (r : T) ≠ 0 →
        ∀ P ∈ associatedPrimes T (T ⧸ span {(r : T)}), t' ∉ (P : Set T)) ∧
      ((c : T) - t' * (a : T)) ∈
        Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) ∧
      (∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (Polynomial.aeval t' f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype) := by
  set I_s' := Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier))
  set C : Set (Ideal T) :=
    (⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
      (associatedPrimes T (T ⧸ span {(r : T)}))) ∪ {⊥}
  set D : Set T :=
    {-t} ∪ ⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
      (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}
  have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := hM_bot
  have hC_prime : ∀ P ∈ C, P.IsPrime := by
    intro P hP
    rcases (Set.mem_union _ _ _).mp hP with h | h
    · rw [Set.mem_iUnion] at h
      obtain ⟨r, h⟩ := h
      rw [Set.mem_iUnion] at h
      obtain ⟨_, hPmem⟩ := h
      exact hPmem.isPrime
    · exact Set.mem_singleton_iff.mp h ▸ Ideal.isPrime_bot
  have hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T := by
    intro P hP
    rcases (Set.mem_union _ _ _).mp hP with h | h
    · rw [Set.mem_iUnion] at h
      obtain ⟨r, h⟩ := h
      rw [Set.mem_iUnion] at h
      obtain ⟨hr, hPmem⟩ := h
      exact fun heq => hM_not_assoc (r : T) hr (heq ▸ hPmem)
    · rw [Set.mem_singleton_iff.mp h]
      exact fun h => hM_ne_bot h.symm
  have hI_not_le : ∀ P ∈ C, ¬(I_s' ≤ P) := by
    intro P hP hle
    rcases (Set.mem_union _ _ _).mp hP with h | h
    · rw [Set.mem_iUnion] at h
      obtain ⟨r, h⟩ := h
      rw [Set.mem_iUnion] at h
      obtain ⟨hr_ne, hP_mem⟩ := h
      exact no_common_I_not_le_assoc hs_eq ha_mem s' hs'_def
        hno_common_prime hI_s'_bot r hr_ne P hP_mem hle
    · rw [Set.mem_singleton_iff.mp h] at hle
      exact hI_s'_bot (le_antisymm hle bot_le)
  let C_main : Set (Ideal T) := ⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
    (associatedPrimes T (T ⧸ span {(r : T)}))
  have hC_eq_main : C = C_main ∪ {⊥} := rfl
  let φ : (P : Ideal T) → R.carrier →+* T ⧸ P :=
    fun P => (Ideal.Quotient.mk P).comp R.carrier.subtype
  let liftQ : (P : Ideal T) → T ⧸ P → T :=
    fun P α => (Ideal.Quotient.mk_surjective α).choose
  have hliftQ : ∀ (P : Ideal T) (α : T ⧸ P),
      Ideal.Quotient.mk P (liftQ P α) = α :=
    fun P α => (Ideal.Quotient.mk_surjective α).choose_spec
  let D_mod : Set T :=
    ⋃ (P : Ideal T) (_ : P ∈ C_main) (f : Polynomial R.carrier)
      (_ : f.map (φ P) ≠ 0),
      (fun α => liftQ P α - t) '' { α : T ⧸ P | (f.map (φ P)).IsRoot α }
  let D' : Set T := D ∪ D_mod
  have hCD'_bound : Cardinal.mk (↑C × ↑D') <
      Cardinal.mk (IsLocalRing.ResidueField T) ∨
      (C.Countable ∧ D'.Countable) :=
    no_common_avoidance_bound R t hR_card hT_card φ liftQ C_main C D D_mod rfl rfl rfl rfl
  obtain ⟨δ, hδ_mem, hδ_avoid⟩ :=
    avoidance hC_prime hC_ne_max hCD'_bound hI_not_le
  refine ⟨t + δ, ?_, ?_, ?_, ?_⟩
  · -- Transcendence: δ is a shifted root in D', contradicting avoidance of ⊥ ∈ C
    rw [Transcendental]
    intro ⟨p, hp_ne, hp_eval⟩
    have hδ_in_D : δ ∈ D := Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp_ne,
        ⟨t + δ, hp_eval, by ring⟩⟩⟩)
    have hδ_in_D' : δ ∈ D' := Set.mem_union_left _ hδ_in_D
    have hbot_in_C : (⊥ : Ideal T) ∈ C := Set.mem_union_right _ rfl
    have h_absurd : δ ∈ ((⊥ : Ideal T) : Set T) + ({δ} : Set T) := by
      have := Set.add_mem_add ((⊥ : Ideal T).zero_mem)
        (show δ ∈ ({δ} : Set T) from rfl)
      rwa [zero_add] at this
    exact absurd h_absurd (hδ_avoid ⊥ hbot_in_C δ hδ_in_D')
  · -- Prime avoidance: δ ∉ P + {-t} implies t + δ ∉ P
    intro r hr P hP hmem
    have hP_in_C : P ∈ C := Set.mem_union_left _
      (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hP⟩⟩)
    have h_neg_t_in_D : -t ∈ D := Set.mem_union_left _ rfl
    have h_neg_t_in_D' : -t ∈ D' := Set.mem_union_left _ h_neg_t_in_D
    have h_in_sum : δ ∈ (P : Set T) + ({-t} : Set T) := by
      have := Set.add_mem_add hmem (show -t ∈ ({-t} : Set T) from rfl)
      rwa [show (t + δ) + -t = δ from by ring] at this
    exact absurd h_in_sum (hδ_avoid P hP_in_C (-t) h_neg_t_in_D')
  · -- Remainder: c - (t+δ)*a = v - δ*a ∈ I_s'
    suffices hrw : (↑c : T) - (t + δ) * (↑a : T) = v - δ * (↑a : T) by
      rw [hrw]
      exact Submodule.sub_mem _ hv (Ideal.mul_mem_right _ _ hδ_mem)
    have hsub : R.carrier.subtype a = (↑a : T) := rfl
    rw [hsub] at ht_eq
    have h_c_eq : (↑c : T) = (↑a : T) * t + v := by rw [← huv, ht_eq]
    rw [h_c_eq]
    ring
  · exact no_common_modular_transcendence t δ C_main C D' rfl Set.subset_union_left liftQ
      hliftQ (fun P hP f hf α hα => Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP,
          Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, ⟨α, hα, rfl⟩⟩⟩⟩⟩)) hδ_avoid

-- Extracted: no-common-factor branch of close_up_aux_wf.
-- When no prime divides all generators in s', use Heitmann reparametrization.
include T in
theorem close_up_aux_no_common_nonzero
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier} {s : Finset R.carrier}
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    {c : R.carrier}
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hs_insert : s = insert a s')
    (hs'_card : s'.card ≤ n'' + 1 + 1)
    (_hgcd : ¬∃ p : R.carrier, Prime p ∧ ∀ x ∈ s', p ∣ x)
    (hno_common_prime : ∀ (p : R.carrier), Prime p → ¬(∀ x ∈ s', p ∣ x))
    (t : T) (u : T) (v : T)
    (hv : v ∈ Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)))
    (ht_eq : u = R.carrier.subtype a * t)
    (huv : u + v = (c : T))
    (ha_zero : (a : T) ≠ 0)
    (hI_s'_bot : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) ≠ ⊥) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) := by
  by_cases hM_bot : IsLocalRing.maximalIdeal T = ⊥
  · refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
    have h_id : Subring.inclusion (le_refl R.carrier) = RingHom.id R.carrier :=
      RingHom.ext fun x => Subtype.ext rfl
    change (⟨(c : T), le_refl R.carrier c.2⟩ : R.carrier) ∈
      Ideal.map (Subring.inclusion (le_refl R.carrier)) (span (↑s : Set R.carrier))
    rw [h_id, Ideal.map_id]
    have ha_unit : IsUnit a := by
      by_contra h
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr h
      rw [R.maximal_ideal_eq, Ideal.mem_comap, hM_bot, Submodule.mem_bot] at hmem
      exact ha_zero hmem
    rw [Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Finset.mem_coe.mpr ha_mem)) ha_unit]
    exact Submodule.mem_top
  obtain ⟨t', ht'_trans, ht'_avoid, hrem_T, ht'_mod_trans⟩ :=
    no_common_exists_transcendental hM_bot hM_not_assoc hT_card hR_card hs_eq ha_mem s'
      hs'_def hno_common_prime t u v hv ht_eq huv hI_s'_bot
  -- Step 4: Adjoin t' to R → S₁ (NSubring, A-extension of R)
  obtain ⟨S₁, hAext₁, ht'_S₁⟩ :=
    adjoin_transcendental_isNSubring R t' ht'_trans
      hAss_ht ht'_mod_trans
  have hle₁ := hAext₁.le
  -- Step 5: Form rem in S₁
  have hrem_in_S₁ : (c : T) - t' * (a : T) ∈ S₁.carrier :=
    S₁.carrier.sub_mem (hle₁ c.2) (S₁.carrier.mul_mem ht'_S₁ (hle₁ a.2))
  let rem₁ : S₁.carrier := ⟨(c : T) - t' * (a : T), hrem_in_S₁⟩
  have : DecidableEq S₁.carrier := Classical.decEq _
  let liftR₁ := Subring.inclusion hle₁
  let s₁ : Finset S₁.carrier := s'.image liftR₁
  have hs₁_eq : s₁ = s'.image liftR₁ := rfl
  have hs₁_card : s₁.card ≤ n'' + 1 + 1 := by
    change (s'.image liftR₁).card ≤ _
    exact Finset.card_image_le.trans hs'_card
  have hcomp : S₁.carrier.subtype.comp liftR₁ = R.carrier.subtype :=
    RingHom.ext fun _ => rfl
  have hrem₁_span : (rem₁ : T) ∈
      Ideal.map S₁.carrier.subtype (span (↑s₁ : Set S₁.carrier)) := by
    change (c : T) - t' * (a : T) ∈ _
    change _ ∈ Ideal.map S₁.carrier.subtype
      (span (↑(s'.image liftR₁) : Set S₁.carrier))
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map, hcomp]
    exact hrem_T
  have hS₁_card : Cardinal.mk S₁.carrier < Cardinal.mk T :=
    lt_of_le_of_lt hAext₁.card_le (max_lt hT_aleph0 hR_card)
  -- Step 6: Apply IH to S₁ with generators s₁ and element rem₁
  obtain ⟨S₂, hAext₂, hle₂, hrem₂⟩ :=
    ih S₁ hS₁_card s₁ hs₁_card rem₁ hrem₁_span
  -- Step 7-8: Compose A-extensions R → S₁ → S₂ and recombine
  refine ⟨S₂, isAExtension_trans' hAext₁ hAext₂,
    le_trans hle₁ hle₂, ?_⟩
  -- Decompose span(s) = span{a} ⊔ span(s') since s = insert a s'
  rw [hs_insert, Finset.coe_insert, Ideal.span_insert, Ideal.map_sup]
  -- c = t'*a + rem in S₂; show each piece is in the right summand
  refine Submodule.mem_sup.mpr
    ⟨⟨t', hle₂ ht'_S₁⟩ * ⟨(a : T), (le_trans hle₁ hle₂) a.2⟩, ?_,
     ⟨(c : T) - t' * (a : T), hle₂ hrem_in_S₁⟩, ?_, ?_⟩
  · rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · -- rem ∈ Ideal.map incl (span ↑s')
    have hcomp₂ : (Subring.inclusion hle₂).comp liftR₁ =
        Subring.inclusion (le_trans hle₁ hle₂) :=
      RingHom.ext fun _ => rfl
    change ⟨(rem₁ : T), hle₂ rem₁.2⟩ ∈
      Ideal.map (Subring.inclusion hle₂)
        (span (↑(s'.image liftR₁) : Set S₁.carrier)) at hrem₂
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map, hcomp₂] at hrem₂
    exact hrem₂
  · exact Subtype.ext (by
                         simp only [Subring.coe_add, Subring.coe_mul]
                         ring)

include T in
theorem close_up_aux_no_common
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier} {s : Finset R.carrier}
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    {c : R.carrier}
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)))
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hs_insert : s = insert a s')
    (hs'_card : s'.card ≤ n'' + 1 + 1)
    (hgcd : ¬∃ p : R.carrier, Prime p ∧ ∀ x ∈ s', p ∣ x) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) := by
  -- No common factor in s': hno_common_prime holds by classical logic
  have hno_common_prime : ∀ (p : R.carrier), Prime p → ¬(∀ x ∈ s', p ∣ x) :=
    fun p hp hall => hgcd ⟨p, hp, hall⟩
  -- Step 2: Decompose hc via span_insert and Submodule.mem_sup
  rw [hs_insert, Finset.coe_insert, Ideal.span_insert, Ideal.map_sup] at hc
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hc
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht_eq⟩ := hu
  have hv_eq : v = (c : T) - u := eq_sub_of_add_eq' huv
  -- Special case: a = 0 → apply IH directly with s' and c
  by_cases ha_zero : (a : T) = 0
  · -- a = 0: u = 0, so c ∈ span(s')·T. Apply IH directly.
    have hc_s' : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) := by
      have hu_zero : u = 0 := by
        rw [ht_eq]
        change (a : T) * t = 0
        rw [ha_zero, zero_mul]
      rw [← huv, hu_zero, zero_add]
      exact hv
    obtain ⟨S, hAext, hle, hmem⟩ := ih R hR_card s' hs'_card c hc_s'
    exact ⟨S, hAext, hle,
      Ideal.map_mono (Ideal.span_mono (Finset.coe_subset.mpr
        (hs'_def ▸ Finset.erase_subset a s))) hmem⟩
  · -- a ≠ 0: use reparametrization trick
    -- Case split: I_s' = ⊥ (trivial) vs I_s' ≠ ⊥ (Heitmann reparametrization)
    by_cases hI_s'_bot : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) = ⊥
    · -- I_s' = 0: c = a*t, so c ∈ span{a} ⊆ span(s) via close_up_dvd
      have hv_zero : v = 0 := (Submodule.mem_bot T).mp (hI_s'_bot ▸ hv)
      have hc_aT : (c : T) ∈ span {(a : T)} := by
        rw [← huv, hv_zero, add_zero, ht_eq]
        exact Ideal.mem_span_singleton.mpr ⟨t, rfl⟩
      refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
      have h_id : Subring.inclusion (le_refl R.carrier) = RingHom.id R.carrier :=
        RingHom.ext fun x => Subtype.ext rfl
      have hcR := close_up_dvd R a c hc_aT
      change (⟨(c : T), le_refl R.carrier c.2⟩ : R.carrier) ∈
        Ideal.map (Subring.inclusion (le_refl R.carrier)) (span (↑s : Set R.carrier))
      rw [h_id, Ideal.map_id, hs_insert, Finset.coe_insert]
      exact Ideal.span_mono
        (Set.singleton_subset_iff.mpr (Set.mem_insert a _)) hcR
    · exact close_up_aux_no_common_nonzero hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih
        hR_card hs_eq ha_mem s' hs'_def hs_insert hs'_card hgcd hno_common_prime
        t u v hv ht_eq huv ha_zero hI_s'_bot

end
