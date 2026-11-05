/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import LeanPool.AndersonConjecture.Jensen.TransfiniteUnion
public import Mathlib.RingTheory.AdicCompletion.Basic
import LeanPool.AndersonConjecture.Jensen.Construction.ChainHelpers
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transfinite Construction

The ordinal-indexed iteration that builds an ascending chain of
N-subrings, ensuring at each successor step that one more prime
is caught and one more element of T/M^2 is covered.

Jensen, "Completions of UFDs with semi-local formal fibers",
2006, Theorem 2.2.
-/

@[expose] public section

universe u

noncomputable section

open Cardinal Ideal

/-- For `i : (Cardinal.ord c).ToType`, the cardinality of the initial segment
below `i` is strictly less than `c`. -/
private theorem mk_Iio_ord_lt {c : Cardinal} (i : c.ord.ToType) : #(Set.Iio i) < c := by
  have hlt := mk_Iio_lt i (h := by rw [mk_ord_toType, Ordinal.type_toType])
  rwa [mk_ord_toType] at hlt


variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]
/-! ## Ordinal-indexed transfinite construction

Replace the Zorn approach (which needs `hk_countable`) with ordinal recursion
over V = {nonzero primes of T} × T/M². This eliminates the countability
assumption, using `ℵ₀ < #T` and `#R < #T` propagation instead.

### Architecture
- **Index set**: V = {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} × (T ⧸ M²)
- **Ordinal**: κ = Cardinal.ord (#V)
- **Base**: R₀ = initial_NSubring (from NSubring.lean), closed up
- **Successor at α**: combined_step_card R(α) (q_α, ℓ_α)
- **Limit at λ**: transfinite union of R(β) for β < λ
- **Result**: A = R(κ) satisfies surjectivity, closedness, prime coverage
-/

/-! ### Helper lemma: build an NSubring from a union of predecessors

Extracted from the main transfinite construction to stay within the default
heartbeat budget. Given a family of NSubrings indexed by predecessors of `α`,
builds the union as an NSubring with cardinal bounds and prime preservation. -/

private noncomputable def mk_union_nsub_aux
    {ι : Type u} [LinearOrder ι]
    (α : ι) (rings : ∀ β, β < α → NSubring T)
    (hne : ∃ β₀ : ι, β₀ < α)
    (hmono : ∀ ⦃β₁ β₂ : ι⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α),
      β₁ ≤ β₂ → (rings β₁ hβ₁).carrier ≤ (rings β₂ hβ₂).carrier)
    (hprimes : ∀ ⦃β₁ β₂ : ι⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α) (_ : β₁ ≤ β₂)
      (r : (rings β₁ hβ₁).carrier) (hmem : (r : T) ∈ (rings β₂ hβ₂).carrier),
      Prime r → Prime (⟨(r : T), hmem⟩ : (rings β₂ hβ₂).carrier))
    (hIH_cb : ∀ β (hβ : β < α), Cardinal.mk (rings β hβ).carrier ≤
      max Cardinal.aleph0 (Cardinal.mk {γ : ι // γ ≤ β}))
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (h_idx_lt_T : Cardinal.mk {β : ι // β < α} < Cardinal.mk T) :
    Σ' (U : NSubring T),
      (Cardinal.mk U.carrier < Cardinal.mk T) ∧
      (Cardinal.mk U.carrier ≤ max Cardinal.aleph0
        (Cardinal.mk {γ : ι // γ < α})) ∧
      (∀ β (hβ : β < α), (rings β hβ).carrier ≤ U.carrier) ∧
      (∀ β (hβ : β < α) (r : (rings β hβ).carrier),
        Prime r → ∀ (hmem : (r : T) ∈ U.carrier),
          Prime (⟨(r : T), hmem⟩ : U.carrier)) := by
  haveI : Nonempty {β : ι // β < α} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let lc : NSubringChain T {β : ι // β < α} :=
    { ring := fun ⟨β, hβ⟩ => rings β hβ
      mono := fun ⟨_, hβ₁⟩ ⟨_, hβ₂⟩ hle => hmono hβ₁ hβ₂ hle
      primes_preserved := fun ⟨_, hβ₁⟩ ⟨_, hβ₂⟩ hle r hr =>
        hprimes hβ₁ hβ₂ hle r ((hmono hβ₁ hβ₂ hle) r.2) hr }
  set U := lc.unionSubring with hU_def
  have hU_le := lc.le_union
  have hU_mem : ∀ x : ↥U, ∃ β : {β : ι // β < α},
      (x : T) ∈ (lc.ring β).carrier := fun x => lc.mem_union_iff.mp x.2
  have h_tight : Cardinal.mk ↥U ≤
      max Cardinal.aleph0 (Cardinal.mk {γ : ι // γ < α}) := by
    set n := Cardinal.mk {γ : ι // γ < α}
    have h_each_le : ∀ (β : ι) (hβ : β < α),
        Cardinal.mk (rings β hβ).carrier ≤ max Cardinal.aleph0 n := by
      intro β hβ
      exact le_trans (hIH_cb β hβ)
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun γ hγ => lt_of_le_of_lt hγ hβ)))
    have h_sup_le : ⨆ (β : {β : ι // β < α}),
        Cardinal.mk ↑((lc.ring β).carrier : Set T) ≤ max Cardinal.aleph0 n := by
      apply ciSup_le
      intro ⟨β, hβ⟩
      exact le_trans (le_of_eq rfl) (h_each_le β hβ)
    have hU_eq : (U : Set T) = ⋃ β : {β : ι // β < α},
        ↑(lc.ring β).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed lc.directed_carriers
    have h1 : Cardinal.mk ↥U ≤ n *
        ⨆ (β : {β : ι // β < α}),
          Cardinal.mk ↑((lc.ring β).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le
        (fun β : {β : ι // β < α} => ((lc.ring β).carrier : Set T))
      rwa [← hU_eq] at this
    calc Cardinal.mk ↥U
        ≤ n * ⨆ (β : {β : ι // β < α}),
            Cardinal.mk ↑((lc.ring β).carrier : Set T) := h1
      _ ≤ n * max Cardinal.aleph0 n := mul_le_mul_right h_sup_le _
      _ ≤ max Cardinal.aleph0 n * max Cardinal.aleph0 n :=
          mul_le_mul_left (le_max_right _ _) _
      _ ≤ max (max Cardinal.aleph0 n) (max Cardinal.aleph0 n) :=
          Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = max Cardinal.aleph0 n := max_self _
  have hU_lt : Cardinal.mk ↥U < Cardinal.mk T :=
    lt_of_le_of_lt h_tight (max_lt hT_aleph0 h_idx_lt_T)
  have hU_card : Cardinal.mk ↥U ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) :=
    hU_lt.le.trans (hcard.le.trans (le_max_right ..))
  refine ⟨lc.unionNSubring hU_card, hU_lt, h_tight, fun β hβ => hU_le ⟨β, hβ⟩, ?_⟩
  intro β hβ r hr hmem
  exact transfinite_union_primes_preserved lc U hU_le hU_mem ⟨β, hβ⟩ r hr


omit [IsNoetherianRing T] [IsDomain T] in
/-- A regular sequence of length two in the maximal ideal forces it to be nonzero. -/
private lemma maximalIdeal_ne_bot_of_depth
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b]) :
    IsLocalRing.maximalIdeal T ≠ ⊥ := by
  intro h
  obtain ⟨a, _, ha_mem, _, hreg⟩ := hdepth
  rw [h] at ha_mem
  simp only [Ideal.mem_bot] at ha_mem
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
  have hreg0 : IsSMulRegular T (0 : T) := ha_mem ▸ hreg.1
  exact one_ne_zero (hreg0 (show (0 : T) • (0 : T) = 0 • 1 by simp)).symm

omit [IsDomain T] in
/-- The index set of the construction has cardinality at most `#T`. -/
private lemma card_index_le (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    Cardinal.mk ({q : Ideal T // q.IsPrime ∧ q ≠ ⊥} × (T ⧸ IsLocalRing.maximalIdeal T ^ 2)) ≤
      Cardinal.mk T := by
  have hT_inf : Infinite T := Cardinal.infinite_iff.mpr (le_of_lt hT_aleph0)
  have h_primes_le : Cardinal.mk {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} ≤ Cardinal.mk T := by
    calc Cardinal.mk {q : Ideal T // q.IsPrime ∧ q ≠ ⊥}
        ≤ Cardinal.mk (Ideal T) := Cardinal.mk_subtype_le _
      _ ≤ Cardinal.mk (Finset T) :=
          Cardinal.mk_le_of_surjective fun I =>
            IsNoetherian.noetherian (I : Ideal T)
      _ = Cardinal.mk T := Cardinal.mk_finset_of_infinite T
  have h_quot_le : Cardinal.mk (T ⧸ IsLocalRing.maximalIdeal T ^ 2) ≤ Cardinal.mk T :=
    Cardinal.mk_quotient_le
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc _ ≤ Cardinal.mk T * Cardinal.mk T := mul_le_mul' h_primes_le h_quot_le
    _ = Cardinal.mk T := Cardinal.mul_eq_self (le_of_lt hT_aleph0)

/-- Joint well-founded induction for the transfinite chain: every earlier ring lies in the
predecessor ring `prev α`, and primes are preserved along the chain up to `α`. -/
private lemma chain_le_prev_and_primes {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    (ring prev : ι → NSubring T) (hext : ∀ α, IsAExtension (prev α) (ring α))
    (hprev_limit : ∀ α, ¬IsMin α → Order.IsSuccLimit α →
      (∀ ⦃β₁ β₂ : ι⦄, β₁ < α → β₂ < α → β₁ ≤ β₂ →
        (ring β₁).carrier ≤ (ring β₂).carrier) →
      (∀ ⦃β₁ β₂ : ι⦄, β₁ < α → β₂ < α → β₁ ≤ β₂ →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier)) →
      (∀ β, β < α → (ring β).carrier ≤ (prev α).carrier) ∧
      (∀ β, β < α → ∀ (r : (ring β).carrier), Prime r →
        ∀ (hmem : (r : T) ∈ (prev α).carrier), Prime (⟨(r : T), hmem⟩ : (prev α).carrier)))
    (hprev_succ : ∀ α, ¬IsMin α → ¬Order.IsSuccLimit α →
      ∃ γ, γ < α ∧ (∀ β, β < α → β ≤ γ) ∧ prev α = ring γ)
    (α : ι) :
    (∀ β, β < α → (ring β).carrier ≤ (prev α).carrier) ∧
      (∀ ⦃β₁ β₂ : ι⦄, β₁ ≤ β₂ → β₂ ≤ α →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier)) := by
  induction α using WellFoundedLT.induction with
  | ind α IH_wf =>
  have hmono_lt : ∀ ⦃β₁ β₂ : ι⦄, β₁ ≤ β₂ → β₂ < α →
      (ring β₁).carrier ≤ (ring β₂).carrier := by
    intro β₁ β₂ hle hβ₂
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_refl _
    · exact ((IH_wf β₂ hβ₂).1 β₁ hlt).trans (hext β₂).le
  have hprimes_lt : ∀ ⦃β₁ β₂ : ι⦄, β₁ ≤ β₂ → β₂ < α →
      ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
        Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier) :=
    fun β₁ β₂ hle hβ₂ r hmem hr => (IH_wf β₂ hβ₂).2 hle (le_refl _) r hmem hr
  -- Earlier rings lie in `prev α`, and their primes stay prime there
  have hprev : (∀ β, β < α → (ring β).carrier ≤ (prev α).carrier) ∧
      (∀ β, β < α → ∀ (r : (ring β).carrier), Prime r →
        ∀ (hmem : (r : T) ∈ (prev α).carrier),
          Prime (⟨(r : T), hmem⟩ : (prev α).carrier)) := by
    by_cases hmin : IsMin α
    · exact ⟨fun β hβ => absurd (hmin (le_of_lt hβ)) (not_le.mpr hβ),
        fun β hβ => absurd (hmin (le_of_lt hβ)) (not_le.mpr hβ)⟩
    by_cases hlim : Order.IsSuccLimit α
    · exact hprev_limit α hmin hlim (fun β₁ β₂ _ hβ₂ hle => hmono_lt hle hβ₂)
        (fun β₁ β₂ _ hβ₂ hle r hmem hr => hprimes_lt hle hβ₂ r hmem hr)
    obtain ⟨γ, hγ_lt, hγ_max, hprev_eq⟩ := hprev_succ α hmin hlim
    rw [hprev_eq]
    exact ⟨fun β hβ => hmono_lt (hγ_max β hβ) hγ_lt,
      fun β hβ r hr hmem => hprimes_lt (hγ_max β hβ) hγ_lt r hmem hr⟩
  refine ⟨hprev.1, ?_⟩
  -- Prime transfer: β₁ ≤ β₂ ≤ α, key case is β₂ = α via prev(α)
  intro β₁ β₂ hle hle_α r hmem hr
  rcases eq_or_lt_of_le hle with rfl | hlt
  · convert hr using 1
  · rcases eq_or_lt_of_le hle_α with heq_α | hlt_α
    · have hβ₁_lt_α : β₁ < α := heq_α ▸ hlt
      have hmem_prev : (r : T) ∈ (prev α).carrier := hprev.1 β₁ hβ₁_lt_α r.2
      have hprime_ring := (hext α).primes_preserved ⟨(r : T), hmem_prev⟩
        (hprev.2 β₁ hβ₁_lt_α r hr hmem_prev)
      cases heq_α
      convert hprime_ring using 1
    · exact hprimes_lt hle hlt_α r hmem hr

/-- Closedness `IT ∩ A = I` for finitely generated `I` passes to the union of a chain. -/
private lemma chain_union_closed {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (chain : NSubringChain T ι) (A : NSubring T)
    (hA_le : ∀ α : ι, (chain.ring α).carrier ≤ A.carrier)
    (hA_mem : ∀ x : A.carrier, ∃ α : ι, (x : T) ∈ (chain.ring α).carrier)
    (hclosed : ∀ α : ι, ∀ (I : Ideal (chain.ring α).carrier), I.FG →
      ∀ (c : (chain.ring α).carrier),
        (c : T) ∈ Ideal.map (chain.ring α).carrier.subtype I → c ∈ I)
    (I : Ideal A.carrier) (hI_fg : I.FG) (c : A.carrier)
    (hc_mem : (c : T) ∈ Ideal.map A.carrier.subtype I) : c ∈ I := by
  classical
  have hfin_cover : ∀ (F : Finset A.carrier), ∃ α : ι,
      ∀ x ∈ F, (x : T) ∈ (chain.ring α).carrier := by
    intro F
    induction F using Finset.induction with
    | empty =>
      exact ⟨Classical.arbitrary _, fun _ h => absurd h (by simp)⟩
    | @insert a F' _ha ih =>
      obtain ⟨α₁, hα₁⟩ := ih
      obtain ⟨α₂, hα₂⟩ := hA_mem a
      exact ⟨max α₁ α₂, fun x hx => by
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact chain.mono (le_max_right α₁ α₂) hα₂
        · exact chain.mono (le_max_left α₁ α₂) (hα₁ x hx)⟩
  obtain ⟨s, hs⟩ := hI_fg
  obtain ⟨γ, hγ⟩ := hfin_cover (insert c s)
  have hgens_γ : ∀ g ∈ s, (g : T) ∈ (chain.ring γ).carrier :=
    fun g hg => hγ g (Finset.mem_insert_of_mem hg)
  have hc_γ : (c : T) ∈ (chain.ring γ).carrier :=
    hγ c (Finset.mem_insert_self c s)
  set c_γ : (chain.ring γ).carrier := ⟨(c : T), hc_γ⟩
  let s_γ : Finset (chain.ring γ).carrier :=
    s.attach.image (fun ⟨g, hg⟩ =>
      (⟨(g : T), hgens_γ g hg⟩ : (chain.ring γ).carrier))
  let J := Ideal.span (↑s_γ : Set (chain.ring γ).carrier)
  have hc_in_JT :
      (c_γ : T) ∈ Ideal.map (chain.ring γ).carrier.subtype J := by
    suffices h : Ideal.map A.carrier.subtype I ≤
        Ideal.map (chain.ring γ).carrier.subtype J by
      exact h hc_mem
    rw [← hs, Ideal.map_span, Ideal.map_span]
    apply Ideal.span_mono
    rintro t ⟨g, hg_mem, rfl⟩
    have hg := Finset.mem_coe.mp hg_mem
    exact ⟨⟨(g : T), hgens_γ g hg⟩,
      Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩), rfl⟩
  have hc_in_J : c_γ ∈ J :=
    hclosed γ J ⟨s_γ, rfl⟩ c_γ hc_in_JT
  let incl := Subring.inclusion (hA_le γ)
  have hJ_le_I : Ideal.map incl J ≤ I := by
    rw [← hs, Ideal.map_span]
    apply Ideal.span_mono
    rintro t ⟨x, hx_mem, rfl⟩
    simp only [Finset.mem_coe] at hx_mem
    rw [Finset.mem_image] at hx_mem
    obtain ⟨⟨g, hg⟩, _, rfl⟩ := hx_mem
    change (Subring.inclusion (hA_le γ)
      ⟨(g : T), hgens_γ g hg⟩ : A.carrier) ∈ (↑s : Set _)
    rw [show (Subring.inclusion (hA_le γ)
      ⟨(g : T), hgens_γ g hg⟩ : A.carrier) = g
      from Subtype.ext rfl]
    exact Finset.mem_coe.mpr hg
  have h_mem := hJ_le_I (Ideal.mem_map_of_mem incl hc_in_J)
  rwa [show incl c_γ = c from Subtype.ext rfl] at h_mem

/-- Cardinality bound for the union of a chain indexed by a small enough type. -/
private lemma chain_union_card_le {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (chain : NSubringChain T ι)
    (hι_card : Cardinal.mk ι ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))) :
    Cardinal.mk ↥chain.unionSubring ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
  set U := chain.unionSubring with hU_def
  have hU_eq : (U : Set T) = ⋃ α, ↑(chain.ring α).carrier := by
    rw [hU_def, NSubringChain.unionSubring]
    exact Subring.coe_iSup_of_directed chain.directed_carriers
  set κ' := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
  have h1 : Cardinal.mk ↥U ≤ Cardinal.mk ι *
      ⨆ (α : ι), Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
    have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
    rwa [← hU_eq] at this
  have h2 : ⨆ (α : ι), Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤ κ' :=
    ciSup_le fun α => (chain.ring α).card_le
  calc Cardinal.mk ↥U
      ≤ Cardinal.mk ι *
        ⨆ (α : ι), Cardinal.mk ↑((chain.ring α).carrier : Set T) := h1
    _ ≤ Cardinal.mk ι * κ' := mul_le_mul_right h2 _
    _ ≤ κ' * κ' := mul_le_mul_left hι_card κ'
    _ ≤ max κ' κ' := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
    _ = κ' := max_self κ'

/-- Assemble the union `A` of the transfinite chain and transfer surjectivity onto `T/M²`,
closedness and prime catching from the rings of the chain to `A`. -/
private lemma transfinite_result_of_family {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (ring prev : ι → NSubring T) (hext : ∀ α, IsAExtension (prev α) (ring α))
    (hcombined : ∀ α, (∀ β, β < α → (ring β).carrier ≤ (prev α).carrier) ∧
      (∀ ⦃β₁ β₂ : ι⦄, β₁ ≤ β₂ → β₂ ≤ α →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier)))
    (hclosed : ∀ α : ι, ∀ (I : Ideal (ring α).carrier), I.FG →
      ∀ (c : (ring α).carrier), (c : T) ∈ Ideal.map (ring α).carrier.subtype I → c ∈ I)
    (hsurj : ∀ ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2, ∃ α : ι,
      ∃ (c : (ring α).carrier), Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ)
    (hcatch : ∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ → ∃ α : ι,
      ∃ (t : (ring α).carrier), (t : T) ∈ q ∧ (t : T) ≠ 0)
    (hι_card : Cardinal.mk ι ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))) :
    ∃ (A : NSubring T),
      (Function.Surjective (fun r : A.carrier =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T))) ∧
      (∀ (I : Ideal A.carrier), I.FG →
        ∀ (c : A.carrier), (c : T) ∈ Ideal.map A.carrier.subtype I → c ∈ I) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ →
        ∃ (t : A.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) := by
  have hmono : ∀ ⦃β₁ β₂ : ι⦄, β₁ ≤ β₂ →
      (ring β₁).carrier ≤ (ring β₂).carrier := by
    intro β₁ β₂ hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_refl _
    · exact ((hcombined β₂).1 β₁ hlt).trans (hext β₂).le
  have hprimes_pres : ∀ ⦃β₁ β₂ : ι⦄ (h : β₁ ≤ β₂)
      (r : (ring β₁).carrier), Prime r →
      Prime (⟨r.1, hmono h r.2⟩ : (ring β₂).carrier) := by
    intro β₁ β₂ hle r hr
    rcases eq_or_lt_of_le hle with rfl | hlt
    · convert hr using 1
    · exact (hcombined β₂).2 hle (le_refl β₂) r (hmono hle r.2) hr
  let chain : NSubringChain T ι :=
    { ring := ring
      mono := hmono
      primes_preserved := hprimes_pres }
  let A : NSubring T := chain.unionNSubring (chain_union_card_le chain hι_card)
  refine ⟨A, ?_, chain_union_closed chain A chain.le_union
    (fun x => chain.mem_union_iff.mp x.2) hclosed, ?_⟩
  · intro ℓ
    obtain ⟨α, c, hc⟩ := hsurj ℓ
    exact ⟨⟨(c : T), chain.le_union α c.2⟩, hc⟩
  · intro q hq hq_ne
    obtain ⟨α, t, ht_q, ht_ne⟩ := hcatch q hq hq_ne
    exact ⟨⟨(t : T), chain.le_union α t.2⟩, ht_q, ht_ne⟩

include T in
/-- The transfinite construction via ordinal recursion: iterate `combined_step`
over all (prime, residue) pairs indexed by ordinals, building an N-subring A
of T that is surjective onto T/M², has every nonzero prime of T meeting A
nontrivially, and satisfies the closedness condition IT ∩ A = I.

This replaces the Zorn-based `transfinite_construction_zorn` which required
`hk_countable : #k ≤ ℵ₀` (false for our T). Instead takes `hT_aleph0 : ℵ₀ < #T`
and propagates cardinal bounds `#R < #T` through the chain. -/
theorem transfinite_construction
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ (A : NSubring T),
      (Function.Surjective (fun r : A.carrier =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T))) ∧
      (∀ (I : Ideal A.carrier), I.FG →
        ∀ (c : A.carrier), (c : T) ∈ Ideal.map A.carrier.subtype I → c ∈ I) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ →
        ∃ (t : A.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) := by
  obtain ⟨R₀, hR₀_count⟩ := initial_NSubring hchar
  have hR₀_card : Cardinal.mk R₀.carrier < Cardinal.mk T :=
    lt_of_le_of_lt hR₀_count hT_aleph0
  have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := maximalIdeal_ne_bot_of_depth hdepth
  obtain ⟨S₀, hS₀_ext, hS₀_closed⟩ :=
    combined_step_surj_card R₀ 0 hM_not_assoc hAss_ht hR₀_card hT_aleph0 hcard hM_ne_bot
  obtain ⟨_, hS₀_closed, hS₀_card⟩ := hS₀_closed
  let V := {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} × (T ⧸ IsLocalRing.maximalIdeal T ^ 2)
  have hV_card : Cardinal.mk V ≤ Cardinal.mk T := card_index_le hT_aleph0
  let κ := Cardinal.ord (Cardinal.mk V)
  have : Nonempty V :=
    ⟨⟨⟨IsLocalRing.maximalIdeal T,
       (IsLocalRing.maximalIdeal.isMaximal (R := T)).isPrime, hM_ne_bot⟩, 0⟩⟩
  have : Nonempty κ.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact Cardinal.mk_ne_zero V
  obtain ⟨enum⟩ := Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk V))
  -- Bundled return type for WellFounded.fix: ring + predecessor + properties
  let RD := fun (α : κ.ToType) => Σ' (R : NSubring T) (prev : NSubring T),
    IsAExtension prev R ∧
    (Cardinal.mk R.carrier < Cardinal.mk T) ∧
    (∀ (I : Ideal R.carrier), I.FG →
      ∀ c : R.carrier, (c : T) ∈ Ideal.map R.carrier.subtype I → c ∈ I) ∧
    (∃ c : R.carrier,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = (enum α).2) ∧
    (∃ t : R.carrier, (t : T) ∈ (enum α).1.1 ∧ (t : T) ≠ 0) ∧
    (Cardinal.mk R.carrier ≤ max Cardinal.aleph0
      (Cardinal.mk {γ : κ.ToType // γ ≤ α}))
  -- IH_good: monotonicity + prime preservation for predecessors
  let IH_good := fun (α : κ.ToType) (IH : ∀ β, β < α → RD β) =>
    (∀ ⦃β₁ β₂ : κ.ToType⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α),
      β₁ ≤ β₂ → (IH β₁ hβ₁).1.carrier ≤ (IH β₂ hβ₂).1.carrier) ∧
    (∀ ⦃β₁ β₂ : κ.ToType⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α) (hle : β₁ ≤ β₂)
      (r : (IH β₁ hβ₁).1.carrier) (hmem : (r : T) ∈ (IH β₂ hβ₂).1.carrier),
      Prime r → Prime (⟨(r : T), hmem⟩ : (IH β₂ hβ₂).1.carrier))
  have mk_union_nsub : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β)
      (_ : ∃ β₀ : κ.ToType, β₀ < α) (_ : IH_good α IH)
      (_ : ∀ β (hβ : β < α), Cardinal.mk (IH β hβ).1.carrier ≤
        max Cardinal.aleph0 (Cardinal.mk {γ : κ.ToType // γ ≤ β})),
      Σ' (U : NSubring T),
        (Cardinal.mk U.carrier < Cardinal.mk T) ∧
        (Cardinal.mk U.carrier ≤ max Cardinal.aleph0
          (Cardinal.mk {γ : κ.ToType // γ < α})) ∧
        (∀ β (hβ : β < α), (IH β hβ).1.carrier ≤ U.carrier) ∧
        (∀ β (hβ : β < α) (r : (IH β hβ).1.carrier),
          Prime r → ∀ (hmem : (r : T) ∈ U.carrier),
            Prime (⟨(r : T), hmem⟩ : U.carrier)) := by
    intro α IH hne hgood hIH_cb
    exact mk_union_nsub_aux α (fun β hβ => (IH β hβ).1) hne hgood.1 hgood.2
      hIH_cb hcard hT_aleph0
        (lt_of_lt_of_le (mk_Iio_ord_lt (c := Cardinal.mk V) α) hV_card)
  -- prevF: predecessor ring (min→S₀, limit→union, successor→ring(γ))
  let prevF : (α : κ.ToType) → (∀ β, β < α → RD β) → NSubring T :=
    fun α IH =>
    @dite _ (IsMin α) (Classical.dec _)
      (fun _ => S₀)
      (fun hmin =>
        @dite _ (Order.IsSuccLimit α) (Classical.dec _)
          (fun hlim =>
            @dite _ (IH_good α IH) (Classical.dec _)
              (fun hgood =>
                (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
                  (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).1)
              (fun _ => S₀))
          (fun hlim =>
            let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
            let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
            let hγ_lt := lt_of_lt_of_eq (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1)
              hγ_ex.choose_spec.2
            (IH hγ_ex.choose hγ_lt).1))
  have hprevF_card : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β),
      Cardinal.mk (prevF α IH).carrier < Cardinal.mk T := by
    intro α IH
    simp only [prevF]
    split_ifs with hmin hlim hgood
    · exact hS₀_card
    · exact (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
        (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).2.1
    · exact hS₀_card
    · exact (IH _ _).2.2.2.1
  have hprevF_cb : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β),
      Cardinal.mk (prevF α IH).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk {γ : κ.ToType // γ ≤ α}) := by
    intro α IH
    simp only [prevF]
    split_ifs with hmin hlim hgood
    · exact le_trans (le_trans hS₀_ext.card_le
        (max_le (le_refl _) hR₀_count)) (le_max_left ..)
    · exact le_trans
        (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
          (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).2.2.1
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun γ hγ => le_of_lt hγ)))
    · exact le_trans (le_trans hS₀_ext.card_le
        (max_le (le_refl _) hR₀_count)) (le_max_left ..)
    · let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
      let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
      let hγ_lt := lt_of_lt_of_eq (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1)
        hγ_ex.choose_spec.2
      exact le_trans (IH hγ_ex.choose hγ_lt).2.2.2.2.2.2.2
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun δ hδ =>
          le_trans hδ (le_of_lt hγ_lt))))
  let hbuildF : ∀ (α : κ.ToType), (∀ β, β < α → RD β) → RD α :=
    fun α IH =>
    let prev := prevF α IH
    let h := combined_step_card prev (enum α).2 (enum α).1.1
      (enum α).1.2.1 (enum α).1.2.2
      hM_not_assoc hAss_ht (hprevF_card α IH) hT_aleph0 hcard
    ⟨h.choose, prev, h.choose_spec.1, h.choose_spec.2.2.2.2,
      h.choose_spec.2.2.2.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
      le_trans h.choose_spec.1.card_le
        (max_le (le_max_left ..) (hprevF_cb α IH))⟩
  let data : ∀ α : κ.ToType, RD α :=
    fun α => @WellFounded.fix κ.ToType RD (· < ·) wellFounded_lt hbuildF α
  let ring : κ.ToType → NSubring T := fun α => (data α).1
  -- prevF agrees with (data α).2.1 by WellFounded.fix_eq
  have hprevF_eq : ∀ (α : κ.ToType),
      (data α).2.1 = prevF α (fun γ hγ => data γ) :=
    fun α => congrArg (fun d => d.2.1) (WellFounded.fix_eq wellFounded_lt hbuildF α)
  -- At limits, `prev α` is the union of the earlier rings
  have hprev_limit : ∀ α : κ.ToType, ¬IsMin α → Order.IsSuccLimit α →
      (∀ ⦃β₁ β₂ : κ.ToType⦄, β₁ < α → β₂ < α → β₁ ≤ β₂ →
        (ring β₁).carrier ≤ (ring β₂).carrier) →
      (∀ ⦃β₁ β₂ : κ.ToType⦄, β₁ < α → β₂ < α → β₁ ≤ β₂ →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier)) →
      (∀ β, β < α → (ring β).carrier ≤ (data α).2.1.carrier) ∧
      (∀ β, β < α → ∀ (r : (ring β).carrier), Prime r →
        ∀ (hmem : (r : T) ∈ (data α).2.1.carrier),
          Prime (⟨(r : T), hmem⟩ : (data α).2.1.carrier)) := by
    intro α hmin hlim hmono hprimes
    have hgood_α : IH_good α (fun γ hγ => data γ) := ⟨hmono, hprimes⟩
    have h_eq : (data α).2.1 =
        (mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
          (fun β hβ => (data β).2.2.2.2.2.2.2)).1 := by
      rw [hprevF_eq α]
      simp only [prevF, dite_eq_right hmin, dite_eq_left hlim, dite_eq_left hgood_α]
    rw [h_eq]
    exact ⟨(mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
        (fun β hβ => (data β).2.2.2.2.2.2.2)).2.2.2.1,
      (mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
        (fun β hβ => (data β).2.2.2.2.2.2.2)).2.2.2.2⟩
  -- At successors `succ γ`, `prev α` is the ring at `γ`
  have hprev_succ : ∀ α : κ.ToType, ¬IsMin α → ¬Order.IsSuccLimit α →
      ∃ γ, γ < α ∧ (∀ β, β < α → β ≤ γ) ∧ (data α).2.1 = ring γ := by
    intro α hmin hlim
    let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
    let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
    refine ⟨hγ_ex.choose,
      lt_of_lt_of_eq (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1) hγ_ex.choose_spec.2,
      fun β hβ => (Order.lt_succ_iff_of_not_isMax hγ_ex.choose_spec.1).mp
        (by rw [hγ_ex.choose_spec.2]; exact hβ), ?_⟩
    rw [hprevF_eq α]
    simp only [prevF, dite_eq_right hmin, dite_eq_right hlim]
    rfl
  refine transfinite_result_of_family ring (fun α => (data α).2.1) (fun α => (data α).2.2.1)
    (chain_le_prev_and_primes ring (fun α => (data α).2.1) (fun α => (data α).2.2.1)
      hprev_limit hprev_succ)
    (fun α => (data α).2.2.2.2.1) ?_ ?_ ?_
  · -- Surjectivity: use enum to find α covering each residue class ℓ
    intro ℓ
    have hq₀ : (IsLocalRing.maximalIdeal T).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal (R := T)).isPrime
    let v : V := (⟨IsLocalRing.maximalIdeal T, hq₀, hM_ne_bot⟩, ℓ)
    let α := enum.symm v
    obtain ⟨c, hc⟩ := (data α).2.2.2.2.2.1
    have : (enum α).2 = ℓ := by simp [α, v]
    exact ⟨α, c, this ▸ hc⟩
  · -- Prime catching: use enum to find α covering each nonzero prime q
    intro q hq hq_ne
    let v : V := (⟨q, hq, hq_ne⟩, 0)
    let α := enum.symm v
    obtain ⟨t, ht_q, ht_ne⟩ := (data α).2.2.2.2.2.2.1
    have : (enum α).1.1 = q := by simp [α, v]
    exact ⟨α, t, this ▸ ht_q, ht_ne⟩
  · rw [Cardinal.mk_ord_toType]
    calc Cardinal.mk V ≤ Cardinal.mk T := hV_card
      _ = Cardinal.mk (IsLocalRing.ResidueField T) := hcard
      _ ≤ max Cardinal.aleph0 _ := le_max_right _ _
end
