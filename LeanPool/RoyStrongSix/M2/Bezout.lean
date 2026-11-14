/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.Algebra.Module.Submodule.Union

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.BridgeLow

/-!
# Philippon's upper bound for `H` (Roy, DALAG Thm 8.4)

Let `I = (l)` be a complete intersection in `A = K[σ]` (`ht I = length l`). Let `F` be a set of
polynomials of block degree `≤ D`, and `J = I + (F) ≠ (1)`. Then

  `deg_D J ≤ deg_D I`   (`bezout`),

where `deg_D` is the degree in the data of `hfun` (Roy's `H(·; D)`).

Proof (Roy): build complete intersections `I = I_0 ⊆ I_1 ⊆ ⋯ ⊆ I_s ⊆ J` with `ht I_k = ht I + k`.
At each
step choose `P ∈ span_K F`, of block degree `≤ D`, outside every associated prime of `I_k`. This is
possible because `I_k` is unmixed (Macaulay) of height `< ht J`, and a vector space over an infinite
field is not a finite union of proper subspaces. Then `P` is a non-zero-divisor. The section
inequality
(Lemma 8.5), with the dimension drop pinned by `hdim + ht = card σ`, keeps the degree from
increasing.
At `ht I_s = ht J` the dimensions agree and `I_s ⊆ J` finishes the proof.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (β : σ → ι) (D : ι → ℕ)

local notation "A" => MvPolynomial σ K

omit [DecidableEq σ] in
omit [Fintype σ] in
/-- **Avoidance for a span.** If each associated prime of `I` misses some element of `F`, some
`K`-linear combination of `F` misses all of them. -/
theorem exists_avoid_span [Finite σ] [Infinite K] {I : Ideal A} {F : Set A}
    (hF : ∀ q ∈ associatedPrimes A (A ⧸ I), ∃ f ∈ F, f ∉ q) :
    ∃ P ∈ Submodule.span K F, ∀ q ∈ associatedPrimes A (A ⧸ I), P ∉ q := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let V := Submodule.span K F
  let S := associatedPrimes A (A ⧸ I)
  have : Finite S := (associatedPrimes.finite A (A ⧸ I)).to_subtype
  let p : S → Submodule K V := fun q => (q.1.restrictScalars K).comap V.subtype
  have hp : ∀ q, p q ≠ ⊤ := fun q h => by
    obtain ⟨f, hfF, hfq⟩ := hF q.1 q.2
    have : (⟨f, Submodule.subset_span hfF⟩ : V) ∈ p q := h ▸ Submodule.mem_top
    exact hfq this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨x.1, x.2, fun q hq => hx ⟨q, hq⟩⟩

omit [DecidableEq σ] [Fintype ι] in
/-- The bridge with a known height. -/
theorem hdim_of_height [Finite ι] (hD : ∀ i, 1 ≤ D i) {L : Ideal A} (hL : L ≠ ⊤) {h : ℕ}
    (hh : L.height = h) : (hdata β D K L).1 + h = Fintype.card σ := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  have := hdim_add_height_eq β D hD hL
  rw [hh] at this
  exact_mod_cast this

omit [DecidableEq σ] [Fintype ι] in
/-- **Roy, Theorem 8.4.** -/
theorem bezout [Finite ι] [Infinite K] (hD : ∀ i, 1 ≤ D i) {l : List A}
    (hl : (Ideal.ofList l).height = l.length) {F : Set A} (hFD : F ⊆ FLE K β D)
    (hJ : Ideal.ofList l ⊔ Ideal.span F ≠ ⊤) :
    (hdata β D K (Ideal.ofList l ⊔ Ideal.span F)).2 ≤ (hdata β D K (Ideal.ofList l)).2 := by
  classical
  let : DecidableEq σ := Classical.decEq σ
  let : Fintype ι := Fintype.ofFinite ι
  set J := Ideal.ofList l ⊔ Ideal.span F
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hJ)
  have hJdim := hdim_of_height β D hD hJ hN.symm
  have hlJ : Ideal.ofList l ≤ J := le_sup_left
  have hlN : l.length ≤ N := by
    have := Ideal.height_mono hlJ
    rw [hl, ← hN] at this
    exact_mod_cast this
  have hspanJ : (Submodule.span K F) ≤ J.restrictScalars K := by
    rw [Submodule.span_le]
    intro f hf
    exact Ideal.mem_sup_right (Ideal.subset_span hf)
  have hspanD : Submodule.span K F ≤ FLE K β D := Submodule.span_le.mpr hFD
  -- the chain
  have chain : ∀ k, l.length + k ≤ N → ∃ rs : List A, Ideal.ofList l ≤ Ideal.ofList rs ∧
      Ideal.ofList rs ≤ J ∧ rs.length = l.length + k ∧
      (Ideal.ofList rs).height = rs.length ∧
      (hdata β D K (Ideal.ofList rs)).2 ≤ (hdata β D K (Ideal.ofList l)).2 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨l, le_rfl, hlJ, rfl, hl, le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨rs, hl_rs, hrsJ, hlen, hht, hdeg⟩ := ih (by omega)
      set Ik := Ideal.ofList rs
      have hIk : Ik ≠ ⊤ := ne_top_of_le_ne_top hJ hrsJ
      have hunmix := ofList_isUnmixed K hht
      -- every associated prime misses some element of `F`
      have hF : ∀ q ∈ associatedPrimes A (A ⧸ Ik), ∃ f ∈ F, f ∉ q := by
        intro q hq
        by_contra hcon
        push Not at hcon
        have hqI : Ik ≤ q := by
          have := (AssociatedPrimes.mem_iff.mp hq).annihilator_le
          rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at this
        have hJq : J ≤ q := sup_le (hl_rs.trans hqI) (Ideal.span_le.mpr hcon)
        have h1 : q.height = Ik.height := hunmix.height_eq hq
        have h2 := Ideal.height_mono hJq
        rw [h1, hht, hlen, ← hN] at h2
        norm_cast at h2
        omega
      obtain ⟨P, hPspan, hPass⟩ := exists_avoid_span hF
      have hPD : P ∈ FLE K β D := hspanD hPspan
      have hPJ : P ∈ J := hspanJ hPspan
      have hnzd := nzd_of_not_mem_ass hPass
      have hmin : ∀ q ∈ Ik.minimalPrimes, P ∉ q := fun q hq => by
        rw [← associatedPrimes_eq_minimalPrimes_of_isUnmixed hunmix] at hq
        exact hPass q hq
      have heq : Ideal.ofList (rs ++ [P]) = Ik ⊔ Ideal.span {P} := by
        rw [Ideal.ofList_append, Ideal.ofList_singleton]
      have hnewJ : Ideal.ofList (rs ++ [P]) ≤ J := by
        rw [heq]; exact sup_le hrsJ (Ideal.span_le.mpr (by simpa using hPJ))
      have hne : Ideal.ofList (rs ++ [P]) ≠ ⊤ := ne_top_of_le_ne_top hJ hnewJ
      have hht' := height_append hht hmin hne
      refine ⟨rs ++ [P], hl_rs.trans (by rw [heq]; exact le_sup_left), hnewJ,
        by simp [hlen]; ring, hht', ?_⟩
      -- degrees: the dimension drops by exactly one, so the degree does not increase
      have hdk := hdim_of_height β D hD hIk (h := l.length + k) (hht.trans (by rw [hlen]))
      have hdk1 := hdim_of_height β D hD hne (h := l.length + k + 1)
        (hht'.trans (by simp [hlen]))
      have hspec := hdata_spec β D K hIk
      obtain ⟨b, hb⟩ : ∃ b, (hdata β D K Ik).1 = b + 1 := ⟨(hdata β D K Ik).1 - 1, by omega⟩
      rw [hb] at hspec
      have hsec : ∀ t, (hfun β D K (Ideal.ofList (rs ++ [P])) (t + 1) : ℤ) ≤
          hfun β D K Ik (t + 1) - hfun β D K Ik t := fun t => by
        rw [heq]; exact hfun_section β D K hPD hnzd t
      rcases HasData.of_le_Δ hspec (hfun_evPoly β D K _) (fun _ => by positivity) hsec with
        hz | ⟨b', d, hd, hcmp⟩
      · exfalso
        obtain ⟨k0, hk0⟩ := hz.exists
        have := one_le_hfun β D K hne k0
        omega
      · have hd' := hdata_eq β D K hne hd
        have hb' : b' = b := by
          have : (hdata β D K (Ideal.ofList (rs ++ [P]))).1 = b' := by rw [hd']
          omega
        rw [hd']
        rcases hcmp with h | ⟨-, h⟩
        · omega
        · exact h.trans hdeg
  -- the end of the chain
  obtain ⟨rs, -, hrsJ, hlen, hht, hdeg⟩ := chain (N - l.length) (by omega)
  have hIs : Ideal.ofList rs ≠ ⊤ := ne_top_of_le_ne_top hJ hrsJ
  have hsdim := hdim_of_height β D hD hIs hht
  rw [hlen] at hsdim
  rcases hdata_le_of_le β D K hrsJ hJ with h | ⟨-, h⟩
  · omega
  · exact h.trans hdeg

end StrongSix.M2

end LeanPool
