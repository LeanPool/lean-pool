/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Overfull.Basic

/-!
# Multifans (Stiebitz–Scheide–Toft–Favrholdt, Theorem 2.1; CCJS Lemma 2.2)

Let `G` be of class two and `c` a colouring of `G − x y₀` with `Δ(G)` colours. A *multifan* at
`x` is a sequence `y₀, y₁, …, y_{L−1}` of distinct neighbours of `x` such that the colour of
every edge `x yᵢ`, `i ≥ 1`, is missing at some earlier `yⱼ` (`IsMultifan`).

`multifan_elementary`: the vertices `x, y₀, …, y_{L−1}` are elementary (no colour is missing at
two of them), and for every colour `α` missing at `x` and `β` missing at `yᵢ`, the vertices `x`
and `yᵢ` lie in the same `(α, β)`-Kempe component.

Proof (simultaneous induction on `L`): a colour missing at `x` and at some `yᵢ` lets the edge
`x y₀` be coloured after rotating the linear fan from `y₀` to `yᵢ` (`fan_rotate` of the Vizing
entry), contradicting class two; a colour missing at two fan vertices, or a failure of linkage,
is reduced to the first case by a Kempe swap on the component of the later vertex.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A multifan at `x` with respect to the uncoloured edge `x y₀`, of length `L`. -/
structure IsMultifan {k : ℕ} (c : PEC G (Fin k)) (x : V) (L : ℕ) (y : ℕ → V) : Prop where
  pos : 0 < L
  uncol : c.col x (y 0) = none
  adj : ∀ i < L, G.Adj x (y i)
  inj : ∀ i < L, ∀ j < L, y i = y j → i = j
  step : ∀ i, 0 < i → i < L → ∃ j < i, ∃ γ, c.col x (y i) = some γ ∧ c.IsFree (y j) γ

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem IsMultifan.prefix {k : ℕ} {c : PEC G (Fin k)} {x : V} {L m : ℕ} {y : ℕ → V}
    (hF : IsMultifan c x L y) (hm : m ≤ L) (hm0 : 0 < m) : IsMultifan c x m y := by
  classical
  exact ⟨hm0, hF.uncol, fun i hi => hF.adj i (by omega),
    fun i hi j hj h => hF.inj i (by omega) j (by omega) h,
    fun i hi hi' => hF.step i hi (by omega)⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Every vertex of a multifan is joined to a linear (Vizing) fan from `y₀`. -/
theorem IsMultifan.exists_linear {k : ℕ} {c : PEC G (Fin k)} {x : V} {L : ℕ} {y : ℕ → V}
    (hF : IsMultifan c x L y) :
    ∀ q < L, ∃ n f, c.IsFan x (y 0) n f ∧ f n = y q ∧ ∀ i ≤ n, ∃ j ≤ q, f i = y j := by
  classical
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · refine ⟨0, fun _ => y 0, ⟨rfl, hF.uncol, fun i _ => hF.adj 0 hF.pos, ?_, ?_⟩, rfl,
        fun i _ => ⟨0, le_rfl, rfl⟩⟩
      · intro i hi j hj _
        omega
      · intro i hi
        omega
    · obtain ⟨j, hjq, γ, hγ, hfree⟩ := hF.step q hq0 hq
      obtain ⟨n, f, hfan, hfn, hmem⟩ := ih j hjq (by omega)
      refine ⟨n + 1, fun i => if i ≤ n then f i else y q, ⟨?_, hfan.uncoloured, ?_, ?_, ?_⟩,
        by simp, ?_⟩
      · simp [hfan.start]
      · intro i hi
        by_cases h : i ≤ n
        · simp only [h, ite_true]
          exact hfan.adj i h
        · simp only [h, ite_false]
          exact hF.adj q hq
      · intro i hi i' hi' h
        by_cases h1 : i ≤ n <;> by_cases h2 : i' ≤ n <;> simp only [h1, h2, ite_true,
            ite_false] at h
        · exact hfan.inj i h1 i' h2 h
        · obtain ⟨j', hj', hfj⟩ := hmem i h1
          rw [hfj] at h
          have := hF.inj j' (by omega) q hq h
          omega
        · obtain ⟨j', hj', hfj⟩ := hmem i' h2
          rw [hfj] at h
          have := hF.inj q hq j' (by omega) h
          omega
        · omega
      · intro i hi
        by_cases h : i + 1 ≤ n
        · obtain ⟨δ, hδ, hδf⟩ := hfan.step i (by omega)
          refine ⟨δ, ?_, ?_⟩
          · simp only [h, ite_true]
            exact hδ
          · simp only [show i ≤ n by omega, ite_true]
            exact hδf
        · have hin : i = n := by omega
          subst hin
          refine ⟨γ, ?_, ?_⟩
          · simp only [h, ite_false]
            exact hγ
          · simp only [le_refl, ite_true, hfn]
            exact hfree
      · intro i hi
        by_cases h : i ≤ n
        · obtain ⟨j', hj', hfj⟩ := hmem i h
          exact ⟨j', by omega, by simp only [h, ite_true]; exact hfj⟩
        · exact ⟨q, le_rfl, by simp [h]⟩

omit [DecidableEq V] in
/-- **Rotation.** In a class-two graph, no colour is missing both at `x` and at a vertex of a
multifan at `x`. -/
theorem IsMultifan.not_common_x (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {x : V}
    {L : ℕ} {y : ℕ → V} (hcm : IsColMinus c x (y 0)) (hF : IsMultifan c x L y) {q : ℕ}
    (hq : q < L) {γ : Fin G.maxDegree} (hx : c.IsFree x γ) (hy : c.IsFree (y q) γ) : False := by
  classical
  obtain ⟨n, f, hfan, hfn, -⟩ := hF.exists_linear q hq
  obtain ⟨c', hext, hcol⟩ := fan_rotate x (y 0) f n c γ hfan hx (hfn ▸ hy)
  refine not_total_of_classTwo hG c' fun u v huv => ?_
  by_cases h : s(u, v) = s(x, y 0)
  · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcol
    · rw [c'.col_symm]
      exact hcol
  · exact hext u v (hcm.total u v huv h)

omit [DecidableEq V] in
/-- At an endpoint of the uncoloured edge some colour is missing. -/
theorem IsColMinus.exists_free_left {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) : ∃ γ, c.IsFree a γ := by
  classical
  by_contra hcon
  push Not at hcon
  simp only [IsFree, not_forall, not_not] at hcon
  choose g hg using hcon
  have hmem : ∀ γ ∈ (univ : Finset (Fin G.maxDegree)), g γ ∈ (G.neighborFinset a).erase b := by
    intro γ _
    refine mem_erase.2 ⟨fun h => ?_, (mem_neighborFinset _ _ _).2 (c.col_adj (hg γ))⟩
    have := hg γ
    rw [h, hcm.uncol] at this
    simp at this
  have hinj : Set.InjOn g (univ : Finset (Fin G.maxDegree)) := by
    intro γ₁ _ γ₂ _ h
    exact Option.some_injective _ (by rw [← hg γ₁, ← hg γ₂, h])
  have hcard := card_le_card_of_injOn g hmem hinj
  rw [card_univ, Fintype.card_fin, card_erase_of_mem ((mem_neighborFinset _ _ _).2 hcm.adj),
    card_neighborFinset_eq_degree] at hcard
  have := G.degree_le_maxDegree a
  have : 0 < G.degree a := G.degree_pos_iff_exists_adj a |>.2 ⟨b, hcm.adj⟩
  omega

/-! ### Kempe swaps preserve multifans -/

omit [DecidableEq V] in
theorem kempeSwap_isColMinus {c : PEC G (Fin G.maxDegree)} {x z : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x z) {w : V} (hxw : ¬ (c.kempeGraph α β).Reachable w x) :
    IsColMinus (c.kempeSwap α β w) x z := by
  classical
  exact ⟨hcm.adj, by rw [kempeSwap_col, kempeSwapFun_of_not_reachable c α β hxw z, hcm.uncol],
    fun u v huv hne => extends_kempeSwap c α β w u v (hcm.total u v huv hne)⟩

omit [DecidableEq V] in
/-- Swapping `α, β` on the Kempe component of the last vertex `w = y (m − 1)` of a multifan of
length `m` keeps it a multifan, provided `x` is not in the component and the earlier vertices in
the component miss neither `α` nor `β`. -/
theorem IsMultifan.kempeSwap {c : PEC G (Fin G.maxDegree)} {x : V} {m : ℕ} {y : ℕ → V}
    (hF : IsMultifan c x m y) {α β : Fin G.maxDegree}
    (hxw : ¬ (c.kempeGraph α β).Reachable (y (m - 1)) x)
    (hprev : ∀ j < m - 1, (c.kempeGraph α β).Reachable (y (m - 1)) (y j) →
      ¬ c.IsFree (y j) α ∧ ¬ c.IsFree (y j) β) :
    IsMultifan (c.kempeSwap α β (y (m - 1))) x m y := by
  classical
  have hcolx : ∀ v, (c.kempeSwap α β (y (m - 1))).col x v = c.col x v := fun v => by
    rw [kempeSwap_col, kempeSwapFun_of_not_reachable c α β hxw v]
  refine ⟨hF.pos, by rw [hcolx]; exact hF.uncol, hF.adj, hF.inj, fun i hi0 hi => ?_⟩
  obtain ⟨j, hji, γ, hγ, hfree⟩ := hF.step i hi0 hi
  refine ⟨j, hji, γ, by rw [hcolx]; exact hγ, ?_⟩
  by_cases hr : (c.kempeGraph α β).Reachable (y (m - 1)) (y j)
  · rw [isFree_kempeSwap_of_reachable c α β hr]
    obtain ⟨hα, hβ⟩ := hprev j (by omega) hr
    have hγα : γ ≠ α := fun h => hα (h ▸ hfree)
    have hγβ : γ ≠ β := fun h => hβ (h ▸ hfree)
    rw [Equiv.swap_apply_of_ne_of_ne hγα hγβ]
    exact hfree
  · rw [isFree_kempeSwap_of_not_reachable c α β hr]
    exact hfree

/-! ### The multifan lemma -/

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Three distinct vertices each missing `α` or `β` are not all in one Kempe component. -/
theorem not_three_linked [Finite V] {k : ℕ} (c : PEC G (Fin k)) {α β : Fin k} {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : c.IsFree u α ∨ c.IsFree u β) (hv : c.IsFree v α ∨ c.IsFree v β)
    (hw : c.IsFree w α ∨ c.IsFree w β)
    (h1 : (c.kempeGraph α β).Reachable u v) (h2 : (c.kempeGraph α β).Reachable u w) : False := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hd : ∀ z, (c.kempeGraph α β).degree z ≤ 2 := fun z => by
    convert c.kempe_degree_le_two α β z
  have d1 : ∀ {z}, (c.IsFree z α ∨ c.IsFree z β) → (c.kempeGraph α β).degree z ≤ 1 := by
    rintro z (h | h)
    · convert c.kempe_degree_le_one_of_isFree (Or.inl rfl) h
    · convert c.kempe_degree_le_one_of_isFree (Or.inr rfl) h
  exact no_three_endpoints hd huv huw hvw (d1 hu) (d1 hv) (d1 hw) h1 h2

omit [DecidableEq V] in
/-- **The multifan lemma** (Stiebitz–Scheide–Toft–Favrholdt, Theorem 2.1; CCJS Lemma 2.2).
In a class-two graph, for a colouring `c` of `G − x y₀` with `Δ(G)` colours and a multifan
`y₀, …, y_{L−1}` at `x`: (a) no colour is missing at `x` and at a fan vertex, (a') no colour is
missing at two distinct fan vertices, and (b) for `α` missing at `x` and `β` missing at `yᵢ`,
`x` and `yᵢ` are `(α, β)`-linked. -/
theorem multifan_elementary (hG : IsClassTwo G) :
    ∀ (L : ℕ) (c : PEC G (Fin G.maxDegree)) (x : V) (y : ℕ → V), IsColMinus c x (y 0) →
      IsMultifan c x L y →
        (∀ i < L, ∀ γ, c.IsFree x γ → ¬ c.IsFree (y i) γ) ∧
        (∀ i < L, ∀ j < L, i ≠ j → ∀ γ, c.IsFree (y i) γ → ¬ c.IsFree (y j) γ) ∧
        (∀ i < L, ∀ α β, c.IsFree x α → c.IsFree (y i) β →
          (c.kempeGraph α β).Reachable x (y i)) := by
  classical
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro c x y hcm hF
    -- (a): rotation
    have hA : ∀ i < L, ∀ γ, c.IsFree x γ → ¬ c.IsFree (y i) γ :=
      fun i hi γ hx hy => hF.not_common_x hG hcm hi hx hy
    -- (a'): two fan vertices
    have hA' : ∀ i < L, ∀ j < L, i ≠ j → ∀ γ, c.IsFree (y i) γ → ¬ c.IsFree (y j) γ := by
      have key : ∀ i < L, ∀ j < i, ∀ γ, c.IsFree (y i) γ → ¬ c.IsFree (y j) γ := by
        intro i hi j hji γ hyi hyj
        obtain ⟨β, hβ⟩ := hcm.exists_free_left
        have hβγ : β ≠ γ := fun h => hA j (by omega) γ (h ▸ hβ) hyj
        -- the prefix `y₀ … y_{i−1}` is elementary and linked
        have hFi := hF.prefix (m := i) (by omega) (by omega)
        obtain ⟨hAi, hA'i, hBi⟩ := ih i hi c x y hcm hFi
        have hlink : (c.kempeGraph β γ).Reachable x (y j) := hBi j hji β γ hβ hyj
        have hxi : x ≠ y i := (hF.adj i hi).ne
        have hxj : x ≠ y j := (hF.adj j (by omega)).ne
        have hji' : y j ≠ y i := fun h => by
          have := hF.inj j (by omega) i hi h
          omega
        have hnr : ¬ (c.kempeGraph β γ).Reachable (y i) x := fun h =>
          not_three_linked c hxj hxi hji' (Or.inl hβ) (Or.inr hyj) (Or.inr hyi) hlink h.symm
        -- swap on the component of `y i`, keeping the prefix `y₀ … y_i`
        have hFi1 := hF.prefix (m := i + 1) (by omega) (by omega)
        have hsw := hFi1.kempeSwap (α := β) (β := γ) (by simpa using hnr) (by
          intro q hq hr
          simp only [Nat.add_sub_cancel] at hr hq
          refine ⟨hAi q hq β hβ, fun hqγ => ?_⟩
          by_cases hqj : q = j
          · subst hqj
            exact hnr (hr.trans hlink.symm)
          · exact hA'i q hq j hji hqj γ hqγ hyj)
        simp only [Nat.add_sub_cancel] at hsw
        have hcm' := kempeSwap_isColMinus (α := β) (β := γ) hcm (w := y i) hnr
        have hx' : (c.kempeSwap β γ (y i)).IsFree x β := by
          rw [isFree_kempeSwap_of_not_reachable c β γ (fun h => hnr h)]
          exact hβ
        have hyi' : (c.kempeSwap β γ (y i)).IsFree (y i) β := by
          rw [isFree_kempeSwap_of_reachable c β γ (Reachable.refl _), Equiv.swap_apply_left]
          exact hyi
        exact hsw.not_common_x hG hcm' (Nat.lt_succ_self i) hx' hyi'
      intro i hi j hj hij γ h1 h2
      rcases lt_or_gt_of_ne hij with h | h
      · exact key j hj i h γ h2 h1
      · exact key i hi j h γ h1 h2
    refine ⟨hA, hA', fun i hi α β hα hβ => ?_⟩
    -- (b): linkage
    by_contra hnr
    have hαβ : α ≠ β := fun h => hA i hi α hα (h ▸ hβ)
    have hnr' : ¬ (c.kempeGraph α β).Reachable (y i) x := fun h => hnr h.symm
    have hFi1 := hF.prefix (m := i + 1) (by omega) (by omega)
    have hsw := hFi1.kempeSwap (α := α) (β := β) (by simpa using hnr') (by
      intro q hq _
      simp only [Nat.add_sub_cancel] at hq
      exact ⟨hA q (by omega) α hα, fun hq' => hA' q (by omega) i hi (by omega) β hq' hβ⟩)
    simp only [Nat.add_sub_cancel] at hsw
    have hcm' := kempeSwap_isColMinus (α := α) (β := β) hcm (w := y i) hnr'
    have hx' : (c.kempeSwap α β (y i)).IsFree x α := by
      rw [isFree_kempeSwap_of_not_reachable c α β hnr']
      exact hα
    have hyi' : (c.kempeSwap α β (y i)).IsFree (y i) α := by
      rw [isFree_kempeSwap_of_reachable c α β (Reachable.refl _), Equiv.swap_apply_left]
      exact hβ
    exact hsw.not_common_x hG hcm' (Nat.lt_succ_self i) hx' hyi'
end Overfull

end LeanPool.BalancedEdgeColourings
