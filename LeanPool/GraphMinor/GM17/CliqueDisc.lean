/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CliqueSphere

/-!
# A clique of nodes lies in one disc

This file proves the surface part of Claim (1) of the proof of (12.2) of Graph Minors XVII (page
198). Let `M` be a set of at least three nodes, any two on a common cell. Every normal `O`-arc with
at most three nodes bounds a disc with a property `P` (in the paper, "`α(Δ)` is small"), and no four
such discs contain all cells.

As in the paper we take a circuit of length 3 on `M` with a maximal disc, and show `M` lies in this
disc (`clique_disc`). If `m₀ ∈ M` lies outside, the three circuits through `m₀` have discs that do
not include the first disc, so the four discs have the first one's inside to itself. Then the four
discs form a sphere, which is all of `Σ`, so they contain all cells (`four_discs_cover`), a
contradiction.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

omit [TopologicalSpace S] [T2Space S] in
/-- Six pairs of four distinct points are distinct. -/
theorem six_pairs_inj {a b c m : S} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hma : m ≠ a)
  (hmb : m ≠ b) (hmc : m ≠ c) (i j : Fin 6) (hij : i ≠ j)
    (he : (![{a, b}, {b, c}, {c, a}, {m, a}, {m, b}, {m, c}] : Fin 6 → Set S) i
      = ![{a, b}, {b, c}, {c, a}, {m, a}, {m, b}, {m, c}] j) : False := by
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have ham := hma.symm
  have hbm := hmb.symm
  have hcm := hmc.symm
  fin_cases i <;> fin_cases j <;> first
    | exact hij rfl
    | simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
        Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Set.pair_eq_pair_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first | exact absurd h1 ‹_› | exact absurd h2 ‹_›

private theorem triangle_is_normal_arc
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {Γ : Painting S}
    {M : Set S}
    (L : Set S → Set S)
    (𝓟 : Set (Set S))
    (hline : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → IsLineWithEnds (L {a, b}) a b)
    (hpp : ∀ {a b : S}, a ∈ M → b ∈ M → a ≠ b → {a, b} ∈ 𝓟)
    (hpN : ∀ p ∈ 𝓟, p ⊆ Γ.N)
    (hLU : ∀ p ∈ 𝓟, L p ∩ Γ.U ⊆ p)
    (hLN : ∀ p ∈ 𝓟, L p ∩ Γ.N ⊆ p)
    (hcom : ∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → L p ∩ L q ⊆ p ∩ q) :
    let E : S → S → Set S := fun x y => L {x, y}
    let Φ : S → S → S → Set S := fun x y z => E x y ∪ E y z ∪ E z x
    (∀ {a b c d : S}, a ≠ c → a ≠ d → ({a, b} : Set S) ≠ {c, d}) →
    ∀ {a : S},
    ∀ {b : S},
    ∀ {c : S},
    (a ∈ M) →
    (b ∈ M) →
    (c ∈ M) →
    (a ≠ b) →
    (a ≠ c) →
    (b ≠ c) →
    IsOArc (Φ a b c) ∧ Γ.IsNormal (Φ a b c) ∧ (Φ a b c ∩ Γ.N).ncard ≤ 3 := by
  intro E Φ hpne a b c ha hb hc hab hac hbc
  have hp1 := hpp ha hb hab
  have hp2 := hpp hb hc hbc
  have hp3 := hpp hc ha hac.symm
  have hne12 : ({a, b} : Set S) ≠ {b, c} := hpne hab hac
  have hne13 : ({b, a} : Set S) ≠ {c, a} := hpne hbc hab.symm
  have hne23 : ({b, c} : Set S) ≠ {c, a} := hpne hbc hab.symm
  have hi1 : E a b ∩ E b c = {b} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨h1, h2⟩ := hcom _ hp1 _ hp2 hne12 hx
      rcases h1 with rfl | rfl
      · rcases h2 with h2 | h2
        · exact absurd h2 hab
        · exact absurd h2 hac
      · rfl
    · rintro x rfl
      exact ⟨(hline a ha x hb hab).right_mem, (hline x hb c hc hbc).left_mem⟩
  have hA : IsLineWithEnds (E a b ∪ E b c) a c := (hline a ha b hb hab).union
    (hline b hb c hc hbc) hi1
  have hB : IsLineWithEnds (E c a) a c := (hline c hc a ha hac.symm).symm
  have hi2 : (E a b ∪ E b c) ∩ E c a = {a, c} := by
    apply Subset.antisymm
    · rintro x ⟨h1 | h1, h2⟩
      · have h3 := hcom {a, b} hp1 {c, a} hp3 (by rw [pair_comm a b]; exact hne13) ⟨h1, h2⟩
        rcases h3.2 with rfl | rfl
        · exact .inr rfl
        · exact .inl rfl
      · have h3 := hcom _ hp2 _ hp3 hne23 ⟨h1, h2⟩
        rcases h3.2 with rfl | rfl
        · exact .inr rfl
        · exact .inl rfl
    · rintro x (rfl | rfl)
      · exact ⟨.inl (hline x ha b hb hab).left_mem, (hline c hc x ha hac.symm).right_mem⟩
      · exact ⟨.inr (hline b hb x hc hbc).right_mem, (hline x hc a ha hac.symm).left_mem⟩
  have hsub : Φ a b c ∩ Γ.N ⊆ {a, b, c} := by
    rintro x ⟨(h1 | h1) | h1, h2⟩
    · rcases hLN _ hp1 ⟨h1, h2⟩ with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
    · rcases hLN _ hp2 ⟨h1, h2⟩ with rfl | rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    · rcases hLN _ hp3 ⟨h1, h2⟩ with rfl | rfl
      · exact .inr (.inr rfl)
      · exact .inl rfl
  refine ⟨oArc_of_lines hA hB hi2, ?_, ?_⟩
  · rintro x ⟨(h1 | h1) | h1, h2⟩
    · exact hpN _ hp1 (hLU _ hp1 ⟨h1, h2⟩)
    · exact hpN _ hp2 (hLU _ hp2 ⟨h1, h2⟩)
    · exact hpN _ hp3 (hLU _ hp3 ⟨h1, h2⟩)
  · have hf : ({a, b, c} : Set S).Finite := by simp
    refine (ncard_le_ncard hsub hf).trans ?_
    exact (ncard_insert_le _ _).trans (by rw [ncard_pair hbc])

private theorem tetrahedral_disc_boundaries
    {S : Type}
    [TopologicalSpace S]
    (E : S → S → Set S)
    (hEc : ∀ (x y : S), E x y = E y x) :
    let Φ : S → S → S → Set S := fun x y z => E x y ∪ E y z ∪ E z x
    ∀ (𝒯 : Set (S × S × S)),
    ∀ (dsc : S × S × S → Set S),
    (∀ t ∈ 𝒯, discBd (dsc t) = Φ t.1 t.2.1 t.2.2) →
    ∀ (a : S),
    ∀ (b : S),
    ∀ (c : S),
    ∀ (m : S),
    ∀ (Δ : Set S),
    (discBd Δ = Φ a b c) →
    ((m, b, c) ∈ 𝒯) →
    ((a, m, c) ∈ 𝒯) →
    ((a, b, m) ∈ 𝒯) →
    ∀ (e : Fin 6 → Set S),
    e 0 = E a b → e 1 = E b c → e 2 = E c a →
    e 3 = E m a → e 4 = E m b → e 5 = E m c →
    let D : Fin 4 → Set S := ![Δ, dsc (m, b, c), dsc (a, m, c), dsc (a, b, m)]
    (∀ (x y z : Fin 6), ⋃ i ∈ ({x, y, z} : Finset (Fin 6)), e i = e x ∪ e y ∪ e z) →
    ∀ (k : Fin 4),
    discBd (D k) = ⋃ i ∈ circuitChords k, e i := by
  intro Φ 𝒯 dsc hdB a b c m Δ hΔb ht1 ht2 ht3 e he₀ he₁ he₂ he₃ he₄ he₅ D hunion k
  fin_cases k
  · change discBd Δ = ⋃ i ∈ ({0, 1, 2} : Finset (Fin 6)), e i
    rw [hunion, hΔb, he₀, he₁, he₂]
  · change discBd (dsc (m, b, c)) = ⋃ i ∈ ({4, 1, 5} : Finset (Fin 6)), e i
    rw [hunion, hdB _ ht1, he₄, he₁, he₅]
    change E m b ∪ E b c ∪ E c m = E m b ∪ E b c ∪ E m c
    rw [hEc c m]
  · change discBd (dsc (a, m, c)) = ⋃ i ∈ ({3, 5, 2} : Finset (Fin 6)), e i
    rw [hunion, hdB _ ht2, he₃, he₅, he₂]
    change E a m ∪ E m c ∪ E c a = E m a ∪ E m c ∪ E c a
    rw [hEc a m]
  · change discBd (dsc (a, b, m)) = ⋃ i ∈ ({0, 4, 3} : Finset (Fin 6)), e i
    rw [hunion, hdB _ ht3, he₀, he₄, he₃]
    change E a b ∪ E b m ∪ E m a = E a b ∪ E m b ∪ E m a
    rw [hEc b m]

private theorem disc_side_vertex_on_boundary_or_off_disc
    {S : Type}
    [TopologicalSpace S]
    {Γ : Painting S}
    {M : Set S}
    (hM : M ⊆ Γ.N)
    (L : Set S → Set S)
    (hline : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → IsLineWithEnds (L {a, b}) a b) :
    let E : S → S → Set S := fun x y => L {x, y}
    let Φ : S → S → S → Set S := fun x y z => E x y ∪ E y z ∪ E z x
    ∀ (𝒯 : Set (S × S × S)),
    ∀ (dsc : S × S × S → Set S),
    (∀ t ∈ 𝒯, discBd (dsc t) = Φ t.1 t.2.1 t.2.2) →
    ∀ (a : S),
    ∀ (b : S),
    ∀ (c : S),
    (a ∈ M) →
    (b ∈ M) →
    (c ∈ M) →
    (a ≠ b) →
    (a ≠ c) →
    (b ≠ c) →
    ∀ (m : S),
    (m ∈ M) →
    ∀ (Δ : Set S),
    (a ∈ discBd Δ) →
    (b ∈ discBd Δ) →
    (c ∈ discBd Δ) →
    (m ≠ a) →
    (m ≠ b) →
    (m ≠ c) →
    ((m, b, c) ∈ 𝒯) →
    ((a, m, c) ∈ 𝒯) →
    ((a, b, m) ∈ 𝒯) →
    let e : Fin 6 → Set S := fun i => L ((![{a, b}, {b, c}, {c, a}, {m, a}, {m, b}, {m, c}] : Fin
      6 → Set S) i)
    let D : Fin 4 → Set S := ![Δ, dsc (m, b, c), dsc (a, m, c), dsc (a, b, m)]
    (∀ {z x y : S}, z ∈ Γ.N → z ≠ x → z ≠ y → x ∈ M → y ∈ M → x ≠ y → z ∉ E x y) →
    (∀ (k : Fin 4) (i : Fin 6), k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k → k =
      1 ∧ i = 3 ∨ k = 2 ∧ i = 4 ∨ k = 3 ∧ i = 5) →
    ∀ (k : Fin 4) (i : Fin 6), k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k → ∃ z ∈ e i, z ∈
      discBd (D 0) ∧ z ∉ discBd (D k) := by
  intro E Φ 𝒯 dsc hdB a b c ha hb hc hab hac hbc m hm Δ haΔ hbΔ hcΔ hma hmb hmc ht1 ht2 ht3 e D
    hnotN hcase k i hk hi0 hik
  rcases hcase k i hk hi0 hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨a, show a ∈ E m a from (hline m hm a ha hma).right_mem, haΔ, ?_⟩
    change a ∉ discBd (dsc (m, b, c))
    rw [hdB _ ht1]
    rintro ((h1 | h1) | h1)
    · exact hnotN (hM ha) hma.symm hab hm hb hmb h1
    · exact hnotN (hM ha) hab hac hb hc hbc h1
    · exact hnotN (hM ha) hac hma.symm hc hm hmc.symm h1
  · refine ⟨b, show b ∈ E m b from (hline m hm b hb hmb).right_mem, hbΔ, ?_⟩
    change b ∉ discBd (dsc (a, m, c))
    rw [hdB _ ht2]
    rintro ((h1 | h1) | h1)
    · exact hnotN (hM hb) hab.symm hmb.symm ha hm hma.symm h1
    · exact hnotN (hM hb) hmb.symm hbc hm hc hmc h1
    · exact hnotN (hM hb) hbc hab.symm hc ha hac.symm h1
  · refine ⟨c, show c ∈ E m c from (hline m hm c hc hmc).right_mem, hcΔ, ?_⟩
    change c ∉ discBd (dsc (a, b, m))
    rw [hdB _ ht3]
    rintro ((h1 | h1) | h1)
    · exact hnotN (hM hc) hac.symm hbc.symm ha hb hab h1
    · exact hnotN (hM hc) hbc.symm hmc.symm hb hm hmb.symm h1
    · exact hnotN (hM hc) hmc.symm hac.symm hm ha hma h1

private theorem outside_vertex_chord_disjoint_of_disc
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {M : Set S}
    (hman : ∀ (x : S), IsManifoldPoint x)
    (L : Set S → Set S)
    (𝓟 : Set (Set S))
    (hline : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → IsLineWithEnds (L {a, b}) a b)
    (hdj : ∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → Disjoint (L p \ p) (L q))
    (hpp : ∀ {a b : S}, a ∈ M → b ∈ M → a ≠ b → {a, b} ∈ 𝓟) :
    let E : S → S → Set S := fun x y => L {x, y}
    let Φ : S → S → S → Set S := fun x y z => E x y ∪ E y z ∪ E z x
    (∀ {a b c d : S}, a ≠ c → a ≠ d → ({a, b} : Set S) ≠ {c, d}) →
    ∀ (a : S),
    ∀ (b : S),
    ∀ (c : S),
    (a ∈ M) →
    (b ∈ M) →
    (c ∈ M) →
    (a ≠ b) →
    (a ≠ c) →
    (b ≠ c) →
    ∀ (m : S),
    (m ∈ M) →
    ∀ (Δ : Set S),
    (IsClosedDisc Δ) →
    (discBd Δ = Φ a b c) →
    (m ∉ Δ) →
    (m ≠ a) →
    (m ≠ b) →
    (m ≠ c) →
    ∀ (y : S),
    (y ∈ M) →
    (m ≠ y) →
    Disjoint (E m y \ {m, y}) Δ := by
  intro E Φ hpne a b c ha hb hc hab hac hbc m hm Δ hΔD hΔb hmΔ hma hmb hmc y hy hne
  have hl := hline m hm y hy hne
  have hoffb : Disjoint (E m y \ {m, y}) (discBd Δ) := by
    rw [hΔb]
    refine disjoint_left.mpr fun x hx hxb => ?_
    have hp := hpp hm hy hne
    rcases hxb with (h1 | h1) | h1
    · exact disjoint_left.mp (hdj _ hp _ (hpp ha hb hab) (hpne hma hmb)) hx h1
    · exact disjoint_left.mp (hdj _ hp _ (hpp hb hc hbc) (hpne hmb hmc)) hx h1
    · exact disjoint_left.mp (hdj _ hp _ (hpp hc ha hac.symm) (hpne hmc hma)) hx h1
  rcases disc_dichotomy hman hΔD hl.isPreconnected_diff hoffb with h1 | h1
  · exact absurd (closure_minimal h1 hΔD.isClosed (hl.subset_closure_diff hl.left_mem)) hmΔ
  · exact h1

private theorem triangle_disc_avoids_original_interior
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {M : Set S}
    (hman : ∀ (x : S), IsManifoldPoint x)
    (E : S → S → Set S)
    (𝒯 : Set (S × S × S))
    (dsc : S × S × S → Set S)
    (hdD : ∀ t ∈ 𝒯, IsClosedDisc (dsc t))
    (a : S)
    (b : S)
    (c : S)
    (ha : a ∈ M)
    (hb : b ∈ M)
    (hc : c ∈ M)
    (m : S)
    (Δ : Set S)
    (hmax : ∀ ⦃j : S × S × S⦄, (fun x => x ∈ 𝒯) j → Δ ⊆ dsc j → dsc j ⊆ Δ)
    (hΔD : IsClosedDisc Δ)
    (hmΔ : m ∉ Δ)
    (haΔ : a ∈ discBd Δ)
    (hbΔ : b ∈ discBd Δ)
    (hcΔ : c ∈ discBd Δ)
    (hma : m ≠ a)
    (hmb : m ≠ b)
    (hmc : m ≠ c)
    (hintoff : ∀ y ∈ M, y ∈ discBd Δ → m ≠ y → Disjoint (discInt Δ) (E m y))
    (t' : S × S × S)
    (ht' : t' ∈ 𝒯)
    (hsub : discBd (dsc t') ⊆ discBd Δ ∪ E m a ∪ E m b ∪ E m c)
    (hmb' : m ∈ discBd (dsc t')) :
    Disjoint (discInt Δ) (dsc t') := by
  have hoff : Disjoint (discInt Δ) (discBd (dsc t')) := disjoint_left.mpr fun x hx hxb => by
    rcases hsub hxb with ((h1 | h1) | h1) | h1
    · exact hx.2 h1
    · exact disjoint_left.mp (hintoff a ha haΔ hma) hx h1
    · exact disjoint_left.mp (hintoff b hb hbΔ hmb) hx h1
    · exact disjoint_left.mp (hintoff c hc hcΔ hmc) hx h1
  rcases disc_dichotomy hman (hdD t' ht') hΔD.isPreconnected_discInt hoff with h1 | h1
  · have hsubΔ : Δ ⊆ dsc t' := hΔD.subset_closure_discInt.trans (closure_minimal h1
      (hdD t' ht').isClosed)
    exact absurd (hmax ht' hsubΔ (discBd_subset _ hmb')) hmΔ
  · exact h1

private theorem clique_chord_discs_cover
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    {Γ : Painting S}
    [ConnectedSpace S]
    (hS : IsSurface S)
    (L : Set S → Set S)
    (𝓟 : Set (Set S))
    (hreg : ∀ p ∈ 𝓟, ∃ r ∈ Γ.regions, L p \ p ⊆ r ∧ ∀ x ∈ L p \ p, IsChordSide (L p) (L '' 𝓟) x)
    (hdj : ∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → Disjoint (L p \ p) (L q))
    (hpN : ∀ p ∈ 𝓟, p ⊆ Γ.N)
    (Pp : Fin 6 → Set S) :
    let e : Fin 6 → Set S := fun i => L (Pp i)
    ∀ (D : Fin 4 → Set S),
    (∀ (i : Fin 6), Pp i ∈ 𝓟) →
    (∀ (i j : Fin 6), i ≠ j → Pp i ≠ Pp j) →
    (∀ (k : Fin 4), IsClosedDisc (D k)) →
    (∀ (k : Fin 4), discBd (D k) = ⋃ i ∈ circuitChords k, e i) →
    (∀ (k : Fin 4), k ≠ 0 → Disjoint (discInt (D 0)) (D k)) →
    (∀ p ∈ 𝓟, ∃ x y, p = {x, y} ∧ IsLineWithEnds (L p) x y) →
    (∀ (k : Fin 4) (i : Fin 6), k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k → ∃ z
      ∈ e i, z ∈ discBd (D 0) ∧ z ∉ discBd (D k)) →
    ∀ c ∈ Γ.C, ∃ k, c ⊆ D k := by
  intro e D hPmem hinj hDd hDb hfree hLline hnode
  exact four_discs_cover hS e Pp (fun i => hpN _ (hPmem i))
    (fun i => by
      obtain ⟨x, y, hp, hl⟩ := hLline _ (hPmem i)
      change Pp i ⊆ L (Pp i)
      rw [hp] at hl ⊢
      rintro z (rfl | rfl)
      · exact hl.left_mem
      · exact hl.right_mem)
    (fun i => by
      obtain ⟨x, y, hp, hl⟩ := hLline _ (hPmem i)
      change IsPreconnected (L (Pp i) \ Pp i)
      rw [hp] at hl ⊢
      exact hl.isPreconnected_diff)
    (fun i => by
      obtain ⟨x, y, hp, hl⟩ := hLline _ (hPmem i)
      change L (Pp i) ⊆ closure (L (Pp i) \ Pp i)
      rw [hp] at hl ⊢
      exact fun z hz => hl.subset_closure_diff hz)
    (fun i => by
      obtain ⟨x, y, hp, hl⟩ := hLline _ (hPmem i)
      change (L (Pp i) \ Pp i).Nonempty
      rw [hp] at hl ⊢
      exact closure_nonempty_iff.mp ⟨x, hl.subset_closure_diff hl.left_mem⟩)
    (fun i => by
      obtain ⟨r, hr, hsub, -⟩ := hreg _ (hPmem i)
      exact ⟨r, hr, hsub⟩)
    (fun i x hx => by
      obtain ⟨-, -, -, hs⟩ := hreg _ (hPmem i)
      obtain ⟨V, A, B, h1, h2, h3, h4, h5, h6, h7⟩ := hs x hx
      refine ⟨V, A, B, h1, h2, h3, h4, h5, h6, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact h7 _ ⟨_, hPmem j, rfl⟩)
    (fun i j hij => hdj _ (hPmem i) _ (hPmem j) (hinj i j hij)) D hDd hDb hfree hnode

theorem clique_disc [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {M : Set S}
  (hM : M ⊆ Γ.N) (h3 : 3 ≤ M.ncard)
    (hadj : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → ∃ c ∈ Γ.C, a ∈ tilde c ∧ b ∈ tilde c) (Pr : Set S → Prop)
    (h85 : ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.N).ncard ≤ 3 → ∃ Δ, IsClosedDisc Δ
      ∧ discBd Δ = F ∧ Pr Δ)
    (hfour : ¬ ∃ D : Fin 4 → Set S, (∀ k, IsClosedDisc (D k) ∧ Γ.IsNormal (discBd (D k)) ∧ (discBd
      (D k) ∩ Γ.N).ncard ≤ 3 ∧ Pr (D k)) ∧ ∀ c ∈ Γ.C, ∃ k, c ⊆ D k) :
    ∃ Δ, IsClosedDisc Δ ∧ IsOArc (discBd Δ) ∧ Γ.IsNormal (discBd Δ) ∧ (discBd Δ ∩ Γ.N).ncard ≤ 3
      ∧ Pr Δ ∧ M ⊆ Δ := by
  have hman := hS.2.2
  have hfinM : M.Finite := Γ.finite_N.subset hM
  obtain ⟨a₀, b₀, c₀, ha₀, hb₀, hc₀, hab₀, hac₀, hbc₀⟩ := (Set.two_lt_ncard_iff hfinM).1
    (by omega : 2 < M.ncard)
  obtain ⟨L, hL⟩ := exists_chords hS h hM ⟨a₀, ha₀⟩ hadj
  let 𝓟 : Set (Set S) := {p | ∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ p = {a, b}}
  obtain ⟨hline, hreg, hdj⟩ := hL 𝓟 rfl
  have hpp : ∀ {a b}, a ∈ M → b ∈ M → a ≠ b → ({a, b} : Set S) ∈ 𝓟 := fun ha hb hab
    => ⟨_, ha, _, hb, hab, rfl⟩
  have hpN : ∀ p ∈ 𝓟, p ⊆ Γ.N := by
    rintro p ⟨a, ha, b, hb, -, rfl⟩ x (rfl | rfl)
    · exact hM ha
    · exact hM hb
  have hLU : ∀ p ∈ 𝓟, L p ∩ Γ.U ⊆ p := fun p hp x hx => by
    obtain ⟨r, hr, hsub, -⟩ := hreg p hp
    by_contra hn
    exact (arcComponentsIn_subset hr (hsub ⟨hx.1, hn⟩)).2 hx.2
  have hLN : ∀ p ∈ 𝓟, L p ∩ Γ.N ⊆ p := fun p hp x hx => hLU p hp ⟨hx.1, Γ.N_subset hx.2⟩
  have hcom : ∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → L p ∩ L q ⊆ p ∩ q := fun p hp q hq hpq x hx => by
    refine ⟨?_, ?_⟩
    · by_contra hn
      exact disjoint_left.mp (hdj p hp q hq hpq) ⟨hx.1, hn⟩ hx.2
    · by_contra hn
      exact disjoint_left.mp (hdj q hq p hp hpq.symm) ⟨hx.2, hn⟩ hx.1
  let E : S → S → Set S := fun x y => L {x, y}
  have hEc : ∀ x y, E x y = E y x := fun x y => by
    change L {x, y} = L {y, x}
    rw [pair_comm]
  let Φ : S → S → S → Set S := fun x y z => E x y ∪ E y z ∪ E z x
  have hpne : ∀ {a b c d : S}, a ≠ c → a ≠ d → ({a, b} : Set S) ≠ {c, d} := fun {a b c d} h1 h2 he
    => by
    have : a ∈ ({c, d} : Set S) := he ▸ mem_insert _ _
    rcases this with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hΦ : ∀ {a b c : S}, a ∈ M → b ∈ M → c ∈ M → a ≠ b → a ≠ c → b ≠ c → IsOArc (Φ a b c)
    ∧ Γ.IsNormal (Φ a b c) ∧ (Φ a b c ∩ Γ.N).ncard ≤ 3 := fun {a b c} ha hb hc hab hac hbc => by
    exact triangle_is_normal_arc (S := S) (Γ := Γ) (M := M) L 𝓟 hline hpp hpN hLU hLN hcom
      hpne (a := a) (b := b) (c := c) ha hb hc hab hac hbc
  let 𝒯 : Set (S × S × S) := {t | t.1 ∈ M ∧ t.2.1 ∈ M ∧ t.2.2 ∈ M ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2
    ∧ t.2.1 ≠ t.2.2}
  have h𝒯fin : 𝒯.Finite := (hfinM.prod (hfinM.prod hfinM)).subset fun t ht
    => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hd : ∀ t ∈ 𝒯, ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = Φ t.1 t.2.1 t.2.2 ∧ Pr Δ := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := hΦ ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2
    exact h85 _ h1 h2 h3
  choose! dsc hdD hdB hdP using hd
  obtain ⟨⟨a, b, c⟩, ht, hmax⟩ := Set.Finite.exists_maximalFor dsc 𝒯 h𝒯fin ⟨(a₀, b₀, c₀), ha₀, hb₀,
    hc₀, hab₀, hac₀, hbc₀⟩
  have ht0 : (a, b, c) ∈ 𝒯 := ht
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ : a ∈ M ∧ b ∈ M ∧ c ∈ M ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := ht
  have hΔD := hdD (a, b, c) ht0
  have hΔb : discBd (dsc (a, b, c)) = Φ a b c := hdB (a, b, c) ht0
  obtain ⟨hO, hnorm, hcard⟩ := hΦ ha hb hc hab hac hbc
  refine ⟨dsc (a, b, c), hΔD, hΔb ▸ hO, hΔb ▸ hnorm, hΔb ▸ hcard, hdP _ ht0, fun m hm => ?_⟩
  by_contra hmΔ
  set Δ := dsc (a, b, c) with hΔ
  have haΔ : a ∈ discBd Δ := by
    rw [hΔb]
    exact .inl (.inl (hline a ha b hb hab).left_mem)
  have hbΔ : b ∈ discBd Δ := by
    rw [hΔb]
    exact .inl (.inr (hline b hb c hc hbc).left_mem)
  have hcΔ : c ∈ discBd Δ := by
    rw [hΔb]
    exact .inr (hline c hc a ha hac.symm).left_mem
  have hma : m ≠ a := fun e => hmΔ (e ▸ discBd_subset _ haΔ)
  have hmb : m ≠ b := fun e => hmΔ (e ▸ discBd_subset _ hbΔ)
  have hmc : m ≠ c := fun e => hmΔ (e ▸ discBd_subset _ hcΔ)
  have hchord : ∀ y, y ∈ M → y ∈ discBd Δ → m ≠ y → Disjoint (E m y \ {m, y}) Δ := fun y hy hyb hne
    => by
    exact outside_vertex_chord_disjoint_of_disc (S := S) (M := M) hman L 𝓟 hline hdj hpp hpne
      a b c ha hb hc hab hac hbc m hm Δ hΔD hΔb hmΔ hma hmb hmc y hy hne
  have hintoff : ∀ y, y ∈ M → y ∈ discBd Δ → m ≠ y → Disjoint (discInt Δ) (E m y)
    := fun y hy hyb hne => disjoint_left.mpr fun x hx hxe => by
    by_cases hxp : x ∈ ({m, y} : Set S)
    · rcases hxp with rfl | rfl
      · exact hmΔ hx.1
      · exact hx.2 hyb
    · exact disjoint_left.mp (hchord y hy hyb hne) ⟨hxe, hxp⟩ hx.1
  have hk : ∀ t' ∈ 𝒯, discBd (dsc t') ⊆ discBd Δ ∪ E m a ∪ E m b ∪ E m c → m ∈ discBd (dsc t')
    → Disjoint (discInt Δ) (dsc t') := fun t' ht' hsub hmb' => by
    exact triangle_disc_avoids_original_interior (S := S) (M := M) hman E 𝒯 dsc hdD a b c ha hb hc
      m Δ hmax hΔD hmΔ haΔ hbΔ hcΔ hma hmb hmc hintoff t' ht' hsub hmb'
  have ht1 : (m, b, c) ∈ 𝒯 := ⟨hm, hb, hc, hmb, hmc, hbc⟩
  have ht2 : (a, m, c) ∈ 𝒯 := ⟨ha, hm, hc, hma.symm, hac, hmc⟩
  have ht3 : (a, b, m) ∈ 𝒯 := ⟨ha, hb, hm, hab, hma.symm, hmb.symm⟩
  have hbc' : E b c ⊆ discBd Δ := by rw [hΔb]; exact fun x hx => .inl (.inr hx)
  have hab' : E a b ⊆ discBd Δ := by rw [hΔb]; exact fun x hx => .inl (.inl hx)
  have hca' : E c a ⊆ discBd Δ := by rw [hΔb]; exact fun x hx => .inr hx
  have hd1 : Disjoint (discInt Δ) (dsc (m, b, c)) := by
    refine hk _ ht1 (fun x hx => ?_) ?_
    · rw [hdB _ ht1] at hx
      rcases hx with (h1 | h1) | h1
      · exact .inl (.inr h1)
      · exact .inl (.inl (.inl (hbc' h1)))
      · exact .inr (hEc c m ▸ h1)
    · rw [hdB _ ht1]
      exact .inl (.inl (hline m hm b hb hmb).left_mem)
  have hd2 : Disjoint (discInt Δ) (dsc (a, m, c)) := by
    refine hk _ ht2 (fun x hx => ?_) ?_
    · rw [hdB _ ht2] at hx
      rcases hx with (h1 | h1) | h1
      · exact .inl (.inl (.inr (hEc a m ▸ h1)))
      · exact .inr h1
      · exact .inl (.inl (.inl (hca' h1)))
    · rw [hdB _ ht2]
      exact .inl (.inr (hline m hm c hc hmc).left_mem)
  have hd3 : Disjoint (discInt Δ) (dsc (a, b, m)) := by
    refine hk _ ht3 (fun x hx => ?_) ?_
    · rw [hdB _ ht3] at hx
      rcases hx with (h1 | h1) | h1
      · exact .inl (.inl (.inl (hab' h1)))
      · exact .inl (.inr (hEc b m ▸ h1))
      · exact .inl (.inl (.inr h1))
    · rw [hdB _ ht3]
      exact .inr (hline m hm a ha hma).left_mem
  let Pp : Fin 6 → Set S := ![{a, b}, {b, c}, {c, a}, {m, a}, {m, b}, {m, c}]
  let e : Fin 6 → Set S := fun i => L (Pp i)
  let D : Fin 4 → Set S := ![Δ, dsc (m, b, c), dsc (a, m, c), dsc (a, b, m)]
  have hPmem : ∀ i, Pp i ∈ 𝓟 := fun i => by
    fin_cases i
    exacts [hpp ha hb hab, hpp hb hc hbc, hpp hc ha hac.symm, hpp hm ha hma, hpp hm hb hmb, hpp hm
      hc hmc]
  have hinj : ∀ i j, i ≠ j → Pp i ≠ Pp j := fun i j hij he => six_pairs_inj hab hac hbc hma hmb hmc
    i j hij he
  have hLcl : ∀ p ∈ 𝓟, IsClosed (L p) := by
    rintro p ⟨x, hx, y, hy, hxy, rfl⟩
    exact (hline x hx y hy hxy).isCompact.isClosed
  have hunion : ∀ x y z : Fin 6, (⋃ i ∈ ({x, y, z} : Finset (Fin 6)), e i) = e x ∪ e y ∪ e z
    := fun x y z => by
    ext w
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton, mem_union, exists_prop]
    constructor
    · rintro ⟨i, rfl | rfl | rfl, h1⟩
      · exact .inl (.inl h1)
      · exact .inl (.inr h1)
      · exact .inr h1
    · rintro ((h1 | h1) | h1)
      · exact ⟨x, .inl rfl, h1⟩
      · exact ⟨y, .inr (.inl rfl), h1⟩
      · exact ⟨z, .inr (.inr rfl), h1⟩
  have hDd : ∀ k, IsClosedDisc (D k) := fun k => by
    fin_cases k
    exacts [hΔD, hdD _ ht1, hdD _ ht2, hdD _ ht3]
  have hDb : ∀ k, discBd (D k) = ⋃ i ∈ circuitChords k, e i := fun k => by
    exact tetrahedral_disc_boundaries (S := S) E hEc 𝒯 dsc hdB a b c m Δ hΔb ht1 ht2 ht3 e
      rfl rfl rfl rfl rfl rfl hunion k
  have hfree : ∀ k, k ≠ 0 → Disjoint (discInt (D 0)) (D k) := fun k hk0 => by
    fin_cases k
    · exact absurd rfl hk0
    · exact hd1
    · exact hd2
    · exact hd3
  have hLline : ∀ p ∈ 𝓟, ∃ x y, p = {x, y} ∧ IsLineWithEnds (L p) x y := by
    rintro p ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, y, rfl, hline x hx y hy hxy⟩
  have hnotN : ∀ {z x y : S}, z ∈ Γ.N → z ≠ x → z ≠ y → x ∈ M → y ∈ M → x ≠ y → z ∉ E x y :=
    fun hz h1 h2 hx hy hxy hzE => by
      rcases hLN _ (hpp hx hy hxy) ⟨hzE, hz⟩ with h | h
      · exact h1 h
      · exact h2 h
  have hcase : ∀ (k : Fin 4) (i : Fin 6), k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k →
      (k = 1 ∧ i = 3) ∨ (k = 2 ∧ i = 4) ∨ (k = 3 ∧ i = 5) := by decide
  have hnode : ∀ k i, k ≠ 0 → i ∉ circuitChords 0 → i ∉ circuitChords k →
      ∃ z ∈ e i, z ∈ discBd (D 0) ∧ z ∉ discBd (D k) := by
    exact disc_side_vertex_on_boundary_or_off_disc (S := S) (Γ := Γ) (M := M) hM L hline 𝒯 dsc
      hdB a b c ha hb hc hab hac hbc m hm Δ haΔ hbΔ hcΔ hma hmb hmc ht1 ht2 ht3   hnotN hcase
  have hcov : ∀ c ∈ Γ.C, ∃ k, c ⊆ D k := by
    exact clique_chord_discs_cover (S := S) (Γ := Γ) hS L 𝓟 hreg hdj hpN Pp D hPmem hinj hDd hDb
      hfree hLline hnode
  refine hfour ⟨D, fun k => ?_, hcov⟩
  fin_cases k
  · exact ⟨hΔD, hΔb ▸ hnorm, hΔb ▸ hcard, hdP _ ht0⟩
  · obtain ⟨-, h2, h3⟩ := hΦ hm hb hc hmb hmc hbc
    exact ⟨hdD _ ht1, (hdB _ ht1).symm ▸ h2, (hdB _ ht1).symm ▸ h3, hdP _ ht1⟩
  · obtain ⟨-, h2, h3⟩ := hΦ ha hm hc hma.symm hac hmc
    exact ⟨hdD _ ht2, (hdB _ ht2).symm ▸ h2, (hdB _ ht2).symm ▸ h3, hdP _ ht2⟩
  · obtain ⟨-, h2, h3⟩ := hΦ ha hb hm hab hma.symm hmb.symm
    exact ⟨hdD _ ht3, (hdB _ ht3).symm ▸ h2, (hdB _ ht3).symm ▸ h3, hdP _ ht3⟩

end GraphMinor.GM17
