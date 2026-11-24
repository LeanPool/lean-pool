/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8b
public import LeanPool.GraphMinor.GM10.Section8
public import LeanPool.GraphMinor.GM10.Section9

/-!
# Graph Minors XIX, (8.2) and (8.3)

The tie-breakers of Section 8 are tie-breakers in the sense of Graph Minors X.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

section Sep

variable {A B : Hypergraph S (Set S)}

omit [T2Space S] in
theorem edge_cases (h : Γ.toHypergraph.IsSeparation A B) {c : Set S} (hc : c ∈ Γ.E) :
    (c ∈ A.edgeSet ∧ c ∉ B.edgeSet) ∨ (c ∉ A.edgeSet ∧ c ∈ B.edgeSet) := by
  have h₁ : c ∈ (A ∪ B).edgeSet := by
    rw [h.union_eq]
    exact hc
  have h₂ : ∀ {x}, x ∈ A.edgeSet → x ∈ B.edgeSet → False := fun hA hB ↦ by
    have : _ ∈ (A ∩ B).edgeSet := ⟨hA, hB⟩
    rw [h.edgeSet_inter_eq] at this
    exact this
  rcases h₁ with h₁ | h₁
  · exact Or.inl ⟨h₁, fun hB ↦ h₂ h₁ hB⟩
  · exact Or.inr ⟨fun hA ↦ h₂ hA h₁, h₁⟩

/-- A pair decides whether a separation splits an edge of `Γ*`. -/
theorem splits_of_pair (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
    {rad : RadialDrawing cap Γ} {e : Set Shat} {c₁ c₂ : Set S} (hp : rad.PairOf e c₁ c₂)
    (h : Γ.toHypergraph.IsSeparation A B) :
    rad.Splits A B e ↔ ¬ (c₁ ∈ A.edgeSet ↔ c₂ ∈ A.edgeSet) := by
  obtain ⟨hc₁, hc₂⟩ : c₁ ∈ Γ.E ∧ c₂ ∈ Γ.E := by
    obtain ⟨_, _, _, _, _, _, _, _, h₁, h₂, _⟩ := hp
    exact ⟨h₁.1, h₂.1⟩
  have h₁ := edge_cases h hc₁
  have h₂ := edge_cases h hc₂
  rw [rad.splits_iff]
  constructor
  · rintro ⟨d₁, d₂, hd, hs⟩
    rcases hp.unique hS h3 hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · intro hn
    refine ⟨c₁, c₂, hp, ?_⟩
    tauto

end Sep

/-- The pure order fact behind the second tie-breaker axiom. -/
theorem lex_axiom2 {n₁ n₂ n₃ n₄ : ℕ} {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ} (hn : n₃ + n₄ = n₁ + n₂)
    (hx : x₃ + x₄ ≤ x₁ + x₂) (hy : y₃ + y₄ = y₁ + y₂) :
    (toLex (n₃, toLex (x₃, y₃)) ≤ toLex (n₁, toLex (x₁, y₁)) ∨
      toLex (n₄, toLex (x₄, y₄)) < toLex (n₂, toLex (x₂, y₂))) ∧
    (toLex (n₃, toLex (x₃, y₃)) < toLex (n₁, toLex (x₁, y₁)) ∨
      toLex (n₄, toLex (x₄, y₄)) ≤ toLex (n₂, toLex (x₂, y₂))) := by
  constructor
  · by_contra! h
    obtain ⟨h₁, h₂⟩ := h
    rw [Prod.Lex.lt_iff] at h₁
    rw [Prod.Lex.le_iff] at h₂
    simp only [ofLex_toLex] at h₁ h₂
    rcases h₁ with a | ⟨a, b⟩
    · rcases h₂ with c | ⟨c, -⟩ <;> omega
    · rcases h₂ with c | ⟨c, d⟩
      · omega
      · rw [Prod.Lex.lt_iff] at b
        rw [Prod.Lex.le_iff] at d
        simp only [ofLex_toLex] at b d
        rcases b with b | ⟨b, e⟩
        · rcases d with d | ⟨d, -⟩ <;> linarith
        · rcases d with d | ⟨-, d⟩ <;> linarith
  · by_contra! h
    obtain ⟨h₁, h₂⟩ := h
    rw [Prod.Lex.le_iff] at h₁
    rw [Prod.Lex.lt_iff] at h₂
    simp only [ofLex_toLex] at h₁ h₂
    rcases h₁ with a | ⟨a, b⟩
    · rcases h₂ with c | ⟨c, -⟩ <;> omega
    · rcases h₂ with c | ⟨c, d⟩
      · omega
      · rw [Prod.Lex.le_iff] at b
        rw [Prod.Lex.lt_iff] at d
        simp only [ofLex_toLex] at b d
        rcases d with d | ⟨d, e⟩
        · rcases b with b | ⟨b, -⟩ <;> linarith
        · rcases b with b | ⟨-, b⟩ <;> linarith

theorem ite_cast (p q : Prop) [Decidable p] [Decidable q] (x : ℝ) :
    (((if p then 1 else 0) - (if q then 1 else 0) : ℚ) : ℝ) * x =
      (if p then x else 0) - (if q then x else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_zero {p q : Prop} [Decidable p] [Decidable q]
    (h : ((if p then 1 else 0) - (if q then 1 else 0) : ℚ) = 0) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- A sum over a finite set, written as a sum over a larger one. -/
theorem finsum_eq_sum_ite {T : Type*} {s : Set T} (F : Finset T) (hs : s ⊆ F) (f : T → ℝ)
    [DecidablePred (· ∈ s)] : ∑ᶠ x ∈ s, f x = ∑ x ∈ F, if x ∈ s then f x else 0 := by
  rw [← Finset.sum_filter]
  have : s = ↑(F.filter (· ∈ s)) := by
    ext x
    simp only [Finset.coe_filter, mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨hs h, h⟩, fun h ↦ h.2⟩
  conv_lhs => rw [this]
  exact finsum_mem_coe_finset _ _

/-- A separation is decided by its middle and its edges, when each vertex is an end of an edge. -/
theorem side_le {α β : Type*} {G A B C D : Hypergraph α β} (hAB : G.IsSeparation A B)
    (hCD : G.IsSeparation C D) (hV : (A ∩ B).vertexSet ⊆ (C ∩ D).vertexSet)
    (hE : A.edgeSet ⊆ C.edgeSet) (hinc : ∀ v ∈ G.vertexSet, ∃ c, G.Inc c v) : A ≤ C := by
  refine ⟨fun v hv ↦ ?_, hE, fun e he ↦ ?_⟩
  · by_cases hvB : v ∈ B.vertexSet
    · exact (hV ⟨hv, hvB⟩).1
    · obtain ⟨c, hc⟩ := hinc v (hAB.left_le.vertexSet_subset hv)
      have hcG := G.edge_mem_of_inc hc
      rw [← hAB.union_eq] at hcG
      rcases hcG with hcA | hcB
      · have h₁ : v ∈ G.ends c := hc
        rw [hCD.left_le.ends_eq c (hE hcA)] at h₁
        exact C.vertex_mem_of_inc h₁
      · have h₁ : v ∈ G.ends c := hc
        rw [hAB.right_le.ends_eq c hcB] at h₁
        exact absurd (B.vertex_mem_of_inc h₁) hvB
  · rw [← hCD.left_le.ends_eq e (hE he), hAB.left_le.ends_eq e he]

section TieBreaker

variable [T2Space Shat] {rad : RadialDrawing cap Γ}

omit [T2Space Shat] in
omit [T2Space S] in
theorem splits_comm {A B : Hypergraph S (Set S)} {e : Set Shat} :
    rad.Splits A B e ↔ rad.Splits B A e := by
  simp only [rad.splits_iff, or_comm]

omit [T2Space Shat] [T2Space S] in
theorem TieBreaker.lambdaOrder_comm (tb : TieBreaker rad) (A B : Hypergraph S (Set S)) :
    tb.lambdaOrder (A, B) = tb.lambdaOrder (B, A) := by
  have hi : (A ∩ B).vertexSet = (B ∩ A).vertexSet := Set.inter_comm _ _
  have h₁ : tb.N1 (A, B) = tb.N1 (B, A) := by
    simp only [TieBreaker.N1, Hypergraph.separationOrder, hi]
  have h₂ : tb.N2 (A, B) = tb.N2 (B, A) := by
    simp only [TieBreaker.N2, splits_comm (A := A)]
  have h₃ : tb.N3 (A, B) = tb.N3 (B, A) := by
    simp only [TieBreaker.N3, hi]
  simp only [TieBreaker.lambdaOrder, h₁, h₂, h₃]

open Classical in
omit [T2Space Shat] in
theorem TieBreaker.N2_le (tb : TieBreaker rad) (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) {A B C D : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hCD : Γ.toHypergraph.IsSeparation C D) :
    tb.N2 (A ∪ C, B ∩ D) + tb.N2 (A ∩ C, B ∪ D) ≤ tb.N2 (A, B) + tb.N2 (C, D) := by
  have hEfin : rad.G.E.Finite := rad.G.finite_edges
  have hfs : ∀ A' B' : Hypergraph S (Set S), {e ∈ rad.G.E | rad.Splits A' B' e} ⊆
      ↑hEfin.toFinset := fun _ _ e he ↦ by simpa using he.1
  simp only [TieBreaker.N2, finsum_eq_sum_ite _ (hfs _ _), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he ↦ ?_
  have heE : e ∈ rad.G.E := by simpa using he
  have hpos := tb.wtE_pos e heE
  have hs₁ := hAB.union_inter hCD
  have hs₂ := (hAB.symm.union_inter hCD.symm).symm
  by_cases hp : ∃ c₁ c₂, rad.PairOf e c₁ c₂
  · obtain ⟨c₁, c₂, hp⟩ := hp
    have e₁ := splits_of_pair hS h3 hp hAB
    have e₂ := splits_of_pair hS h3 hp hCD
    have e₃ := splits_of_pair hS h3 hp hs₁
    have e₄ := splits_of_pair hS h3 hp hs₂
    have hA₁ : c₁ ∈ (A ∪ C).edgeSet ↔ (c₁ ∈ A.edgeSet ∨ c₁ ∈ C.edgeSet) := Iff.rfl
    have hA₂ : c₂ ∈ (A ∪ C).edgeSet ↔ (c₂ ∈ A.edgeSet ∨ c₂ ∈ C.edgeSet) := Iff.rfl
    have hB₁ : c₁ ∈ (A ∩ C).edgeSet ↔ (c₁ ∈ A.edgeSet ∧ c₁ ∈ C.edgeSet) := Iff.rfl
    have hB₂ : c₂ ∈ (A ∩ C).edgeSet ↔ (c₂ ∈ A.edgeSet ∧ c₂ ∈ C.edgeSet) := Iff.rfl
    simp only [mem_ofPred_eq, mem_ofPred_eq, heE, true_and, e₁, e₂, e₃, e₄, hA₁, hA₂, hB₁, hB₂]
    by_cases a₁ : c₁ ∈ A.edgeSet <;> by_cases a₂ : c₂ ∈ A.edgeSet <;>
      by_cases b₁ : c₁ ∈ C.edgeSet <;> by_cases b₂ : c₂ ∈ C.edgeSet <;>
      simp [a₁, a₂, b₁, b₂, hpos.le]
  · have hno : ∀ A' B' : Hypergraph S (Set S), ¬ rad.Splits A' B' e := fun A' B' h ↦ by
      obtain ⟨c₁, c₂, h, -⟩ := rad.splits_iff.mp h
      exact hp ⟨c₁, c₂, h⟩
    simp [hno]

open Classical in
omit [T2Space S] [T2Space Shat] in
theorem TieBreaker.N3_eq (tb : TieBreaker rad) {A B C D : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hCD : Γ.toHypergraph.IsSeparation C D) :
    tb.N3 (A ∪ C, B ∩ D) + tb.N3 (A ∩ C, B ∪ D) = tb.N3 (A, B) + tb.N3 (C, D) := by
  have hle : ∀ {P Q : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation P Q →
      (P ∩ Q).vertexSet ⊆ ↑Γ.finite_V.toFinset := fun h v hv ↦ by
    exact Γ.finite_V.mem_toFinset.mpr (h.left_le.vertexSet_subset hv.1)
  have hs₁ := hAB.union_inter hCD
  have hs₂ := (hAB.symm.union_inter hCD.symm).symm
  simp only [TieBreaker.N3, finsum_eq_sum_ite _ (hle hAB), finsum_eq_sum_ite _ (hle hCD),
    finsum_eq_sum_ite _ (hle hs₁), finsum_eq_sum_ite _ (hle hs₂), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  have hvV : v ∈ Γ.toHypergraph.vertexSet := Γ.finite_V.mem_toFinset.mp hv
  have h₁ : v ∈ (A ∪ B).vertexSet := hAB.union_eq ▸ hvV
  have h₂ : v ∈ (C ∪ D).vertexSet := hCD.union_eq ▸ hvV
  have h₁' : v ∈ A.vertexSet ∨ v ∈ B.vertexSet := h₁
  have h₂' : v ∈ C.vertexSet ∨ v ∈ D.vertexSet := h₂
  have m₁ : v ∈ (A ∩ B).vertexSet ↔ (v ∈ A.vertexSet ∧ v ∈ B.vertexSet) := Iff.rfl
  have m₂ : v ∈ (C ∩ D).vertexSet ↔ (v ∈ C.vertexSet ∧ v ∈ D.vertexSet) := Iff.rfl
  have m₃ : v ∈ ((A ∪ C) ∩ (B ∩ D)).vertexSet ↔
      ((v ∈ A.vertexSet ∨ v ∈ C.vertexSet) ∧ (v ∈ B.vertexSet ∧ v ∈ D.vertexSet)) := Iff.rfl
  have m₄ : v ∈ ((A ∩ C) ∩ (B ∪ D)).vertexSet ↔
      ((v ∈ A.vertexSet ∧ v ∈ C.vertexSet) ∧ (v ∈ B.vertexSet ∨ v ∈ D.vertexSet)) := Iff.rfl
  simp only [m₁, m₂, m₃, m₄]
  by_cases a : v ∈ A.vertexSet <;> by_cases b : v ∈ B.vertexSet <;>
    by_cases c : v ∈ C.vertexSet <;> by_cases d : v ∈ D.vertexSet <;> simp_all

omit [T2Space Shat] in
/-- **Graph Minors XIX, (8.3)**, in the form of the second tie-breaker axiom of Graph Minors X. -/
theorem TieBreaker.lambda_sum (tb : TieBreaker rad) (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) {A B C D : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hCD : Γ.toHypergraph.IsSeparation C D) :
    (tb.lambdaOrder (A ∪ C, B ∩ D) ≤ tb.lambdaOrder (A, B) ∨
      tb.lambdaOrder (A ∩ C, B ∪ D) < tb.lambdaOrder (C, D)) ∧
    (tb.lambdaOrder (A ∪ C, B ∩ D) < tb.lambdaOrder (A, B) ∨
      tb.lambdaOrder (A ∩ C, B ∪ D) ≤ tb.lambdaOrder (C, D)) := by
  refine lex_axiom2 ?_ (tb.N2_le hS h3 hAB hCD) (tb.N3_eq hAB hCD)
  have := separationOrder_add_separationOrder hAB hCD
  simp only [TieBreaker.N1]
  omega

omit [T2Space Shat] in
/-- **Graph Minors XIX, (8.2).** Separations with the same `λ`-order are equal, up to swapping. -/
theorem TieBreaker.eq_of_lambda_eq (tb : TieBreaker rad) (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) {A B C D : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hCD : Γ.toHypergraph.IsSeparation C D)
    (h : tb.lambdaOrder (A, B) = tb.lambdaOrder (C, D)) : (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  classical
  have h' := congrArg ofLex h
  simp only [TieBreaker.lambdaOrder, ofLex_toLex, Prod.mk.injEq] at h'
  obtain ⟨-, h'⟩ := h'
  have h'' := congrArg ofLex h'
  simp only [ofLex_toLex, Prod.mk.injEq] at h''
  obtain ⟨hN₂, hN₃⟩ := h''
  have hEfin : rad.G.E.Finite := rad.G.finite_edges
  have hfs : ∀ A' B' : Hypergraph S (Set S), {e ∈ rad.G.E | rad.Splits A' B' e} ⊆
      ↑hEfin.toFinset := fun _ _ e he ↦ hEfin.mem_toFinset.mpr he.1
  have hspl : ∀ e ∈ rad.G.E, rad.Splits A B e ↔ rad.Splits C D e := by
    let α : Set Shat → ℚ := fun e ↦
      (if rad.Splits A B e then 1 else 0) - (if rad.Splits C D e then 1 else 0)
    have hsum : ∑ᶠ e ∈ rad.G.E, (α e : ℝ) * tb.wtE e =
        ∑ᶠ v ∈ Γ.V, (((0 : S → ℚ) v : ℚ) : ℝ) * tb.wtV v := by
      have hl : ∑ᶠ e ∈ rad.G.E, (α e : ℝ) * tb.wtE e = tb.N2 (A, B) - tb.N2 (C, D) := by
        simp only [TieBreaker.N2, finsum_eq_sum_ite _ (hfs _ _),
          finsum_eq_sum_ite hEfin.toFinset (fun e he ↦ hEfin.mem_toFinset.mpr he),
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e he ↦ ?_
        have heE : e ∈ rad.G.E := hEfin.mem_toFinset.mp he
        simp only [heE, mem_ofPred_eq, true_and, ite_true, α]
        exact ite_cast _ _ _
      rw [hl, hN₂]
      simp
    have hz := (tb.rationally_independent α 0 hsum).1
    intro e he
    have := hz e he
    exact ite_zero this
  have hvert : (A ∩ B).vertexSet = (C ∩ D).vertexSet := by
    have hle : ∀ {P Q : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation P Q →
        (P ∩ Q).vertexSet ⊆ ↑Γ.finite_V.toFinset := fun h v hv ↦
      Γ.finite_V.mem_toFinset.mpr (h.left_le.vertexSet_subset hv.1)
    let β : S → ℚ := fun v ↦
      (if v ∈ (A ∩ B).vertexSet then 1 else 0) - (if v ∈ (C ∩ D).vertexSet then 1 else 0)
    have hsum : ∑ᶠ e ∈ rad.G.E, (((0 : Set Shat → ℚ) e : ℚ) : ℝ) * tb.wtE e =
        ∑ᶠ v ∈ Γ.V, (β v : ℝ) * tb.wtV v := by
      have hl : ∑ᶠ v ∈ Γ.V, (β v : ℝ) * tb.wtV v = tb.N3 (A, B) - tb.N3 (C, D) := by
        simp only [TieBreaker.N3, finsum_eq_sum_ite _ (hle hAB), finsum_eq_sum_ite _ (hle hCD),
          finsum_eq_sum_ite Γ.finite_V.toFinset (fun v hv ↦ Γ.finite_V.mem_toFinset.mpr hv),
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v hv ↦ ?_
        have hvV : v ∈ Γ.V := Γ.finite_V.mem_toFinset.mp hv
        simp only [hvV, ite_true, β]
        exact ite_cast _ _ _
      rw [hl, hN₃]
      simp
    have hz := (tb.rationally_independent 0 β hsum).2
    ext v
    by_cases hv : v ∈ Γ.V
    · exact ite_zero (hz v hv)
    · exact ⟨fun h ↦ absurd (hAB.left_le.vertexSet_subset h.1) hv,
        fun h ↦ absurd (hCD.left_le.vertexSet_subset h.1) hv⟩
  have hsame : ∀ {c c' : Set S}, c ∈ Γ.E → c' ∈ Γ.E →
      ((c ∈ A.edgeSet ↔ c ∈ C.edgeSet) ↔ (c' ∈ A.edgeSet ↔ c' ∈ C.edgeSet)) := by
    intro c c' hc hc'
    refine edges_same hS h3 rad (fun c ↦ c ∈ A.edgeSet ↔ c ∈ C.edgeSet) ?_ hc hc'
    intro e he c₁ c₂ hp
    have e₁ := splits_of_pair hS h3 hp hAB
    have e₂ := splits_of_pair hS h3 hp hCD
    have := hspl e he
    rw [e₁, e₂] at this
    tauto
  have hinc : ∀ v ∈ Γ.toHypergraph.vertexSet, ∃ c, Γ.toHypergraph.Inc c v := fun v hv ↦ by
    obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 rad hv
    exact ⟨c, hc, hv, hvc, fun h ↦ Γ.disjoint_V hc h hv⟩
  have hdecide : ∀ {P Q R T : Hypergraph S (Set S)}, Γ.toHypergraph.IsSeparation P Q →
      Γ.toHypergraph.IsSeparation R T → (P ∩ Q).vertexSet = (R ∩ T).vertexSet →
      (∀ c ∈ Γ.E, (c ∈ P.edgeSet ↔ c ∈ R.edgeSet)) → P = R ∧ Q = T := by
    intro P Q R T hPQ hRT hV hE
    have hE' : ∀ c ∈ Γ.E, (c ∈ Q.edgeSet ↔ c ∈ T.edgeSet) := fun c hc ↦ by
      have := hE c hc
      have h₁ := edge_cases hPQ hc
      have h₂ := edge_cases hRT hc
      tauto
    have hVc : (Q ∩ P).vertexSet = (T ∩ R).vertexSet := by
      have e₁ : (Q ∩ P).vertexSet = (P ∩ Q).vertexSet := Set.inter_comm _ _
      have e₂ : (T ∩ R).vertexSet = (R ∩ T).vertexSet := Set.inter_comm _ _
      rw [e₁, e₂, hV]
    exact ⟨le_antisymm
        (side_le hPQ hRT hV.subset (fun c hc ↦ (hE c (hPQ.left_le.edgeSet_subset hc)).mp hc) hinc)
        (side_le hRT hPQ hV.symm.subset
          (fun c hc ↦ (hE c (hRT.left_le.edgeSet_subset hc)).mpr hc) hinc),
      le_antisymm
        (side_le hPQ.symm hRT.symm hVc.subset
          (fun c hc ↦ (hE' c (hPQ.right_le.edgeSet_subset hc)).mp hc) hinc)
        (side_le hRT.symm hPQ.symm hVc.symm.subset
          (fun c hc ↦ (hE' c (hRT.right_le.edgeSet_subset hc)).mpr hc) hinc)⟩
  obtain ⟨c₀, hc₀⟩ := h3.1
  by_cases ht : c₀ ∈ A.edgeSet ↔ c₀ ∈ C.edgeSet
  · exact Or.inl (hdecide hAB hCD hvert fun c hc ↦ (hsame hc₀ hc).mp ht)
  · refine Or.inr ?_
    have hvert' : (A ∩ B).vertexSet = (D ∩ C).vertexSet := by
      rw [hvert]
      exact Set.inter_comm _ _
    refine hdecide hAB hCD.symm hvert' fun c hc ↦ ?_
    have h₁ : ¬ (c ∈ A.edgeSet ↔ c ∈ C.edgeSet) := fun h ↦ ht ((hsame hc hc₀).mp h)
    have h₂ := edge_cases hCD hc
    tauto

omit [T2Space Shat] in
/-- The `λ`-order of a tie-breaker of a painting is a tie-breaker of Graph Minors X. -/
theorem TieBreaker.isTieBreaker (tb : TieBreaker rad) (hS : IsSurface S)
    (h3 : Γ.IsInternallyThreeConnected) : IsTieBreaker Γ.toHypergraph tb.lambdaOrder where
  axiom1 A B C D hAB hCD := by
    constructor
    · exact tb.eq_of_lambda_eq hS h3 hAB hCD
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact tb.lambdaOrder_comm _ _
  axiom2 A B C D hAB hCD := (tb.lambda_sum hS h3 hAB hCD).1
  axiom3 A B C D _ _ h := by
    simp only [TieBreaker.lambdaOrder]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end TieBreaker

/-- **Graph Minors XIX, (8.2).** "If $(A, B), (A', B')$ are separations with the same
$\lambda$-order, then $(A, B) = (A',
B')$ or $(B', A')$." -/
theorem theorem_8_2_proof {rad : RadialDrawing cap Γ} (tb : TieBreaker rad)
    (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) {A B A' B' : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hAB' : Γ.toHypergraph.IsSeparation A' B')
    (h : tb.lambdaOrder (A, B) = tb.lambdaOrder (A', B')) :
    (A = A' ∧ B = B') ∨ (A = B' ∧ B = A') :=
  tb.eq_of_lambda_eq hS h3 hAB hAB' h

/-- **Graph Minors XIX, (8.3).** "If $(A, B), (A', B')$ are separations then so are $(A \cup A', B
\cap B')$, $(A \cap A', B
\cup B')$, and either $(A \cup A', B \cap B')$ has smaller $\lambda$-order than $(A, B)$, or
$(A \cap A', B \cup B')$ has $\lambda$-order at most that of $(A', B')$." -/
theorem theorem_8_3_proof {rad : RadialDrawing cap Γ} (tb : TieBreaker rad)
    (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected) {A B A' B' : Hypergraph S (Set S)}
    (hAB : Γ.toHypergraph.IsSeparation A B) (hAB' : Γ.toHypergraph.IsSeparation A' B') :
    Γ.toHypergraph.IsSeparation (A ∪ A') (B ∩ B') ∧
      Γ.toHypergraph.IsSeparation (A ∩ A') (B ∪ B') ∧
      (tb.lambdaOrder (A ∪ A', B ∩ B') < tb.lambdaOrder (A, B) ∨
        tb.lambdaOrder (A ∩ A', B ∪ B') ≤ tb.lambdaOrder (A', B')) :=
  ⟨hAB.union_inter hAB', (hAB.symm.union_inter hAB'.symm).symm,
    (tb.lambda_sum hS h3 hAB hAB').2⟩

end GraphMinor.GM19
