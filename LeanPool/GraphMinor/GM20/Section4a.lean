/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Basic

/-!
# Graph Minors XX, Section 4, (4.1) and (4.3)–(4.6)

This file proves the bound (4.1) on the number of ends of edges in `dom(μ)` in a well-behaved set,
and the results (4.3)–(4.6), which change the roots of the members of a well-behaved set.

For (4.1), an unbounded set would give a sequence in which one edge gets a label incomparable to all
others, and an expansion would have to match two such edges with different numbers of ends. For
(4.3), we record the new root `v` by giving a distinguished edge `f` with `v` as its `r`th term a
label from a disjoint copy of `Ω`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

open Classical in
/-- Graph Minors XX, (4.1) (page 330): "If $\mathcal{F}$ is well-behaved, then there exists $N \ge
0$ such that if $(G, \mu, \Delta)
\in \mathcal{F}$ and $e \in dom(\mu)$ then $|\bar{\mu}(e)| \le N$." We bound the length of the march
`μ(e)`, which
is `|μBar(e)|`. -/
theorem theorem_4_1_proof {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) :
    ∃ N, ∀ P ∈ 𝓕, ∀ e ∈ P.dom, (P.μ e).length ≤ N := by
  by_contra hcon
  push Not at hcon
  choose P hP E hE hL using hcon
  -- The numbers `g k` make the lengths `L (g k) = g (k + 1)` strictly increase.
  let g : ℕ → ℕ := fun k ↦ Nat.rec 0 (fun _ m ↦ ((P m).μ (E m)).length) k
  have hg : StrictMono g := strictMono_nat_of_lt_succ fun k ↦ hL (g k)
  let Ω := ULift.{max u v} (Discrete Bool)
  let _ : Preorder Ω := Preorder.lift ULift.down
  have hΩ : WellQuasiOrderedLE Ω := by
    have h₀ := wqo_discrete Bool
    exact ⟨fun f ↦ h₀.wqo (fun n ↦ (f n).down)⟩
  let Q : ℕ → Patchwork Ω α β := fun k ↦
    (P (g k)).relabel fun e ↦ ⟨if e = E (g k) then true else false⟩
  obtain ⟨i, j, hij, ηv, ηe, hη, -⟩ := h Ω hΩ Q fun k ↦
    ⟨P (g k), hP _, isCompletionOf_relabel _ _⟩
  have hei : E (g i) ∈ (Q i).G.edgeSet := (P (g i)).dom_subset (hE _)
  have hle := hη.φ_le _ hei
  have hval : ((Q j).φ (ηe (E (g i)))).down = true := by
    have h₁ : ((Q i).φ (E (g i))).down = true := ite_eq_left rfl
    rw [← h₁]
    exact hle.symm
  have heq : ηe (E (g i)) = E (g j) := by
    by_contra hne
    simp [Q, Patchwork.relabel, hne] at hval
  have hlen := hη.μ_length _ (hE (g i))
  rw [heq] at hlen
  have h₃ : g (i + 1) = g (j + 1) := hlen
  have h₄ : g (i + 1) < g (j + 1) := hg (Nat.succ_lt_succ hij)
  exact h₄.ne h₃

/-- The set `𝓕₂` of (4.3), for a fixed `r`: the patchworks `P₂ = (G₂, μ, Δ)` with
`(G₁, μ, Δ) ∈ 𝓕₁`, `G₂⁻ = G₁⁻`, and `π(G₂)` the concatenation of `π(G₁)` with a new last term `v`,
where `v` is the `r`th term of `μ(f)` for some `f ∈ dom(μ)`. -/
def addRootSet (𝓕₁ : Set (UnlabeledPatchwork α β)) (r : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂ ∧ ∃ v f, P₂.G.roots = P₁.G.roots ++ [v] ∧ f ∈ P₁.dom ∧
    (P₁.μ f)[r]? = some v}

open Classical in
/-- The fixed-`r` part of the proof of (4.3). -/
theorem wellBehaved_addRootSet {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁) (r : ℕ) :
    WellBehaved (addRootSet 𝓕₁ r) := by
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦ ?_
  refine ⟨DisjointUnionQuasiOrder Ω₂ Ω₂, inferInstance, wqo_disjointUnion hΩ₂ hΩ₂, ?_⟩
  -- `R Q₂ Q₁`: `Q₁` is `Q₂` with the last root removed and the label of `f` moved to the copy.
  let R : Patchwork Ω₂ α β → Patchwork (DisjointUnionQuasiOrder Ω₂ Ω₂) α β → Prop := fun Q₂ Q₁ ↦
    ∃ v f, Q₂.G.roots = Q₁.G.roots ++ [v] ∧ SameBase Q₂ Q₁ ∧ f ∈ Q₁.dom ∧
      (Q₁.μ f)[r]? = some v ∧
      (∀ e, Q₁.φ e = if e = f then Sum.inr (Q₂.φ e) else Sum.inl (Q₂.φ e))
  refine ⟨R, ?_, ?_⟩
  · rintro Q₂ ⟨P₂, ⟨P₁, hP₁, hb, v, f, hr, hf, hμ⟩, hQ⟩
    have hb' : SameBase P₁ Q₂ := hb.trans hQ.sameBase
    refine ⟨P₁.relabel fun e ↦ if e = f then Sum.inr (Q₂.φ e) else Sum.inl (Q₂.φ e),
      ⟨P₁, hP₁, isCompletionOf_relabel _ _⟩, v, f, ?_,
      hb'.symm.trans (isCompletionOf_relabel _ _).sameBase, hf, hμ, fun e ↦ rfl⟩
    rw [hQ.G_eq, hr]
    rfl
  · rintro Q₂ - Q₂' - S S' ⟨v, f, hr, hb, hf, hμ, hφ⟩ ⟨v', f', hr', hb', hf', hμ', hφ'⟩
      ⟨ηv, ηe, hη⟩
    have hfE : f ∈ S.G.edgeSet := S.dom_subset hf
    -- `η(f) = f'`, since `f'` is the only edge with a label in the copy.
    have hηf : ηe f = f' := by
      have hle := hη.1.φ_le f hfE
      rw [hφ f, hφ' (ηe f)] at hle
      by_contra hne
      simp only [ite_true, hne, ite_false] at hle
      exact nomatch hle
    -- The other labels stay in `Ω₂`.
    have hle : ∀ e ∈ S.G.edgeSet, Q₂.φ e ≤ Q₂'.φ (ηe e) := by
      intro e he
      have hl := hη.1.φ_le e he
      rw [hφ e, hφ' (ηe e)] at hl
      by_cases hef : e = f
      · subst hef
        rw [hηf] at hl ⊢
        simp only [ite_true] at hl
        cases hl with
        | inr h => exact h
      · have hne : ηe e ≠ f' := fun heq ↦ hef (hη.1.edge_injOn he hfE (heq.trans hηf.symm))
        simp only [hef, hne, ite_false] at hl
        cases hl with
        | inl h => exact h
    have hlen : S.G.roots.length = S'.G.roots.length := hη.1.roots_length
    refine ⟨ηv, ηe, realizable_transfer hη hb.symm hb'.symm (fun e he ↦ hle e
      (hb.edgeSet_eq ▸ he)) ?_ ?_⟩
    · simp [hr, hr', hlen]
    · intro i hi hi'
      simp only [hr, hr'] at hi hi' ⊢
      by_cases his : i < S.G.roots.length
      · have his' : i < S'.G.roots.length := hlen ▸ his
        rw [List.getElem_append_left his, List.getElem_append_left his']
        exact hη.1.roots_mem i his his'
      · have hieq : i = S.G.roots.length := by
          simp at hi
          omega
        have hi'' : ¬ i < S'.G.roots.length := hlen ▸ his
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        simp only [List.getElem_singleton]
        -- `v'` is the `r`th term of `μ'(f') = μ'(η(f))`, so it lies in `η(v)`.
        obtain ⟨hr₁, hr₂⟩ := List.getElem?_eq_some_iff.mp hμ
        obtain ⟨hr₁', hr₂'⟩ := List.getElem?_eq_some_iff.mp hμ'
        have hm := hη.1.μ_mem f hf r hr₁ (by rw [hηf]; exact hr₁')
        simp only [hηf, hr₂, hr₂'] at hm
        exact hm

/-- Graph Minors XX, (4.3) (page 331): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks. Let
$\mathcal{F}_2$ be the set of
all patchworks $P_2 = (G_2, \mu, \Delta)$ such that there exist $(G_1, \mu, \Delta) \in
\mathcal{F}_1$ and $v \in V(G_1) \setminus \bar{\pi}(G_1)$ such that $G_2^- = G_1^-$ and
$\pi(G_2)$ is the concatenation of $\pi(G_1)$ with a new last term $v$ and $v$ is incident
with some edge $e \in dom(\mu)$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_3_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁) :
    WellBehaved {P₂ | ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂ ∧ ∃ v e, P₂.G.roots = P₁.G.roots ++ [v] ∧
      e ∈ P₁.dom ∧ P₁.G.Inc e v} := by
  obtain ⟨N, hN⟩ := theorem_4_1_proof h
  refine (WellBehaved.iUnion_lt (𝓕 := addRootSet 𝓕₁) N
    fun r _ ↦ wellBehaved_addRootSet h r).mono ?_
  rintro P₂ ⟨P₁, hP₁, hb, v, e, hr, he, hinc⟩
  have hmem : v ∈ P₁.μ e := by
    have : v ∈ {v | v ∈ P₁.μ e} := (P₁.μ_set e he).symm ▸ hinc
    exact this
  obtain ⟨r, hr₁, hr₂⟩ := List.getElem_of_mem hmem
  simp only [mem_iUnion, exists_prop]
  exact ⟨r, (hr₁.trans_le (hN P₁ hP₁ e he)), P₁, hP₁, hb, v, e, hr, he,
    List.getElem?_eq_some_iff.mpr ⟨hr₁, hr₂⟩⟩

/-- Graph Minors XX, (4.4) (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks, and
let $\mathcal{F}_2$ be the set
of all rootless patchworks $P_2 = (G_2, \mu, \Delta)$ such that there exists $(G_1, \mu,
\Delta) \in \mathcal{F}_1$ with $G_1^- = G_2^-$. Then $\mathcal{F}_2$ is well-behaved." The paper's
reason: "any realization expansion of one
patchwork in another is a realizable expansion of the corresponding patchworks with roots
forgotten". -/
theorem theorem_4_4_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁) :
    WellBehaved {P₂ | P₂.G.roots = [] ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂} := by
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦ ⟨Ω₂, inferInstance, hΩ₂, ?_⟩
  let R : Patchwork Ω₂ α β → Patchwork Ω₂ α β → Prop := fun Q S ↦
    Q.G.roots = [] ∧ SameBase Q S ∧ ∀ e, S.φ e = Q.φ e
  refine ⟨R, ?_, ?_⟩
  · rintro Q ⟨P₂, ⟨hr, P₁, hP₁, hb⟩, hQ⟩
    refine ⟨P₁.relabel Q.φ, ⟨P₁, hP₁, isCompletionOf_relabel _ _⟩, ?_, ?_, fun _ ↦ rfl⟩
    · rw [hQ.G_eq, hr]
    · exact (hb.trans hQ.sameBase).symm.trans (isCompletionOf_relabel _ _).sameBase
  · rintro Q - Q' - S S' ⟨hr, hb, hφ⟩ ⟨hr', hb', hφ'⟩ ⟨ηv, ηe, hη⟩
    refine ⟨ηv, ηe, realizable_transfer hη hb.symm hb'.symm (fun e he ↦ ?_) (by simp [hr, hr']) ?_⟩
    · have := hη.1.φ_le e (hb.edgeSet_eq ▸ he)
      rwa [hφ, hφ'] at this
    · intro i hi
      simp [hr] at hi

/-- The patchworks of (4.5) with exactly `k` roots. -/
def rootedSet (𝓕₁ : Set (UnlabeledPatchwork α β)) (k : ℕ) : Set (UnlabeledPatchwork α β) :=
  {P₂ | P₂.G.roots.length = k ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂}

/-- Graph Minors XX, (4.5) (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of active
patchworks, let $k \ge 0$ and let
$\mathcal{F}_2$ be the set of all patchworks $(G_2, \mu, \Delta)$ such that
$|\bar{\pi}(G_2)| \le k$ and there exists $(G_1, \mu, \Delta) \in \mathcal{F}_1$ with $G_1^-
= G_2^-$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_5_proof {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) (k : ℕ) :
    WellBehaved {P₂ | P₂.G.roots.length ≤ k ∧ ∃ P₁ ∈ 𝓕₁, SameBase P₁ P₂} := by
  -- By induction on `k'`, using (4.4) for `k' = 0` and (4.3) for the step.
  have hk : ∀ k', WellBehaved (rootedSet 𝓕₁ k') := by
    intro k'
    induction k' with
    | zero =>
      refine (theorem_4_4_proof h).mono ?_
      rintro P₂ ⟨hl, P₁, hP₁, hb⟩
      exact ⟨List.length_eq_zero_iff.mp hl, P₁, hP₁, hb⟩
    | succ k' ih =>
      refine (theorem_4_3_proof ih).mono ?_
      rintro P₂ ⟨hl, P₁, hP₁, hb⟩
      -- Remove the last root.
      obtain ⟨r, v, hr⟩ : ∃ r v, P₂.G.roots = r ++ [v] := by
        rcases List.eq_nil_or_concat P₂.G.roots with h0 | ⟨r, v, hr⟩
        · simp [h0] at hl
        · exact ⟨r, v, by simpa using hr⟩
      have hnd : r.Nodup := by
        have := P₂.G.roots_nodup
        rw [hr] at this
        exact (List.nodup_append.mp this).1
      have hs : ∀ w ∈ r, w ∈ P₂.G.vertexSet := fun w hw ↦ P₂.G.roots_subset w (by simp [hr, hw])
      have hbp : SameBase P₂ (P₂.reroot r hnd hs) := ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
      have hvmem : v ∈ P₁.G.vertexSet := by
        have := P₂.G.roots_subset v (by simp [hr])
        rwa [hb.vertexSet_eq] at this
      obtain ⟨e, he, hinc⟩ := ha P₁ hP₁ v hvmem
      refine ⟨P₂.reroot r hnd hs, ⟨?_, P₁, hP₁, hb.trans hbp⟩, hbp.symm, v, e, hr, ?_, ?_⟩
      · change r.length = k'
        have := congrArg List.length hr
        simp at this
        omega
      · exact (hb.trans hbp).dom_eq ▸ he
      · have hI := (hb.trans hbp).inc_eq
        change (P₂.reroot r hnd hs).G.Inc e v
        rw [hI]
        exact hinc
  refine (WellBehaved.iUnion_lt (𝓕 := rootedSet 𝓕₁) (k + 1) fun i _ ↦ hk i).mono ?_
  rintro P₂ ⟨hl, hex⟩
  simp only [mem_iUnion, exists_prop]
  exact ⟨_, Nat.lt_succ_of_le hl, rfl, hex⟩

end GraphMinor.GM20
