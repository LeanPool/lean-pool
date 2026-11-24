/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4a
public import LeanPool.GraphMinor.GM20.Codes

/-!
# Graph Minors XX, Section 4, (4.6)

This file proves (4.6): adding one edge with all ends among the roots keeps a set well-behaved. The
paper calls the proof clear. Members of a well-behaved set have boundedly many roots, so the new
edge
has one of finitely many codes (`edgeCode`) relative to the roots. Along a sequence of completions
we
pass to a subsequence on which that code is constant and the label of the new edge increases. Then
an
expansion of the patchworks without the new edges extends by sending new edge to new edge
(`simulated_add_edge`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem IsCompletionOf.trans {Ω₁ Ω₂ Ω₃ : Type*} {P : Patchwork Ω₁ α β} {Q : Patchwork Ω₂ α β}
    {R : Patchwork Ω₃ α β} (h : IsCompletionOf P Q) (h' : IsCompletionOf Q R) :
    IsCompletionOf P R where
  G_eq := h'.G_eq.trans h.G_eq
  dom_eq := h'.dom_eq.trans h.dom_eq
  μ_eq _ he := (h'.μ_eq (h.dom_eq ▸ he)).trans (h.μ_eq he)
  Δ_eq _ he := by
    have hE : Q.G.edgeSet = P.G.edgeSet := congrArg (·.edgeSet) h.G_eq
    exact (h'.Δ_eq (hE ▸ he)).trans (h.Δ_eq he)

theorem IsCompletionOf.symm {Ω₁ Ω₂ : Type*} {P : Patchwork Ω₁ α β} {Q : Patchwork Ω₂ α β}
    (h : IsCompletionOf P Q) : IsCompletionOf Q P where
  G_eq := h.G_eq.symm
  dom_eq := h.dom_eq.symm
  μ_eq _ he := (h.μ_eq (h.dom_eq ▸ he)).symm
  Δ_eq _ he := (h.Δ_eq ((congrArg (·.edgeSet) h.G_eq) ▸ he)).symm

theorem IsCompletionOf.deleteEdges {Ω₁ Ω₂ : Type*} {P : Patchwork Ω₁ α β} {Q : Patchwork Ω₂ α β}
    (h : IsCompletionOf P Q) (F : Set β) : IsCompletionOf (P.deleteEdges F) (Q.deleteEdges F) where
  G_eq := by
    change Q.G.deleteEdges F = P.G.deleteEdges F
    rw [h.G_eq]
  dom_eq := by
    change Q.dom \ F = P.dom \ F
    rw [h.dom_eq]
  μ_eq _ he := h.μ_eq he.1
  Δ_eq _ he := h.Δ_eq he.1

/-- Members of a well-behaved set have boundedly many roots: an expansion keeps the number of roots,
so a sequence with strictly increasing numbers of roots has no simulated pair. -/
theorem WellBehaved.exists_roots_le {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) :
    ∃ N, ∀ P ∈ 𝓕, P.G.roots.length ≤ N := by
  by_contra hcon
  push Not at hcon
  choose P hP hL using hcon
  let g : ℕ → ℕ := fun k ↦ Nat.rec 0 (fun _ m ↦ (P m).G.roots.length) k
  have hg : StrictMono g := strictMono_nat_of_lt_succ fun k ↦ hL (g k)
  let Ω := ULift.{max u v} (Discrete Unit)
  let _ : Preorder Ω := Preorder.lift ULift.down
  have hΩ : WellQuasiOrderedLE Ω := by
    have h₀ := wqo_discrete Unit
    exact ⟨fun f ↦ h₀.wqo (fun n ↦ (f n).down)⟩
  obtain ⟨i, j, hij, ηv, ηe, hη, -⟩ := h Ω hΩ (fun k ↦ (P (g k)).relabel fun _ ↦ ⟨()⟩) fun k ↦
    ⟨P (g k), hP _, isCompletionOf_relabel _ _⟩
  have h₃ : g (i + 1) = g (j + 1) := hη.roots_length
  exact (hg (Nat.succ_lt_succ hij)).ne h₃

variable {Ω : Type*} [Preorder Ω]

/-- A realizable expansion of `Q \ f` in `Q' \ f'` extends to one of `Q` in `Q'` by `f ↦ f'`, when
the
ends of `f` and `f'` are roots, the edges have the same code relative to the roots, and the label
does
not go down. -/
theorem simulated_add_edge {k : ℕ} {Q Q' : Patchwork Ω α β} {f f' : β} (hf : f ∈ Q.G.edgeSet)
    (hf' : f' ∈ Q'.G.edgeSet) (hr : Q.G.roots.length ≤ k) (hr' : Q'.G.roots.length ≤ k)
    (hends : ∀ v, Q.G.Inc f v → v ∈ Q.G.roots) (hends' : ∀ v, Q'.G.Inc f' v → v ∈ Q'.G.roots)
    (hc : edgeCode k Q.G.roots Q f = edgeCode k Q'.G.roots Q' f') (hφ : Q.φ f ≤ Q'.φ f')
    (h : Simulated (Q.deleteEdges {f}) (Q'.deleteEdges {f'})) : Simulated Q Q' := by
  classical
  obtain ⟨ηv, ηe, hη, H, hH, hcomp⟩ := h
  obtain ⟨hcd, hci, hcm, hcp⟩ : (f ∈ Q.dom ↔ f' ∈ Q'.dom) ∧
      indexSet k Q.G.roots (Q.G.ends f) = indexSet k Q'.G.roots (Q'.G.ends f') ∧
      marchCode k Q.G.roots (Q.μ f) = marchCode k Q'.G.roots (Q'.μ f') ∧
      patchCode k Q.G.roots (Q.Δ f) = patchCode k Q'.G.roots (Q'.Δ f') := by
    simp only [edgeCode, Prod.mk.injEq] at hc
    exact ⟨iff_of_eq hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  have hE : ∀ e ∈ Q.G.edgeSet, e ≠ f → e ∈ (Q.deleteEdges {f}).G.edgeSet :=
    fun e he hne ↦ ⟨he, hne⟩
  have hEη : ∀ e ∈ Q.G.edgeSet, e ≠ f → ηe e ∈ Q'.G.edgeSet ∧ ηe e ≠ f' := fun e he hne ↦
    hη.edge_mem e (hE e he hne)
  have hroot : ∀ (i : Fin k) (x y : α), Q.G.roots[i.1]? = some x → Q'.G.roots[i.1]? = some y →
      y ∈ ηv x := by
    intro i x y hx hy
    obtain ⟨h₁, h₂⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨h₁', h₂'⟩ := List.getElem?_eq_some_iff.mp hy
    have := hη.roots_mem i.1 h₁ h₁'
    change Q'.G.roots[i.1] ∈ ηv Q.G.roots[i.1] at this
    rwa [h₂, h₂'] at this
  have hμ : ∀ (hd : f ∈ Q.dom), (Q.μ f).length = (Q'.μ f').length ∧
      (∀ x ∈ Q.μ f, x ∈ Q.G.roots) ∧ (∀ x ∈ Q'.μ f', x ∈ Q'.G.roots) := by
    intro hd
    have hd' := hcd.mp hd
    have hs : ∀ x ∈ Q.μ f, x ∈ Q.G.roots := fun x hx ↦ hends x
      (by have : x ∈ {x | x ∈ Q.μ f} := hx
          rw [Q.μ_set f hd] at this
          exact this)
    have hs' : ∀ x ∈ Q'.μ f', x ∈ Q'.G.roots := fun x hx ↦ hends' x
      (by have : x ∈ {x | x ∈ Q'.μ f'} := hx
          rw [Q'.μ_set f' hd'] at this
          exact this)
    exact ⟨length_eq_of_code hr hr' (Q.μ_nodup f hd) (Q'.μ_nodup f' hd') hs hs' hcm, hs, hs'⟩
  refine ⟨ηv, fun e ↦ if e = f then f' else ηe e, ?_, H, ?_, hcomp⟩
  · refine
    { vertex_nonempty := hη.vertex_nonempty
      vertex_subset := hη.vertex_subset
      edge_mem := fun e he ↦ ?_
      vertex_disjoint := hη.vertex_disjoint
      edge_injOn := ?_
      mem_dom_iff := fun e he ↦ ?_
      ends_nonempty := fun e he hd v hv ↦ ?_
      μ_length := fun e he ↦ ?_
      μ_mem := fun e he i hi hi' ↦ ?_
      roots_length := hη.roots_length
      roots_mem := hη.roots_mem
      maps_Δ := fun e he ↦ ?_
      φ_le := fun e he ↦ ?_ }
    · by_cases hef : e = f
      · simpa [hef] using hf'
      · simpa [hef] using (hEη e he hef).1
    · intro e₁ h₁ e₂ h₂ heq
      by_cases h₃ : e₁ = f <;> by_cases h₄ : e₂ = f
      · exact h₃.trans h₄.symm
      · simp only [h₃, h₄, ite_true, ite_false] at heq
        exact absurd heq.symm (hEη e₂ h₂ h₄).2
      · simp only [h₃, h₄, ite_true, ite_false] at heq
        exact absurd heq (hEη e₁ h₁ h₃).2
      · simp only [h₃, h₄, ite_false] at heq
        exact hη.edge_injOn (hE e₁ h₁ h₃) (hE e₂ h₂ h₄) heq
    · by_cases hef : e = f
      · simpa [hef] using hcd
      · have := hη.mem_dom_iff e (hE e he hef)
        simp only [hef, ite_false]
        exact ⟨fun hd ↦ (this.mp ⟨hd, hef⟩).1, fun hd ↦ (this.mpr ⟨hd, (hEη e he hef).2⟩).1⟩
    · by_cases hef : e = f
      · subst hef
        obtain ⟨i, hi⟩ := exists_index hr (hends v hv)
        have hmem : i ∈ indexSet k Q'.G.roots (Q'.G.ends f') :=
          hci ▸ (⟨v, hv, hi⟩ : i ∈ indexSet k Q.G.roots (Q.G.ends e))
        obtain ⟨y, hy, hyi⟩ := hmem
        simp only [ite_true]
        exact ⟨y, hroot i v y hi hyi, hy⟩
      · obtain ⟨y, hy, hinc⟩ := hη.ends_nonempty e (hE e he hef) (fun h ↦ hd h.1) v ⟨hv, hef⟩
        simp only [hef, ite_false]
        exact ⟨y, hy, hinc.1⟩
    · by_cases hef : e = f
      · subst hef
        simpa using (hμ he).1
      · simp only [hef, ite_false]
        exact hη.μ_length e ⟨he, hef⟩
    · by_cases hef : e = f
      · subst hef
        obtain ⟨hlen, hs, hs'⟩ := hμ he
        simp only [ite_true] at hi' ⊢
        have hx := List.getElem_mem hi
        obtain ⟨j, hj⟩ := exists_index hr (hs _ hx)
        obtain ⟨y, hy, hyj⟩ := marchCode_forward hcm
          ((length_le_of_subset (Q.μ_nodup e he) hs).trans hr)
          (List.getElem?_eq_getElem hi) hj
        have h₀ : (Q'.μ f')[i] = y := by
          rw [List.getElem?_eq_getElem hi'] at hy
          exact Option.some.inj hy
        rw [h₀]
        exact hroot j _ y hj hyj
      · have := hη.μ_mem e ⟨he, hef⟩ i
        simp only [hef, ite_false] at hi' ⊢
        exact this hi hi'
    · by_cases hef : e = f
      · subst hef
        obtain ⟨hlen, hs, hs'⟩ := hμ he
        have hd' := hcd.mp he
        have hEe := Q.dom_subset he
        have hEf := Q'.dom_subset hd'
        simp only [ite_true]
        refine mapsTo_of_code hr hr' (Q.μ_nodup e he) (Q'.μ_nodup f' hd') hs hs' ?_ ?_ hcm hcp
        · rw [Q.Δ_verts e hEe, Q.μ_set e he]
        · rw [Q'.Δ_verts f' hEf, Q'.μ_set f' hd']
      · simp only [hef, ite_false]
        exact hη.maps_Δ e ⟨he, hef⟩
    · by_cases hef : e = f
      · subst hef
        simpa using hφ
      · simp only [hef, ite_false]
        exact hη.φ_le e ⟨he, hef⟩
  · have himg : (fun e ↦ if e = f then f' else ηe e) '' Q.G.edgeSet =
        insert f' (ηe '' (Q.G.edgeSet \ {f})) := by
      ext y
      constructor
      · rintro ⟨e, he, rfl⟩
        by_cases hef : e = f
        · simp [hef]
        · exact Or.inr ⟨e, ⟨he, hef⟩, by simp [hef]⟩
      · rintro (rfl | ⟨e, he, rfl⟩)
        · exact ⟨f, hf, by simp⟩
        · exact ⟨e, he.1, by simp [show e ≠ f from he.2]⟩
    refine hH.congr rfl ?_ fun _ _ ↦ rfl
    change Q'.G.edgeSet \ _ = (Q'.G.edgeSet \ {f'}) \ ηe '' (Q.G.edgeSet \ {f})
    rw [himg, Set.sdiff_sdiff, Set.singleton_union]

variable (Ω) in
/-- The data of the new edge of (4.6) along a sequence. -/
abbrev EdgeData (k : ℕ) : Type _ := Discrete (EdgeCode k) × Ω

/-- Graph Minors XX, (4.6) (page 332): "Let $\mathcal{F}_1$ be a well-behaved set of patchworks, and
let $\mathcal{F}_2$ be a set of
patchworks such that for each $P_2 = (G_2, \mu_2, \Delta_2) \in \mathcal{F}_2$ there exists
$f \in E(G_2)$ such that $P_2 \setminus \{f\} \in \mathcal{F}_1$ and every end of $f$
belongs to $\bar{\pi}(G_2)$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_6_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ f ∈ P₂.G.edgeSet, P₂.deleteEdges {f} ∈ completions Unit 𝓕₁ ∧
      ∀ v, P₂.G.Inc f v → v ∈ P₂.G.roots) : WellBehaved 𝓕₂ := by
  intro Ω _ hΩ Q hQ
  classical
  obtain ⟨k, hk⟩ := h.exists_roots_le
  choose P hP hPQ using hQ
  choose f hf hdel hends using fun n ↦ h₂ (P n) (hP n)
  -- Each `Q n \ f n` is a completion of a member of `𝓕₁`.
  have hcompl : ∀ n, ∃ P₁ ∈ 𝓕₁, IsCompletionOf P₁ ((Q n).deleteEdges {f n}) := by
    intro n
    obtain ⟨P₁, hP₁, hc⟩ := hdel n
    exact ⟨P₁, hP₁, hc.trans ((hPQ n).deleteEdges _)⟩
  have hbase : ∀ n, SameBase (P n) (Q n) := fun n ↦ (hPQ n).sameBase
  have hrb : ∀ n, (Q n).G.roots.length ≤ k := by
    intro n
    obtain ⟨P₁, hP₁, hc⟩ := hcompl n
    have := hk P₁ hP₁
    have hr : ((Q n).deleteEdges {f n}).G.roots = P₁.G.roots := congrArg (·.roots) hc.G_eq
    change (Q n).G.roots.length ≤ k
    have hr' : (Q n).G.roots = P₁.G.roots := hr
    rwa [hr']
  have hG : ∀ n, (Q n).G = (P n).G := fun n ↦ (hPQ n).G_eq
  have hcodeWqo : WellQuasiOrderedLE (Discrete (EdgeCode k)) := wqo_discrete _
  have hwqo : WellQuasiOrdered (α := EdgeData Ω k) (· ≤ ·) :=
    (inferInstance : WellQuasiOrderedLE (EdgeData Ω k)).wqo
  obtain ⟨g, hg⟩ := hwqo.exists_monotone_subseq
    (fun n ↦ ((edgeCode k (Q n).G.roots (Q n) (f n) : EdgeCode k), (Q n).φ (f n)))
  obtain ⟨i, j, hij, hsim⟩ := h Ω hΩ (fun n ↦ (Q (g n)).deleteEdges {f (g n)}) fun n ↦ hcompl _
  refine ⟨g i, g j, g.strictMono hij, ?_⟩
  obtain ⟨hc, hφ⟩ := hg i j hij.le
  refine simulated_add_edge (k := k) ?_ ?_ (hrb _) (hrb _) ?_ ?_ hc hφ hsim
  · rw [hG]; exact hf _
  · rw [hG]; exact hf _
  · rw [hG]; exact hends _
  · rw [hG]; exact hends _

end GraphMinor.GM20
