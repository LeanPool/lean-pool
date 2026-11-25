/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section6Stars
import LeanPool.GraphMinor.GM04.Patchwork.Menger
import LeanPool.GraphMinor.GM18.Section4
import LeanPool.GraphMinor.GM18.Section5
import LeanPool.GraphMinor.Thomas.RootedTree

/-!
# Graph Minors XVIII, Section 6: Well-Quasi-Ordering (Main Theorem 6.7)

This file completes Section 6 of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108, by proving the main theorem (6.7) (pages 106–107) and re-exporting (6.1)–(6.6)
from `Section6Part1` and `Section6Part2`:

* `lemma_6_7_claim_1` (6.7, claim (1), page 106): `𝒞* = enlargementClass 𝒞 𝒞'` is well-behaved,
  where `𝒞'` is the class of robust partial `Ω`-patchworks of tree-width `≤ 3θ + 1`.
* `lemma_6_7_claim_2` (6.7, claim (2), page 106): for `P ∈ 𝒟` such that `G⁻` has a tangle of order
  `≥ (4/3) θ`, applying (4.4) yields a proper, rotund tree-decomposition `(T, τ)` of `G⁻` whose edge
  separations are robust and whose vertex locations are enlargements of isolating places with hearts
  in `𝒞` by tree-width `≤ 3θ + 1`.
* `lemma_6_7_claim_3` (6.7, claim (3), pages 106–107): every piece of `P` at `t` under `(T, τ)` is
  robust and belongs to `𝒞*`.
* `lemma_6_7_claim_4` (6.7, claim (4), page 107): for every `P ∈ 𝒟'`, there is a rotund, proper
  tree-decomposition `(T, τ)` of `G⁻` such that all pieces of `P` under `(T, τ)` belong to `𝒞*`.
* `theorem_6_7` (6.7, pages 106–107): the class `𝒟` of rootless, robust `Ω`-patchworks whose
  tangles of order `≥ θ` are `θ`-isolated by `Ω`-places with hearts in `𝒞` is well-quasi-ordered by
  simulation.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w w'

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## Helper lemmas for Claim (3) and Theorem (6.7) -/

/-- The class `𝒞'` of all robust partial `Ω`-patchworks of patchwork tree-width `≤ w`
(Graph Minors XVIII, proof of (6.7), page 106). -/
def robustBoundedTWClass (Ω : Type w) (α : Type u) (β : Type v) (w : ℕ) :
    Set (PartialPatchwork Ω α β) :=
  {Q | Q.IsRobust ∧ HasPatchworkTreeWidthLE Q w}

/-- **Graph Minors XVIII, (6.7), Claim (1)** (page 106):
"`𝒞*` is well-behaved." -/
theorem lemma_6_7_claim_1
    [Preorder Ω] {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞) (θ : ℕ) :
    WellBehaved (enlargementClass 𝒞 (robustBoundedTWClass Ω α β (3 * θ + 1))) :=
  theorem_6_3_proof h𝒞 (theorem_6_2_proof (3 * θ + 1))

/-- **Graph Minors XVIII, (6.7), Claim (2)** (page 106):
"There is a tree-decomposition $(T, \tau)$ of $G^-$ such that* *(a) $(T, \tau)$ is proper and
rotund,* *(b) for each $e \in E(T)$, the separations made by $e$ under $(T, \tau)$ are
robust, and* *(c) for each $t \in V(T)$, if $\mathscr{L}_t$ is the location of $t$ in $(T,
\tau)$, then there is an $\Omega$-place $(P, \mathscr{L})$ with heart in $\mathscr{C}$, such
that $\mathscr{L}_t$ is an enlargement of $\mathscr{L}^-$ by tree-width $\le 3\theta + 1$." -/
theorem lemma_6_7_claim_2 {Λ : Type w'} [LinearOrder Λ]
    {𝒞 : Set (PartialPatchwork Ω α β)} {θ : ℕ} (hθ : 1 ≤ θ)
    {P : GM04.Patchwork Ω α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker P.G.toHypergraph lam)
    (hex_tangle : ∃ (θ₀ : ℕ) (𝒯₀ : Set (Hypergraph α β × Hypergraph α β)),
      4 * θ ≤ 3 * θ₀ ∧ GM10.IsTangle P.G.toHypergraph θ₀ 𝒯₀)
    (hiso : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → GM10.IsTangle P.G.toHypergraph θ' 𝒯 →
      ∃ (ℒ : Set (RootedHypergraph α β)) (P' : PartialPatchwork Ω α β),
        IsOmegaPlace (toPartialPatchwork P) ℒ ∧
        HasPlaceHeart (toPartialPatchwork P) ℒ P' ∧
        P' ∈ 𝒞 ∧
        Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ)) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      1 ≤ n ∧
      GM10.IsTreeDecomposition P.G.toHypergraph T τ ∧
      IsProper P.G.toHypergraph T τ ∧
      IsRotund P.G.toHypergraph T τ ∧
      (∀ ⦃e : Sym2 (Fin n)⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
        GM10.MakesSeparation T τ e A B → GM10.IsRobust P.G.toHypergraph A B) ∧
      (∀ t : Fin n, ∃ (ℒ : Set (RootedHypergraph α β)) (P' : PartialPatchwork Ω α β),
        IsOmegaPlace (toPartialPatchwork P) ℒ ∧
        HasPlaceHeart (toPartialPatchwork P) ℒ P' ∧
        P' ∈ 𝒞 ∧
        IsLocationEnlargementByTreeWidth P.G.toHypergraph
          (rootedLocationToLocation P.G ℒ) (vertexLocation T τ t) (3 * θ + 1)) := by
  classical
  let G := P.G.toHypergraph
  let choosePlace : Set (Hypergraph α β × Hypergraph α β) →
      Set (RootedHypergraph α β) × PartialPatchwork Ω α β := fun 𝒯 ↦
    if h : ∃ θ' : ℕ, θ ≤ θ' ∧ GM10.IsTangle G θ' 𝒯 then
      let hex := hiso h.choose_spec.1 h.choose_spec.2
      (hex.choose, hex.choose_spec.choose)
    else
      (∅, toPartialPatchwork P)
  have hchoose_spec : ∀ {θ' : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)},
      θ ≤ θ' → GM10.IsTangle G θ' 𝒯 →
      IsOmegaPlace (toPartialPatchwork P) (choosePlace 𝒯).1 ∧
      HasPlaceHeart (toPartialPatchwork P) (choosePlace 𝒯).1 (choosePlace 𝒯).2 ∧
      (choosePlace 𝒯).2 ∈ 𝒞 ∧
      Isolates G lam θ 𝒯 (rootedLocationToLocation P.G (choosePlace 𝒯).1) := by
    intro θ' 𝒯 hle h𝒯
    have hex : ∃ θ₁ : ℕ, θ ≤ θ₁ ∧ GM10.IsTangle G θ₁ 𝒯 := ⟨θ', hle, h𝒯⟩
    dsimp only [choosePlace]
    rw [dite_eq_left hex]
    exact (hiso hex.choose_spec.1 hex.choose_spec.2).choose_spec.choose_spec
  let L : Set (Hypergraph α β × Hypergraph α β) → Set (Hypergraph α β × Hypergraph α β) :=
    fun 𝒯 ↦ rootedLocationToLocation P.G (choosePlace 𝒯).1
  have hiso_L : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → GM10.IsTangle G θ' 𝒯 → Isolates G lam θ 𝒯 (L 𝒯) :=
    fun _ _ hle h𝒯 ↦ (hchoose_spec hle h𝒯).2.2.2
  obtain ⟨n, T, τ, hn, htd, hprop, hrot, hrob, hloc⟩ :=
    theorem_4_4_proof G lam hlam θ hθ L hiso_L hex_tangle
  refine ⟨n, T, τ, hn, htd, hprop, hrot, hrob, fun t ↦ ?_⟩
  obtain ⟨θ', 𝒯, hθ'_ge, h𝒯, _, henl⟩ := hloc t
  have hθ_le : θ ≤ θ' := by omega
  have hspec := hchoose_spec hθ_le h𝒯
  exact ⟨(choosePlace 𝒯).1, (choosePlace 𝒯).2, hspec.1, hspec.2.1, hspec.2.2.1, henl⟩

/-- Separation order inequality in Claim (3) of (6.7) (page 107):
If `(A, B)` is a separation of `G`, `(C₁, C₂)` is a separation of `A`, `Y ⊆ V(A ∩ B) ∩ V(C₂)`,
and `|V(A ∩ B)| ≤ |V(C₁ ∩ (B ∪ C₂))|`, then `|Y| ≤ |V(C₁ ∩ C₂)|`. -/
private theorem ncard_le_separationOrder_of_le_union {A B C₁ C₂ : Hypergraph α β}
    (hCD : A.IsSeparation C₁ C₂) {Y : Set α}
    (hY_AB : Y ⊆ (A ∩ B).vertexSet) (hY_C₂ : Y ⊆ C₂.vertexSet)
    (hord : separationOrder A B ≤ separationOrder C₁ (B ∪ C₂)) :
    Y.ncard ≤ separationOrder C₁ C₂ := by
  have hsub : (C₁ ∩ (B ∪ C₂)).vertexSet ⊆
      (C₁ ∩ C₂).vertexSet ∪ ((A ∩ B).vertexSet \ Y) := by
    intro v ⟨hvC₁, hvBC₂⟩
    by_cases hvC₂ : v ∈ C₂.vertexSet
    · exact Or.inl ⟨hvC₁, hvC₂⟩
    · refine Or.inr ⟨⟨hCD.left_le.vertexSet_subset hvC₁, hvBC₂.resolve_right hvC₂⟩, ?_⟩
      intro hvY
      exact hvC₂ (hY_C₂ hvY)
  have hfin_union : ((C₁ ∩ C₂).vertexSet ∪ ((A ∩ B).vertexSet \ Y)).Finite :=
    (C₁ ∩ C₂).vertexSet_finite.union ((A ∩ B).vertexSet_finite.sdiff)
  have hcard_le : separationOrder C₁ (B ∪ C₂) ≤
      separationOrder C₁ C₂ + ((A ∩ B).vertexSet \ Y).ncard :=
    (Set.ncard_le_ncard hsub hfin_union).trans (Set.ncard_union_le _ _)
  have hY_fin : Y.Finite := (A ∩ B).vertexSet_finite.subset hY_AB
  have hdiff_eq : ((A ∩ B).vertexSet \ Y).ncard =
      separationOrder A B - Y.ncard :=
    Set.ncard_sdiff hY_AB hY_fin
  have hY_le_AB : Y.ncard ≤ separationOrder A B :=
    Set.ncard_le_ncard hY_AB (A ∩ B).vertexSet_finite
  omega

/-- Counting argument in Claim (3) of (6.7) (page 107):
If `X₁, X₂ ⊆ V` are disjoint with `|X₁| = |X₂|`, `k = |V \ X₁|`, and `H` is a subgraph with `k`
distinct components `D i` (`i : Fin k`), each meeting both `V \ X₁` and `V \ X₂`, then the
grouping `K` on `V` induced by connectivity in `H` is a pairing in `V` that pairs `X₁, X₂`. -/
private theorem isPairing_and_pairs_of_components {V X₁ X₂ : Set α} (hV : V.Finite)
    (hX₁ : X₁ ⊆ V) (hX₂ : X₂ ⊆ V) (hcard : X₁.ncard = X₂.ncard) (hdisj : Disjoint X₁ X₂)
    {H K : (⊤ : SimpleGraph α).Subgraph} (hK_verts : K.verts = V)
    (hK_adj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → (ConnectedIn H u v ↔ K.Adj u v))
    {k : ℕ} (hk : k = (V \ X₁).ncard)
    {D : Fin k → (⊤ : SimpleGraph α).Subgraph} (hD_inj : Function.Injective D)
    (hD : ∀ i : Fin k, GM04.IsComponent H (D i) ∧
      ((D i).verts ∩ (V \ X₁)).Nonempty ∧ ((D i).verts ∩ (V \ X₂)).Nonempty) :
    GM04.IsPairing V K ∧ GM04.Pairs V K X₁ X₂ := by
  classical
  let Y₁ := V \ X₁
  let Y₂ := V \ X₂
  have hY₁_fin : Y₁.Finite := hV.sdiff
  have hY₂_fin : Y₂.Finite := hV.sdiff
  have hk₂ : k = Y₂.ncard := by
    rw [hk, Set.ncard_sdiff hX₁ (hV.subset hX₁), Set.ncard_sdiff hX₂ (hV.subset hX₂), hcard]
  have hY_union : Y₁ ∪ Y₂ = V := by
    ext v
    simp only [Y₁, Y₂, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      by_cases hv₁ : v ∈ X₁
      · exact Or.inr ⟨hv, Set.disjoint_left.1 hdisj hv₁⟩
      · exact Or.inl ⟨hv, hv₁⟩
  have hD_disj : ∀ {i j : Fin k}, i ≠ j → Disjoint (D i).verts (D j).verts :=
    fun hij ↦ (hD _).1.disjoint_verts_of_ne (hD _).1 (fun hEq ↦ hij (hD_inj hEq))
  choose y₁ hy₁_D hy₁_Y₁ using fun i : Fin k ↦ (hD i).2.1
  choose y₂ hy₂_D hy₂_Y₂ using fun i : Fin k ↦ (hD i).2.2
  have hy₁_inj : Function.Injective y₁ := by
    intro i j hEq
    by_contra hne
    exact Set.disjoint_left.1 (hD_disj hne) (hy₁_D i) (hEq ▸ hy₁_D j)
  have hy₂_inj : Function.Injective y₂ := by
    intro i j hEq
    by_contra hne
    exact Set.disjoint_left.1 (hD_disj hne) (hy₂_D i) (hEq ▸ hy₂_D j)
  have hrange₁ : Set.range y₁ = Y₁ := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ hY₁_fin
    · rintro _ ⟨i, rfl⟩; exact hy₁_Y₁ i
    · rw [Set.ncard_range_of_injective hy₁_inj, Nat.card_fin, ← hk]
  have hrange₂ : Set.range y₂ = Y₂ := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ hY₂_fin
    · rintro _ ⟨i, rfl⟩; exact hy₂_Y₂ i
    · rw [Set.ncard_range_of_injective hy₂_inj, Nat.card_fin, ← hk₂]
  have hinter₁ : ∀ (i : Fin k) {x : α}, x ∈ (D i).verts → x ∈ Y₁ → x = y₁ i := by
    intro i x hxD hxY₁
    rw [← hrange₁] at hxY₁
    obtain ⟨j, rfl⟩ := hxY₁
    by_cases hij : j = i
    · subst hij; rfl
    · exact (Set.disjoint_left.1 (hD_disj hij) (hy₁_D j) hxD).elim
  have hinter₂ : ∀ (i : Fin k) {x : α}, x ∈ (D i).verts → x ∈ Y₂ → x = y₂ i := by
    intro i x hxD hxY₂
    rw [← hrange₂] at hxY₂
    obtain ⟨j, rfl⟩ := hxY₂
    by_cases hij : j = i
    · subst hij; rfl
    · exact (Set.disjoint_left.1 (hD_disj hij) (hy₂_D j) hxD).elim
  have hinter_V : ∀ (i : Fin k) {x : α}, x ∈ (D i).verts → x ∈ V → x = y₁ i ∨ x = y₂ i := by
    intro i x hxD hxV
    rw [← hY_union] at hxV
    rcases hxV with hx₁ | hx₂
    · exact Or.inl (hinter₁ i hxD hx₁)
    · exact Or.inr (hinter₂ i hxD hx₂)
  have hex_comp : ∀ u ∈ V, ∃ i : Fin k, u ∈ (D i).verts := by
    intro u hu
    rw [← hY_union, ← hrange₁, ← hrange₂] at hu
    rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨i, hy₁_D i⟩
    · exact ⟨i, hy₂_D i⟩
  have hcomp_of_adj : ∀ {u v : α} (i : Fin k), u ∈ (D i).verts → K.Adj u v → v ∈ (D i).verts := by
    intro u v i huD huv
    have huV : u ∈ V := hK_verts ▸ K.edge_vert huv
    have hvV : v ∈ V := hK_verts ▸ K.edge_vert huv.symm
    have hconn : ConnectedIn H u v := (hK_adj u huV v hvV huv.ne).2 huv
    obtain ⟨C, hC, huC, hvC⟩ := hconn
    have hCD : C = D i := hC.eq_of_mem (hD i).1 huC huD
    exact hCD ▸ hvC
  have hpair : GM04.IsPairing V K := by
    rw [GM04.isPairing_iff hV]
    refine ⟨hK_verts.le, fun a b c hab hac ↦ ?_⟩
    have haV : a ∈ V := hK_verts ▸ K.edge_vert hab
    have hbV : b ∈ V := hK_verts ▸ K.edge_vert hab.symm
    have hcV : c ∈ V := hK_verts ▸ K.edge_vert hac.symm
    obtain ⟨i, haD⟩ := hex_comp a haV
    have hbD : b ∈ (D i).verts := hcomp_of_adj i haD hab
    have hcD : c ∈ (D i).verts := hcomp_of_adj i haD hac
    rcases hinter_V i haD haV with rfl | rfl <;>
      rcases hinter_V i hbD hbV with h1 | h1 <;>
      rcases hinter_V i hcD hcV with h2 | h2
    · exact (hab.ne h1.symm).elim
    · exact (hab.ne h1.symm).elim
    · exact (hac.ne h2.symm).elim
    · exact h1.trans h2.symm
    · exact h1.trans h2.symm
    · exact (hac.ne h2.symm).elim
    · exact (hab.ne h1.symm).elim
    · exact (hab.ne h1.symm).elim
  refine ⟨hpair, ?_⟩
  rw [GM04.pairs_iff_of_isPairing hV hpair]
  refine ⟨hX₁, hX₂, hdisj, fun u v huv ↦ ?_, fun v hv ↦ ?_⟩
  · have huV : u ∈ V := hK_verts ▸ K.edge_vert huv
    have hvV : v ∈ V := hK_verts ▸ K.edge_vert huv.symm
    obtain ⟨i, huD⟩ := hex_comp u huV
    have hvD : v ∈ (D i).verts := hcomp_of_adj i huD huv
    have hy₁_in_X₂ : y₁ i ≠ y₂ i → y₁ i ∈ X₂ := by
      intro hne
      have hy₁_V : y₁ i ∈ V := (hy₁_Y₁ i).1
      by_contra hnot
      exact hne (hinter₂ i (hy₁_D i) ⟨hy₁_V, hnot⟩)
    have hy₂_in_X₁ : y₁ i ≠ y₂ i → y₂ i ∈ X₁ := by
      intro hne
      have hy₂_V : y₂ i ∈ V := (hy₂_Y₂ i).1
      by_contra hnot
      exact hne (hinter₁ i (hy₂_D i) ⟨hy₂_V, hnot⟩).symm
    rcases hinter_V i huD huV with rfl | rfl <;>
      rcases hinter_V i hvD hvV with h1 | h1
    · exact (huv.ne h1.symm).elim
    · subst h1
      exact Or.inr ⟨hy₁_in_X₂ huv.ne, hy₂_in_X₁ huv.ne⟩
    · subst h1
      exact Or.inl ⟨hy₂_in_X₁ huv.ne.symm, hy₁_in_X₂ huv.ne.symm⟩
    · exact (huv.ne h1.symm).elim
  · rcases hv with hv₁ | hv₂
    · have hv_Y₂ : v ∈ Y₂ := ⟨hX₁ hv₁, Set.disjoint_left.1 hdisj hv₁⟩
      rw [← hrange₂] at hv_Y₂
      obtain ⟨i, rfl⟩ := hv_Y₂
      have hne : y₂ i ≠ y₁ i := fun hEq ↦ (hy₁_Y₁ i).2 (hEq ▸ hv₁)
      have hconn : ConnectedIn H (y₂ i) (y₁ i) := ⟨D i, (hD i).1, hy₂_D i, hy₁_D i⟩
      exact ⟨y₁ i, (hK_adj (y₂ i) (hX₁ hv₁) (y₁ i) (hy₁_Y₁ i).1 hne).1 hconn⟩
    · have hv_Y₁ : v ∈ Y₁ := ⟨hX₂ hv₂, Set.disjoint_right.1 hdisj hv₂⟩
      rw [← hrange₁] at hv_Y₁
      obtain ⟨i, rfl⟩ := hv_Y₁
      have hne : y₁ i ≠ y₂ i := fun hEq ↦ (hy₂_Y₂ i).2 (hEq ▸ hv₂)
      have hconn : ConnectedIn H (y₁ i) (y₂ i) := ⟨D i, (hD i).1, hy₁_D i, hy₂_D i⟩
      exact ⟨y₂ i, (hK_adj (y₁ i) (hX₂ hv₂) (y₂ i) (hy₂_Y₂ i).1 hne).1 hconn⟩

/-- **Graph Minors XVIII, (6.7), Claim (3)** (pages 106–107):
"Let $(T, \tau)$ be as in (2) and let $t \in V(T)$. Then every piece of $P$ at $t$ under $(T,
\tau)$ is in $\mathscr{C}^*$." -/
theorem lemma_6_7_claim_3
    {ι : Type*} [Fintype ι]
    {𝒞 : Set (PartialPatchwork Ω α β)} {θ : ℕ}
    {P : GM04.Patchwork Ω α β} (_hrootless : IsRootless P) (hrob : P.IsRobust)
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β}
    (hrobust : ∀ ⦃e : Sym2 ι⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
      GM10.MakesSeparation T τ e A B → GM10.IsRobust P.G.toHypergraph A B)
    {t : ι}
    {ℒ : Set (RootedHypergraph α β)} {P' : PartialPatchwork Ω α β}
    (hP'_heart : HasPlaceHeart (toPartialPatchwork P) ℒ P') (hP'_mem : P' ∈ 𝒞)
    (henl : IsLocationEnlargementByTreeWidth P.G.toHypergraph
      (rootedLocationToLocation P.G ℒ) (vertexLocation T τ t) (3 * θ + 1))
    {Q : PartialPatchwork Ω α β} (hQ_piece : IsPiece (toPartialPatchwork P) T τ t Q) :
    Q ∈ enlargementClass 𝒞 (robustBoundedTWClass Ω α β (3 * θ + 1)) := by
  classical
  obtain ⟨ℒ_star, _, hℒ_star_eq, hQ_heart⟩ := hQ_piece
  rw [← hℒ_star_eq] at henl
  have henl_cast : IsLocationEnlargementByTreeWidth (toPartialPatchwork P).G.toHypergraph
      (rootedLocationToLocation (toPartialPatchwork P).G ℒ)
      (rootedLocationToLocation (toPartialPatchwork P).G ℒ_star) ((3 * θ + 1 : ℕ) : ℚ) := by
    push_cast
    exact henl
  have henl_Q : IsPlaceEnlargementByTreeWidth (3 * θ + 1) P' Q :=
    theorem_5_5_proof hP'_heart hQ_heart henl_cast
  obtain ⟨ℒ_Q, hℒ_Q, hheart_Q, htw_Q⟩ := henl_Q
  -- Prove that `Q` is robust (`Q.IsRobust`).
  have hQ_rob : Q.IsRobust := by
    obtain ⟨newEdge_star, hQ_place⟩ := hQ_heart
    have hℒ_star := hQ_place.isRootedLocation
    intro e he
    rw [hQ_place.edgeSet_eq] at he
    rcases he with he_core | ⟨A, hA_star, rfl⟩
    · rw [hQ_place.Δ_core he_core]
      exact hrob e ((mem_rootedLocationCore_edgeSet_iff.1 he_core).1)
    · rw [hQ_place.Δ_newEdge hA_star]
      let P_A := (toPartialPatchwork P).restrict A
      have hcompA : IsComplemented P.G A := hℒ_star.isComplemented hA_star
      let B := (complement P.G A hcompA).toHypergraph
      have hB_eq : complementHypergraph P.G A = B :=
        complementHypergraph_eq_of_isComplemented hcompA
      have hAB_loc : (A.toHypergraph, B) ∈ vertexLocation T τ t := by
        rw [← hB_eq, ← hℒ_star_eq]
        exact ⟨A, hA_star, rfl⟩
      obtain ⟨s, hadj, hAB_eq⟩ := hAB_loc
      have hm_AB : GM10.MakesSeparation T τ s(s, t) A.toHypergraph B :=
        ⟨s, t, hadj.symm, rfl, congrArg Prod.fst hAB_eq, congrArg Prod.snd hAB_eq⟩
      have hrob_AB : GM10.IsRobust P.G.toHypergraph A.toHypergraph B :=
        hrobust (T.mem_edgeSet.2 hadj.symm) hm_AB
      have hrootA_eq : A.rootSet = (A.toHypergraph ∩ B).vertexSet :=
        hcompA.isSeparation.rootSet_left
      have hrob_PA : P_A.IsRobust := by
        have hrob_part : (toPartialPatchwork P).IsRobust := hrob
        exact isRobust_restrict hrob_part hcompA.le
      intro X₁ hX₁ X₂ hX₂ hcard hdisj
      change X₁ ⊆ A.rootSet at hX₁
      change X₂ ⊆ A.rootSet at hX₂
      let Y₁ := A.rootSet \ X₁
      let Y₂ := A.rootSet \ X₂
      let k := Y₁.ncard
      have hY₁_sub_A : Y₁ ⊆ P_A.G.vertexSet := Set.sdiff_subset.trans A.roots_subset
      have hY₂_sub_A : Y₂ ⊆ P_A.G.vertexSet := Set.sdiff_subset.trans A.roots_subset
      have hV_fin : A.rootSet.Finite := A.rootSet_finite
      have hk₂ : Y₂.ncard = k := by
        change (A.rootSet \ X₂).ncard = (A.rootSet \ X₁).ncard
        rw [Set.ncard_sdiff hX₂ (hV_fin.subset hX₂),
          Set.ncard_sdiff hX₁ (hV_fin.subset hX₁), hcard]
      have hcond1 : GM04.Theorem61Cond1 P_A Y₁ Y₂ k := by
        rw [GM04.theorem_6_1_i_iff_disjointPaths menger hY₁_sub_A hY₂_sub_A k,
          ← menger P_A.G.toHypergraph Y₁ Y₂ hY₁_sub_A hY₂_sub_A k]
        intro H₁ H₂ hsepH hY₁_H₁ hY₂_H₂
        have hY₁_AB : Y₁ ⊆ (A.toHypergraph ∩ B).vertexSet :=
          hrootA_eq ▸ Set.sdiff_subset
        have hY₂_AB : Y₂ ⊆ (A.toHypergraph ∩ B).vertexSet :=
          hrootA_eq ▸ Set.sdiff_subset
        rcases hrob_AB.2 hsepH with hord₁ | hord₂
        · rw [← hk₂]
          exact ncard_le_separationOrder_of_le_union hsepH hY₂_AB hY₂_H₂ hord₁
        · rw [GM10.separationOrder_comm H₁ H₂]
          exact ncard_le_separationOrder_of_le_union hsepH.symm hY₁_AB hY₁_H₁ hord₂
      have hcond2 : GM04.Theorem61Cond2 P_A Y₁ Y₂ k :=
        ((GM04.theorem_6_1_proof menger hrob_PA hY₁_sub_A hY₂_sub_A k).1).1 hcond1
      obtain ⟨H, D, hH, hD_inj, hD⟩ := hcond2
      obtain ⟨K, hK_feas, hK_adj⟩ := exists_isFeasibleGrouping_of_isRealization hH
      have ⟨hK_pair, hK_pairs⟩ :=
        isPairing_and_pairs_of_components hV_fin hX₁ hX₂ hcard hdisj hK_feas.2.1 hK_adj rfl
          hD_inj hD
      exact ⟨K, hK_feas, hK_pair, hK_pairs⟩
  refine ⟨P', hP'_mem, ℒ_Q, hℒ_Q, hheart_Q, fun A hA ↦ ?_⟩
  exact ⟨isRobust_restrict hQ_rob (hℒ_Q.isComplemented hA).le, htw_Q A hA⟩

/-- **Graph Minors XVIII, (6.7), Claim (4)** (page 107):
"For all $P = (G, \mu, \Delta, \phi) \in \mathscr{D}'$, there is a rotund, proper
tree-decomposition $(T, \tau)$ of $G^-$ such that all pieces of $P$ under $(T, \tau)$ belong
to $\mathscr{C}^*$." -/
theorem lemma_6_7_claim_4 {Λ : Type w'} [LinearOrder Λ]
    {𝒞 : Set (PartialPatchwork Ω α β)} {θ : ℕ} (hθ : 1 ≤ θ)
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P) (hrob : P.IsRobust)
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker P.G.toHypergraph lam)
    (hex_tangle : ∃ (θ₀ : ℕ) (𝒯₀ : Set (Hypergraph α β × Hypergraph α β)),
      4 * θ ≤ 3 * θ₀ ∧ GM10.IsTangle P.G.toHypergraph θ₀ 𝒯₀)
    (hiso : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → GM10.IsTangle P.G.toHypergraph θ' 𝒯 →
      ∃ (ℒ : Set (RootedHypergraph α β)) (P' : PartialPatchwork Ω α β),
        IsOmegaPlace (toPartialPatchwork P) ℒ ∧
        HasPlaceHeart (toPartialPatchwork P) ℒ P' ∧
        P' ∈ 𝒞 ∧
        Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ)) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      1 ≤ n ∧
      GM10.IsTreeDecomposition P.G.toHypergraph T τ ∧
      IsProper P.G.toHypergraph T τ ∧
      IsRotund P.G.toHypergraph T τ ∧
      (∀ t : Fin n, ∀ Q : PartialPatchwork Ω α β,
        IsPiece (toPartialPatchwork P) T τ t Q →
        Q ∈ enlargementClass 𝒞 (robustBoundedTWClass Ω α β (3 * θ + 1))) := by
  obtain ⟨n, T, τ, hn, htd, hprop, hrot, hrobust, hloc⟩ :=
    lemma_6_7_claim_2 hθ hlam hex_tangle hiso
  refine ⟨n, T, τ, hn, htd, hprop, hrot, fun t Q hQ ↦ ?_⟩
  obtain ⟨ℒ, P', _, hP'_heart, hP'_mem, henl⟩ := hloc t
  exact lemma_6_7_claim_3 hrootless hrob hrobust hP'_heart hP'_mem henl hQ

private theorem exists_strictMono_of_infinite {I : Set ℕ} (hI : I.Infinite) :
    ∃ sub : ℕ → ℕ, StrictMono sub ∧ ∀ m, sub m ∈ I := by
  obtain ⟨i₀, hi₀⟩ := hI.nonempty
  have hex : ∀ k : ℕ, ∃ m ∈ I, k < m := by
    intro k
    obtain ⟨m, hm, hgt⟩ := (hI.sdiff (Set.finite_le_nat k)).nonempty
    exact ⟨m, hm, not_le.1 hgt⟩
  choose next hnext_I hnext_gt using hex
  let sub : ℕ → ℕ := fun r ↦ Nat.rec i₀ (fun _ prev ↦ next prev) r
  refine ⟨sub, strictMono_nat_of_lt_succ fun r ↦ hnext_gt (sub r), fun r ↦ ?_⟩
  cases r with
  | zero => exact hi₀
  | succ r => exact hnext_I (sub r)

/-- **Graph Minors XVIII, (6.7)** (pages 106–107):
"**6.7.** *Let $\Omega$ be a well-quasi-order, let $\mathscr{C}$ be a well-behaved class of
rootless partial $\Omega$-patchworks, and let $\theta \ge 1$ be an integer. Let $\mathscr{D}$ be a
class of rootless, robust $\Omega$-patchworks and suppose that for each $P \in \mathscr{D}$ there
is a tie-breaker $\lambda$ in $\|P\|^-$ such that for every tangle $\mathscr{T}$ in $G^-$ of order
$\ge \theta$, there is an $\Omega$-place $(P, \mathscr{L})$ with heart in $\mathscr{C}$ such that
$\mathscr{L}^-$ $\theta$-isolates $\mathscr{T}$. Then $\mathscr{D}$ is well-quasi-ordered by
simulation.*"

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
theorem theorem_6_7_proof [Infinite β] [Preorder Ω]
    (hΩ : WellQuasiOrderedLE Ω)
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞)
    {θ : ℕ} (hθ : 1 ≤ θ)
    {𝒟 : Set (GM04.Patchwork Ω α β)}
    (h𝒟 : ∀ ⦃P : GM04.Patchwork Ω α β⦄, P ∈ 𝒟 →
      IsRootless P ∧ P.IsRobust ∧
      ∃ (Λ : Type w') (_ : LinearOrder Λ) (lam : Hypergraph α β × Hypergraph α β → Λ),
        GM10.IsTieBreaker P.G.toHypergraph lam ∧
        ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
          θ ≤ θ' → GM10.IsTangle P.G.toHypergraph θ' 𝒯 →
          ∃ (ℒ : Set (RootedHypergraph α β)) (P' : PartialPatchwork Ω α β),
            IsOmegaPlace (toPartialPatchwork P) ℒ ∧
            HasPlaceHeart (toPartialPatchwork P) ℒ P' ∧
            P' ∈ 𝒞 ∧
            Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ)) :
    ∀ P : ℕ → GM04.Patchwork Ω α β, (∀ i, P i ∈ 𝒟) →
      ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  intro P hP
  let HasLargeTangle : GM04.Patchwork Ω α β → Prop := fun Q ↦
    ∃ (θ₀ : ℕ) (𝒯₀ : Set (Hypergraph α β × Hypergraph α β)),
      4 * θ ≤ 3 * θ₀ ∧ GM10.IsTangle Q.G.toHypergraph θ₀ 𝒯₀
  let I₁ : Set ℕ := {i | HasLargeTangle (P i)}
  let I₂ : Set ℕ := {i | ¬ HasLargeTangle (P i)}
  have hI_union : I₁ ∪ I₂ = Set.univ := by
    ext i
    simp [I₁, I₂, em]
  have hI_inf : I₁.Infinite ∨ I₂.Infinite :=
    Set.infinite_union.1 (hI_union.symm ▸ Set.infinite_univ)
  rcases hI_inf with hI₁ | hI₂
  · -- Case 1: Infinitely many `P i` belong to `𝒟'` (`HasLargeTangle (P i)`).
    obtain ⟨sub, hsub_mono, hsub_mem⟩ := exists_strictMono_of_infinite hI₁
    let P_sub : ℕ → GM04.Patchwork Ω α β := fun m ↦ P (sub m)
    have h𝒞_star : WellBehaved (enlargementClass 𝒞 (robustBoundedTWClass Ω α β (3 * θ + 1))) :=
      lemma_6_7_claim_1 h𝒞 θ
    have hex_decomp : ∀ m : ℕ,
        ∃ (n : ℕ) (S : SimpleGraph (Fin n)) (σ : Fin n → Hypergraph α β),
          1 ≤ n ∧
          GM10.IsTreeDecomposition (P_sub m).G.toHypergraph S σ ∧
          IsProper (P_sub m).G.toHypergraph S σ ∧
          IsRotund (P_sub m).G.toHypergraph S σ ∧
          (∀ t : Fin n, ∀ Q : PartialPatchwork Ω α β,
            IsPiece (toPartialPatchwork (P_sub m)) S σ t Q →
            Q ∈ enlargementClass 𝒞 (robustBoundedTWClass Ω α β (3 * θ + 1))) := by
      intro m
      obtain ⟨hrootless_m, hrob_m, Λ, hlin, lam, hlam, hiso⟩ := h𝒟 (hP (sub m))
      let _ : LinearOrder Λ := hlin
      exact lemma_6_7_claim_4 hθ hrootless_m hrob_m hlam (hsub_mem m) hiso
    choose n S σ _ htd hprop hrot hpieces using hex_decomp
    have hrootless_sub : ∀ m, IsRootless (P_sub m) := fun m ↦ (h𝒟 (hP (sub m))).1
    have hrob_sub : ∀ m, (P_sub m).IsRobust := fun m ↦ (h𝒟 (hP (sub m))).2.1
    obtain ⟨m₁, m₂, hm₁₂, hsim⟩ :=
      theorem_6_6_proof hΩ h𝒞_star P_sub hrootless_sub hrob_sub S σ htd hrot hprop hpieces
    exact ⟨sub m₁, sub m₂, hsub_mono hm₁₂, hsim⟩
  · -- Case 2: Infinitely many `P i` belong to `𝒟 \ 𝒟'` (`¬ HasLargeTangle (P i)`).
    obtain ⟨sub, hsub_mono, hsub_mem⟩ := exists_strictMono_of_infinite hI₂
    let P_sub : ℕ → GM04.Patchwork Ω α β := fun m ↦ P (sub m)
    have h𝒞' : WellBehaved (robustBoundedTWClass Ω α β (3 * θ + 1)) :=
      theorem_6_2_proof (3 * θ + 1)
    have hsub_in_𝒞' : toPartialPatchwork '' Set.range P_sub ⊆
        robustBoundedTWClass Ω α β (3 * θ + 1) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      obtain ⟨hrootless_m, hrob_m, _⟩ := h𝒟 (hP (sub m))
      refine ⟨hrob_m, ?_⟩
      let θ₁ : ℕ := (4 * θ + 2) / 3
      have hθ₁_pos : 1 ≤ θ₁ := by omega
      have hno : ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
          GM10.IsTangle (P_sub m).G.toHypergraph θ' 𝒯 → θ' < θ₁ := by
        intro θ' 𝒯 h𝒯
        by_contra hge
        have h4 : 4 * θ ≤ 3 * θ' := by omega
        exact hsub_mem m ⟨θ', 𝒯, h4, h𝒯⟩
      have htw_22 := theorem_2_2_proof (P_sub m).G.toHypergraph hθ₁_pos hno
      have htw_le : GM10.treeWidth (P_sub m).G.toHypergraph ≤ (3 * θ + 1 : ℤ) := by omega
      obtain ⟨ι, hfin_ι, K, τ_K, hD_K, hw_K⟩ :=
        exists_isTreeDecomposition_treeDecompWidthPlusOne_eq (P_sub m).G.toHypergraph
      let _ : Fintype ι := hfin_ι
      obtain ⟨t₀⟩ := hD_K.isTree.connected.nonempty
      refine ⟨ι, hfin_ι, K, τ_K, t₀, hD_K, ?_, ?_⟩
      · unfold GM10.treeDecompWidth
        rw [hw_K]
        exact htw_le
      · change (P_sub m).G.rootSet ⊆ (τ_K t₀).vertexSet
        rw [hrootless_m]
        exact Set.empty_subset _
    have h_wqo :=
      (wellBehaved_image_toPartialPatchwork_iff hΩ (Set.range P_sub)).1 (h𝒞'.mono hsub_in_𝒞')
    obtain ⟨m₁, m₂, hm₁₂, hsim⟩ := h_wqo P_sub (fun m ↦ ⟨m, rfl⟩)
    exact ⟨sub m₁, sub m₂, hsub_mono hm₁₂, hsim⟩

end GraphMinor.GM18
end
