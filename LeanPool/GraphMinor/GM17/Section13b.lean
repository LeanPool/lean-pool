/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section13a
public import LeanPool.GraphMinor.GM10.Section8
import LeanPool.GraphMinor.Surface.AddCrosscap

import LeanPool.GraphMinor.GM17.Section8Proved

/-!
# Graph Minors XVII, Section 13: raising redundancy

This file proves (13.3) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 162-210.

- **(13.3)** (`theorem_13_3`, page 205).

The proof is by induction on `h`. If `π₀` is not redundant, then `π₀` has a simpler portrayal after
a few more vertices are moved to `Z`, and (13.2) says that `h_p` falls.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

/-- "Simpler than" for surfaces is transitive. The middle surface may come with two different
models, and the model criterion moves crosscap pairs to handles on the last surface so that the
first model still fits. -/
theorem isSimplerThan_trans {X Y W : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace W]
    (h : IsSimplerThan X Y) (h' : IsSimplerThan Y W) : IsSimplerThan X W := by
  obtain ⟨a, b, c, a₁, b₁, c₁, hX, ⟨e₁⟩, h1, h2, h3⟩ := h
  obtain ⟨a₂, b₂, c₂, a₃, b₃, c₃, ⟨e₂⟩, ⟨e₃⟩, h4, h5, h6⟩ := h'
  obtain ⟨h7, h8, h9⟩ := (modelCriterion.2 a₁ b₁ c₁ a₂ b₂ c₂).mp ⟨e₁.symm.trans e₂⟩
  obtain ha | ha := le_total a₁ a₂
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
    have hb₁ : b₁ = b₂ + 2 * j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h4
    have hc : (a₁ + j + k - j : ℕ) = a₁ + k := by omega
    obtain ⟨f⟩ := (modelCriterion.2 (a₁ + j + k) b₃ c₃ (a₁ + k) (b₃ + 2 * j) c₃).mpr
      ⟨rfl, by omega, by
      constructor
      · intro hb
        obtain rfl : j = 0 := by_contra fun hj => by have := h9.mp (by omega); omega
        omega
      · intro hb; omega⟩
    exact ⟨a, b, c, a₁ + k, b₃ + 2 * j, c₃, hX, ⟨e₃.trans f⟩, by omega, by omega, by omega⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
    have hb₂ : b₂ = b₁ + 2 * j := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h5
    obtain ⟨f⟩ := (modelCriterion.2 a₃ (b₁ + 2 * j + k) c₃ (a₃ + j) (b₁ + k) c₃).mpr
      ⟨rfl, by omega, by
      constructor
      · intro hb; omega
      · intro hb
        obtain rfl : j = 0 := by_contra fun hj => by have := h9.mpr (by omega); omega
        omega⟩
    subst hb₂ hk
    exact ⟨a, b, c, a₃ + j, b₁ + k, c₃, hX, ⟨e₃.trans f⟩, by omega, by omega, by omega⟩

variable {α : Type u} {β : Type v}

theorem isSimpler_trans {a₀ a₁ a₂ b₀ b₁ b₂ : Type*} {G₀ : Hypergraph a₀ b₀} {G₁ : Hypergraph a₁ b₁}
  {G₂ : Hypergraph a₂ b₂}
    {π₀ : Portrayal G₀} {π₁ : Portrayal G₁} {π₂ : Portrayal G₂} (h : π₀.IsSimpler π₁)
      (h' : π₁.IsSimpler π₂) : π₀.IsSimpler π₂ := by
  rcases h' with ⟨hs', hle'⟩ | ⟨ψ, hle, hex⟩
  · rcases h with ⟨hs, hle⟩ | ⟨ψ, hle, -⟩
    · exact .inl ⟨isSimplerThan_trans hs hs', hle.trans hle'⟩
    · exact Portrayal.WarpLE.trans_isSimpler ⟨ψ, hle⟩ (.inl ⟨hs', hle'⟩)
  · exact h.trans_warpLE ⟨ψ, hle⟩

/-- A separation stays one after deleting vertices. -/
theorem isSeparation_deleteVertices {G A B : Hypergraph α β} (hs : G.IsSeparation A B) (Z : Set α) :
    (G.deleteVertices Z).IsSeparation (A.deleteVertices Z) (B.deleteVertices Z) := by
  have hle : ∀ {C : Hypergraph α β}, C ≤ G → C.deleteVertices Z ≤ G.deleteVertices Z := by
    intro C hC
    have hI : ∀ e ∈ C.edgeSet, ∀ v, G.Inc e v ↔ C.Inc e v := fun e he v => by
      have h := hC.ends_eq e he
      exact Set.ext_iff.1 h v
    refine ⟨fun v hv => ⟨hC.vertexSet_subset hv.1, hv.2⟩, ?_, ?_⟩
    · rintro e ⟨he, hn⟩
      exact ⟨hC.edgeSet_subset he, fun v hv hi => hn v hv ((hI e he v).1 hi)⟩
    · rintro e ⟨he, hn⟩
      ext v
      exact ⟨fun h => ⟨(hI e he v).1 h.1, hn⟩, fun h => ⟨(hI e he v).2 h.1,
        fun w hw hi => hn w hw ((hI e he w).1 hi)⟩⟩
  refine (isSeparation_iff_of_le (hle hs.left_le) (hle hs.right_le)).2 ⟨?_, ?_, ?_⟩
  · change (A.vertexSet \ Z) ∪ (B.vertexSet \ Z) = G.vertexSet \ Z
    rw [← Set.union_sdiff_distrib, hs.vertexSet_union]
  · ext e
    constructor
    · rintro (⟨he, hn⟩ | ⟨he, hn⟩)
      · exact (hle hs.left_le).edgeSet_subset ⟨he, hn⟩
      · exact (hle hs.right_le).edgeSet_subset ⟨he, hn⟩
    · rintro ⟨he, hn⟩
      have hI : ∀ {C : Hypergraph α β}, C ≤ G → e ∈ C.edgeSet → ∀ v, ¬ C.Inc e v ∨ G.Inc e v := by
        intro C hC hec v
        by_cases h : C.Inc e v
        · exact .inr (Set.ext_iff.1 (hC.ends_eq e hec) v |>.2 h)
        · exact .inl h
      have heU : e ∈ A.edgeSet ∪ B.edgeSet := hs.edgeSet_union ▸ he
      rcases heU with h | h
      · exact .inl ⟨h, fun v hv hi => hn v hv ((hI hs.left_le h v).resolve_left (not_not.2 hi))⟩
      · exact .inr ⟨h, fun v hv hi => hn v hv ((hI hs.right_le h v).resolve_left (not_not.2 hi))⟩
  · ext e
    constructor
    · rintro ⟨h1, h2⟩
      have : e ∈ (A ∩ B).edgeSet := ⟨h1.1, h2.1⟩
      rw [hs.edgeSet_inter_eq] at this
      exact this
    · exact fun h => absurd h (notMem_empty e)

theorem separationOrder_deleteVertices {A B : Hypergraph α β} {Z : Set α} (hZ : Z ⊆
  (A ∩ B).vertexSet) :
    separationOrder (A.deleteVertices Z) (B.deleteVertices Z) + Z.ncard = separationOrder A B := by
  change ((A.vertexSet \ Z) ∩ (B.vertexSet \ Z)).ncard + Z.ncard = (A.vertexSet ∩ B.vertexSet).ncard
  have e : (A.vertexSet \ Z) ∩ (B.vertexSet \ Z) = (A.vertexSet ∩ B.vertexSet) \ Z := by
    ext v; simp only [mem_inter_iff, mem_sdiff]; tauto
  rw [e]
  exact Set.ncard_sdiff_add_ncard_of_subset hZ (A.vertexSet_finite.inter_of_left _)

/-- One step of the proof of (13.3): if `π₀` is not `s`-redundant, then a simpler central portrayal
exists after moving at most `s` more vertices into `Z₀`. The paper notes that `(G \ Z₀) / Y` and `G
\ (Z₀ ∪ Y)` differ only by edges with at most one end; we pass between them by
`Portrayal.exists_moved`. -/
theorem descent_step {G : Hypergraph α β} (hG : G.IsGraph) {θ' p s : ℕ} {𝒯 : Set
  (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ' 𝒯) {Z₀ : Set α} (hZ₀ : Z₀ ⊆ G.vertexSet) (hbound : Z₀.ncard + s + max 3
      (2 * p + 2) < θ')
    (π₀ : Portrayal (G.deleteVertices Z₀)) (hw : π₀.warp ≤ p)
    (hnot : ¬ π₀.IsRedundant (deleteVerticesTangle G Z₀ 𝒯 θ') (θ' - Z₀.ncard) s) :
    ∃ Z, Z₀ ⊆ Z ∧ Z ⊆ G.vertexSet ∧ Z.ncard ≤ Z₀.ncard + s ∧ ∃ π : Portrayal (G.deleteVertices Z),
      π.IsCentral (deleteVerticesTangle G Z 𝒯 θ') ∧ π.IsSimpler π₀ := by
  have hlt : s < θ' - Z₀.ncard := by omega
  have ht₀ := GM10.theorem_8_5_proof hG h𝒯 hZ₀ (by omega)
  simp only [Portrayal.IsRedundant, not_and, not_forall, not_not] at hnot
  obtain ⟨Y, hY, hYc, π', hc', hs'⟩ := hnot hlt
  have hYV : Y ⊆ G.vertexSet := fun v hv => (hY hv).1
  have hdisjunion : Z₀ ⊆ Z₀ ∪ Y := subset_union_left
  have hcard : (Z₀ ∪ Y).ncard ≤ Z₀.ncard + s := (ncard_union_le _ _).trans (by omega)
  have hsub : Z₀ ∪ Y ⊆ G.vertexSet := union_subset hZ₀ hYV
  have ht₁ := GM10.theorem_8_5_proof hG h𝒯 hsub (by omega)
  have hw' : π'.warp ≤ p := hs'.warp_le.trans hw
  have hV : (G.deleteVertices (Z₀ ∪ Y)).vertexSet = (quotientVertices
    (G.deleteVertices Z₀) Y).vertexSet := by
    change G.vertexSet \ (Z₀ ∪ Y) = (G.vertexSet \ Z₀) \ Y
    rw [Set.sdiff_sdiff]
  have hcov : EdgesCovered (G.deleteVertices (Z₀ ∪ Y)) (quotientVertices (G.deleteVertices Z₀) Y)
    := by
    rintro e ⟨he, hn⟩
    have hn₀ : ∀ v ∈ Z₀, ¬ G.Inc e v := fun v hv => hn v (.inl hv)
    refine .inl ⟨e, ⟨he, hn₀⟩, ?_⟩
    rintro v ⟨hi, hn'⟩
    exact ⟨⟨hi, hn₀⟩, fun hv => hn' v (.inr hv) hi⟩
  obtain ⟨π, hc, hl⟩ := π'.exists_moved (H₂ := G.deleteVertices (Z₀ ∪ Y)) (θ₂ := θ' -
    (Z₀ ∪ Y).ncard) (𝒯₂ := deleteVerticesTangle G (Z₀ ∪ Y) 𝒯 θ') hV
    (π'.cells_nonempty (theorem_4_2_proof ht₀ hY (by omega))) hcov
    (fun c hc => by have := π'.ncard_cell_inter_other_le hw' hc; omega)
    (fun c hc A D hs ho hVA => by
      obtain ⟨B, hB⟩ := hc' c hc
      obtain ⟨-, ⟨A₁, B₁⟩, ⟨-, -, ⟨A₂, B₂⟩, hm₂, hZ, h3, h4⟩, hYs, h1, h2⟩ := hB
      dsimp only at h1 h2 h3 h4 hZ hYs
      subst h3 h4
      have hVc : (π'.cellGraph c).vertexSet = (A₂.vertexSet \ Z₀) \ Y := by rw [← h1]; rfl
      have hZ' : Z₀ ∪ Y ⊆ (A₂ ∩ B₂).vertexSet :=
        union_subset hZ fun v hv => ⟨(hYs hv).1.1, (hYs hv).2.1⟩
      have hsep := isSeparation_deleteVertices (h𝒯.isSeparation hm₂) (Z₀ ∪ Y)
      have hord := separationOrder_deleteVertices hZ'
      have hlt₂ := h𝒯.order_lt hm₂
      have hm : (A₂.deleteVertices (Z₀ ∪ Y), B₂.deleteVertices (Z₀ ∪ Y)) ∈ deleteVerticesTangle G
        (Z₀ ∪ Y) 𝒯 θ' :=
        ⟨hsep, by dsimp only; omega, ⟨A₂, B₂⟩, hm₂, hZ', rfl, rfl⟩
      refine GM10.theorem_2_9_proof ht₁ hm hs ho (.inr (.inl ?_))
      rw [hVA, hVc]
      rintro v ⟨⟨h5, h6⟩, h7⟩
      exact ⟨h5, fun h => h.elim h6 h7⟩)
  exact ⟨Z₀ ∪ Y, hdisjunion, hsub, hcard, π, hc, hl.trans_isSimpler hs'⟩

/-- An upper bound on `σ(Σ, p, z')` over the surfaces `Σ` with `h_p ≤ h` and over `z' ≤ z`. There
are finitely many such surfaces, as the paper says, since `p ≥ 1`. -/
noncomputable def sigmaBound (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (p h z : ℕ) : ℕ :=
  (Finset.range (h + 1) ×ˢ Finset.range (h + 1) ×ˢ Finset.range (h + 1) ×ˢ Finset.range (z + 1)).sup
    fun t => σ (SurfaceModel t.1 t.2.1 t.2.2.1) p t.2.2.2

theorem le_sigmaBound {σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ}
  (hσ : IsStandard σ) {p h z z' : ℕ} (hp : 1 ≤ p)
    {G : Hypergraph α β} (π : Portrayal G) (hh : π.hp p ≤ h) (hz : z' ≤ z) : σ π.S p z'
      ≤ sigmaBound σ p h z := by
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification π.S π.isSurface π.connected
  rw [π.hp_eq p e] at hh
  set g := 4 * a + 2 * b + c
  have h1 : g ≤ g ^ 2 * p := by
    nlinarith [Nat.le_self_pow (n := 2) (by norm_num) g, Nat.zero_le (g ^ 2)]
  have hg : g ≤ h := by omega
  have hs : IsSurface (SurfaceModel a b c) := isSurface_of_homeo e π.isSurface
  have hco : ConnectedSpace (SurfaceModel a b c) := by
    have := π.connected
    exact e.surjective.connectedSpace e.continuous
  rw [hσ π.S (SurfaceModel a b c) p z' π.isSurface π.connected hs hco ⟨e⟩]
  have hm : (a, b, c, z') ∈ Finset.range (h + 1) ×ˢ Finset.range (h + 1) ×ˢ Finset.range
    (h + 1) ×ˢ Finset.range (z + 1) := by
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  exact Finset.le_sup (f := fun t : ℕ × ℕ × ℕ × ℕ => σ (SurfaceModel t.1 t.2.1 t.2.2.1) p t.2.2.2)
    hm

/-- **Graph Minors XVII, (13.3)** (page 205): "For any standard $\sigma$ and all $p \ge 1$ and $h$,
$z_0 \ge 0$, there exist $\theta$, $z$ with $\theta > z \ge z_0$ and with the following property.
Let $\mathcal{T}$ be a tangle of order $\ge \theta$ in a graph $G$, let $Z_0 \subseteq V(G)$ with
$|Z_0| \le z_0$, and let $\pi_0$ be a $(\mathcal{T} \setminus Z_0)$-central portrayal of $G
\setminus Z_0$ with warp $\le p$ and with $h_p(\pi_0) \le h$. Then there exist $Z \subseteq V(G)$
with $Z_0 \subseteq Z$ such that $|Z| \le z$, and a $(\mathcal{T} \setminus Z)$-central portrayal
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$, such that $\pi$ is simpler than
or resembles $\pi_0$, and $\pi$ is $\sigma(\Sigma, p, |Z|)$-redundant."

We read a bound on all `σ` from `sigmaBound`, so the paper's reduction to its condition (1) is not
needed. -/
theorem theorem_13_3_proof (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ)
  (hσ : IsStandard σ) {p : ℕ} (hp : 1 ≤ p) (h z₀ : ℕ) :
    ∃ θ z : ℕ, z < θ ∧ z₀ ≤ z ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀
      (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ'
        → ∀ Z₀ ⊆ G.vertexSet, Z₀.ncard ≤ z₀ →
      ∀ π₀ : Portrayal (G.deleteVertices Z₀), π₀.IsCentral (deleteVerticesTangle G Z₀ 𝒯 θ')
        → π₀.warp ≤ p → π₀.hp p ≤ h →
      ∃ Z, Z₀ ⊆ Z ∧ Z ⊆ G.vertexSet ∧ Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
        π.IsCentral (deleteVerticesTangle G Z 𝒯 θ') ∧ (π.IsSimpler π₀ ∨ π.Resembles π₀) ∧
        π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S p Z.ncard) := by
  induction h generalizing z₀ with
  | zero =>
    set M := sigmaBound σ p 0 z₀
    refine ⟨z₀ + M + max 3 (2 * p + 2) + 1, z₀, by omega, le_rfl, ?_⟩
    intro α β G hG θ' 𝒯 h𝒯 hθ Z₀ hZ₀ hcard π₀ hc hw hh
    have hs : σ π₀.S p Z₀.ncard ≤ M := le_sigmaBound hσ hp π₀ hh hcard
    by_cases hred : π₀.IsRedundant (deleteVerticesTangle G Z₀ 𝒯 θ') (θ' - Z₀.ncard)
      (σ π₀.S p Z₀.ncard)
    · exact ⟨Z₀, subset_rfl, hZ₀, hcard, π₀, hc, .inr (Portrayal.Resembles.refl π₀), hred⟩
    · exfalso
      obtain ⟨Z, -, -, -, π, -, hsimp⟩ := descent_step hG h𝒯 hZ₀ (by omega) π₀ hw hred
      have := theorem_13_2_proof hp π₀ π hw hsimp
      omega
  | succ h ih =>
    set M := sigmaBound σ p (h + 1) z₀
    obtain ⟨θ₁, z, hz, hz₀, hmain⟩ := ih (z₀ + M)
    refine ⟨max θ₁ (z₀ + M + max 3 (2 * p + 2) + 1), z, by omega, by omega, ?_⟩
    intro α β G hG θ' 𝒯 h𝒯 hθ Z₀ hZ₀ hcard π₀ hc hw hh
    have hs : σ π₀.S p Z₀.ncard ≤ M := le_sigmaBound hσ hp π₀ hh hcard
    by_cases hred : π₀.IsRedundant (deleteVerticesTangle G Z₀ 𝒯 θ') (θ' - Z₀.ncard)
      (σ π₀.S p Z₀.ncard)
    · exact ⟨Z₀, subset_rfl, hZ₀, by omega, π₀, hc, .inr (Portrayal.Resembles.refl π₀), hred⟩
    · obtain ⟨Z₁, h01, hZ₁, hc₁, π₁, hcen₁, hsimp⟩ := descent_step hG h𝒯 hZ₀ (by omega) π₀ hw hred
      have hdrop := theorem_13_2_proof hp π₀ π₁ hw hsimp
      obtain ⟨Z, h1Z, hZ, hcZ, π, hcen, hrel, hredZ⟩ := hmain G hG θ' 𝒯 h𝒯 (by omega) Z₁ hZ₁
        (by omega) π₁ hcen₁
        (hsimp.warp_le.trans hw) (by omega)
      refine ⟨Z, h01.trans h1Z, hZ, hcZ, π, hcen, .inl ?_, hredZ⟩
      rcases hrel with hr | hr
      · exact isSimpler_trans hr hsimp
      · exact hr.warpLE.trans_isSimpler hsimp

end GraphMinor.GM17
