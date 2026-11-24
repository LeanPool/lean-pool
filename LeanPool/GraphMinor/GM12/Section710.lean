/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section7Proved
public import LeanPool.GraphMinor.GM14.Cited

/-!
# Graph Minors XII, (7.10): cleared respectful tangle in a 2-cell subdrawing

This file formalizes **(7.10)** of Graph Minors XII (page 270) and the cited bridge theorem
`gm14_theorem_7_10` (`GM14.GM12Theorem710Statement`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **(7.10)** of Graph Minors XII (pages 270–271):
"Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order $\ge 4k +
3$ in a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be $d$. Let
$c \in A(\Gamma)$, and let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$ such that $d(c, e)
\le k$ for all $e \in E(\Gamma) - E(\Gamma')$, and such that if $c \in E(\Gamma) -
E(\Gamma')$ then* ... *$k \ge 2$. Then there is a respectful tangle $\mathscr{T}'$ of order
$\theta - 4k - 2$ in $\Gamma'$, with metric $d'$, such that $d'(a', b') \ge d(a, b) - 4k -
2$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a \subseteq a'$ and $b
\subseteq b'$. Moreover,* (i) *$\mathscr{T}'$ is unique* (ii) *$(A \cap \Gamma', B \cap
\Gamma') \in \mathscr{T}'$ for all $(A, B) \in \mathscr{T}$ of order $< \theta - 4k - 2$,*
(iii) *$d'(a', b') \le d(a, b)$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$
with $a \subseteq a'$ and $b \subseteq b'$." -/
theorem theorem_7_10_proof
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {c : Set S}
    (hθ : 4 * k + 3 ≤ θ)
    (hd : HasTangleMetric Γ θ T d)
    (hc : c ∈ Γ.A)
    (hSub : Γ'.IsSubdrawing Γ)
    (h2cell' : (PaintingOrDrawing.drawing Γ').IsTwoCell)
    (hdist : ∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k)
    (hck : c ∈ Γ.E \ Γ'.E → 2 ≤ k) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ),
      IsClearedTangleAux Γ Γ' T d θ k T' d' ∧
      ∀ (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₁ : Set S → Set S → ℕ),
        HasTangleMetric Γ' (θ - 4 * k - 2) T₁ d₁ →
        (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
          a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d₁ a' b') →
        T₁ = T' := by
  obtain ⟨T'', d'', hd'', hd''_ge⟩ :=
    theorem_7_8_proof hS (by omega) hd hc hSub h2cell' hdist hck
  let T' := GM10.truncation T'' (θ - 4 * k - 2)
  let d' : Set S → Set S → ℕ := fun x y => min (d'' x y) (θ - 4 * k - 2)
  have hd' : HasTangleMetric Γ' (θ - 4 * k - 2) T' d' :=
    HasTangleMetric.truncation hd'' (by omega) (by omega)
  have hd_le_θ : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ θ := by
    intro a ha b hb
    obtain ⟨_, K, ins, hK, _, hd_eq⟩ := id hd
    rw [hd_eq a ha b hb]
    exact tangleMetric_le_order hK ins θ a b
  have hd'_ge : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b' := by
    intro a ha b hb a' ha' b' hb' haa' hbb'
    have h1 := hd''_ge a ha b hb a' ha' b' hb' haa' hbb'
    have h2 := hd_le_θ a ha b hb
    change d a b - 4 * k - 2 ≤ min (d'' a' b') (θ - 4 * k - 2)
    omega
  have hord_eq : θ - (4 * k + 2) = θ - 4 * k - 2 := by omega
  have hd'_ord : HasTangleMetric Γ' (θ - (4 * k + 2)) T' d' := hord_eq.symm ▸ hd'
  have hd'_ge_ord : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - (4 * k + 2) ≤ d' a' b' := by
    intro a ha b hb a' ha' b' hb' haa' hbb'
    have hsub_eq : d a b - (4 * k + 2) = d a b - 4 * k - 2 := by omega
    rw [hsub_eq]
    exact hd'_ge a ha b hb a' ha' b' hb' haa' hbb'
  obtain ⟨h79_sep, h79_uniq⟩ :=
    theorem_7_9_proof hS hd hSub h2cell' (k := 4 * k + 2) (by omega) hd'_ord hd'_ge_ord
  have h77_i :=
    (theorem_7_7_proof hS hd hSub h2cell' (by omega) hd').1 (4 * k + 2) hd'_ge_ord
  refine ⟨T', d', ⟨hd', ?_, ?_⟩, ?_⟩
  · intro A B hAB hord
    exact h79_sep A B hAB (by omega)
  · intro a ha b hb a' ha' b' hb' haa' hbb'
    refine ⟨hd'_ge a ha b hb a' ha' b' hb' haa' hbb', ?_⟩
    have hmin_le := h77_i a ha b hb a' ha' b' hb' haa' hbb'
    have hd'_le : d' a' b' ≤ θ - (4 * k + 2) := by
      change min (d'' a' b') (θ - 4 * k - 2) ≤ θ - (4 * k + 2)
      omega
    rwa [min_eq_left hd'_le] at hmin_le
  · intro T₁ d₁ hd₁ hd₁_ge
    refine h79_uniq T₁ d₁ (hord_eq.symm ▸ hd₁) fun a ha b hb a' ha' b' hb' haa' hbb' => ?_
    have hsub_eq : d a b - (4 * k + 2) = d a b - 4 * k - 2 := by omega
    rw [hsub_eq]
    exact hd₁_ge a ha b hb a' ha' b' hb' haa' hbb'

/-- Bridge theorem providing `GM14.GM12Theorem710Statement` from `theorem_7_10_proof`. -/
theorem gm14_theorem_7_10 :
    GM14.GM12Theorem710Statement.{u} := by
  intro S _ _ hS hConn Γ Γ' θ k T d c hθ hd hc hSub h2cell' hdist hck
  have : T2Space S := hS.2.1
  exact theorem_7_10_proof hS hθ hd hc hSub h2cell' hdist hck

end GraphMinor.GM12
