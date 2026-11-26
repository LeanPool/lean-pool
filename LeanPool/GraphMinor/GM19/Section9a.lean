/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Defs3
public import LeanPool.GraphMinor.GM19.RadialExists

/-!
# Graph Minors XIX, (9.1)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

/-- A border edge of a painting that fits a frame lies in a side. -/
theorem Painting.Fits.exists_side {Γ : Painting S} {Φ : Frame S} (hf : Γ.Fits Φ) {e : Set S}
    (he : e ∈ Γ.E) (hb : Painting.IsBorder e) : ∃ s ∈ Φ.sides, e ⊆ s := by
  have hsub : e ⊆ bd S \ Φ.V := fun x hx ↦
    ⟨(Γ.border_edge e he hb).2 hx, fun hV ↦ (he.2.1 hx).2 (hf.V_subset hV)⟩
  obtain ⟨t, ht, het⟩ := exists_arcComp_superset he.2.2.1 hsub
  exact ⟨t, ht, het⟩

theorem side_unique {Φ : Frame S} {e s t : Set S} (hne : e.Nonempty) (hs : s ∈ Φ.sides)
    (ht : t ∈ Φ.sides) (hes : e ⊆ s) (het : e ⊆ t) : s = t := by
  obtain ⟨x, hx⟩ := hne
  exact arcComp_eq_of_mem hs ht (hes hx) (het hx)

/-- The kind of an edge of a coloured painting. -/
theorem ColouredPainting.cases {χ : ColourScheme S α} (P : ColouredPainting χ) {e : Set S}
    (he : e ∈ P.Γ.E) :
    (Painting.IsInternal e ∧ (tilde e).ncard = 2 ∧ P.φ e ∈ χ.Ω2.E) ∨
    (Painting.IsInternal e ∧ (tilde e).ncard = 3 ∧ P.φ e ∈ χ.Ω3.E) ∨
    (Painting.IsBorder e ∧ ∃ s ∈ χ.Φ.sides, e ⊆ s ∧ P.φ e ∈ (χ.ΩS s).E) := by
  by_cases hb : Painting.IsBorder e
  · obtain ⟨s, hs, hes⟩ := P.fits.exists_side he hb
    exact Or.inr (Or.inr ⟨hb, s, hs, hes, P.border_mem e he s hs ⟨hb, hes⟩⟩)
  · have hi : Painting.IsInternal e := by
      rw [Painting.IsInternal, disjoint_iff_inter_eq_empty]
      exact not_nonempty_iff_eq_empty.1 hb
    rcases P.Γ.size_cases he with h | h
    · exact Or.inl ⟨hi, h, P.internal_2_mem e he hi h⟩
    · exact Or.inr (Or.inl ⟨hi, h, P.internal_3_mem e he hi h⟩)

/-- **Graph Minors XIX, (9.1).** "Let $(\Gamma, \phi), (\Gamma', \phi')$ be $\chi$-coloured
paintings, where $\chi$ is
disjoint. Let $\sigma$ be an inflation of $\Gamma$ in $\Gamma'$, such that $\phi(e) \le
\phi'(\sigma(e))$ (in $\Omega_{\chi}$) for every $e \in E(\Gamma)$. Then $\sigma$ is an
inflation of $(\Gamma, \phi)$ in $(\Gamma', \phi')$." -/
theorem theorem_9_1_proof {χ : ColourScheme S α} (hd : χ.IsDisjoint) (P P' : ColouredPainting χ)
    {σv : S → Set S} {σe : Set S → Set S} (hσ : IsInflation P.Γ P'.Γ σv σe)
    (hle : ∀ e ∈ P.Γ.E, (χ.unionWQO hd).le (P.φ e) (P'.φ (σe e))) :
    IsColouredInflation χ P P' σv σe := by
  have h23 := disjoint_left.1 hd.disj_2_3
  have h2S := fun s hs ↦ disjoint_left.1 (hd.disj_2_S s hs)
  have h3S := fun s hs ↦ disjoint_left.1 (hd.disj_3_S s hs)
  have hSS := fun s hs t ht hne ↦ disjoint_left.1 (hd.disj_S_S s hs t ht hne)
  have hsideeq : ∀ {x s t}, s ∈ χ.Φ.sides → t ∈ χ.Φ.sides → x ∈ (χ.ΩS s).E → x ∈ (χ.ΩS t).E →
      s = t := fun {x s t} hs ht h₁ h₂ ↦ by
    by_contra hne
    exact hSS s hs t ht hne h₁ h₂
  have hle2 : ∀ {x y}, x ∈ χ.Ω2.E → (χ.unionWQO hd).le x y → χ.Ω2.le x y := by
    rintro x y hx (⟨-, -, h⟩ | ⟨h, -, -⟩ | ⟨s, hs, h, -, -⟩)
    · exact h
    · exact absurd h (h23 hx)
    · exact absurd h (h2S s hs hx)
  have hle3 : ∀ {x y}, x ∈ χ.Ω3.E → (χ.unionWQO hd).le x y → χ.Ω3.le x y := by
    rintro x y hx (⟨h, -, -⟩ | ⟨-, -, h⟩ | ⟨s, hs, h, -, -⟩)
    · exact absurd hx (h23 h)
    · exact h
    · exact absurd h (h3S s hs hx)
  have hleS : ∀ {x y s}, s ∈ χ.Φ.sides → x ∈ (χ.ΩS s).E → (χ.unionWQO hd).le x y →
      y ∈ (χ.ΩS s).E ∧ (χ.ΩS s).le x y := by
    rintro x y s hs hx (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨t, ht, h₁, h₂, h₃⟩)
    · exact absurd hx (h2S s hs h)
    · exact absurd hx (h3S s hs h)
    · obtain rfl := hsideeq hs ht hx h₁
      exact ⟨h₂, h₃⟩
  refine ⟨hσ, ?_, ?_, ?_, ?_⟩
  · intro e he hb
    obtain ⟨s, hs, hes⟩ := P.fits.exists_side he hb
    have hx := P.border_mem e he s hs ⟨hb, hes⟩
    have hy := (hleS hs hx (hle e he)).1
    have hne : (σe e).Nonempty := (hσ.edge_mem e he).1
    rcases P'.cases (hσ.edge_mem e he) with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hb', t, ht, hzt, hyt⟩
    · exact absurd hy (h2S s hs h)
    · exact absurd hy (h3S s hs h)
    · obtain rfl := hsideeq hs ht hy hyt
      refine ⟨hb', fun t ht' ↦ ⟨fun het ↦ ?_, fun hzt' ↦ ?_⟩⟩
      · rw [← side_unique he.1 hs ht' hes het]
        exact hzt
      · rw [← side_unique hne hs ht' hzt hzt']
        exact hes
  · exact fun e he hi h2 ↦ hle2 (P.internal_2_mem e he hi h2) (hle e he)
  · exact fun e he hi h3 ↦ hle3 (P.internal_3_mem e he hi h3) (hle e he)
  · exact fun e he s hs hb ↦ (hleS hs (P.border_mem e he s hs hb) (hle e he)).2

end GraphMinor.GM19
