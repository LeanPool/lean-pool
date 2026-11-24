/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SlideDescent
public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM07.Section46SideParam
public import LeanPool.GraphMinor.GM07.Section46LongEdges
import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM07.Section2Base

/-!
# The slide in VII (4.6)

Page 227: "Since each edge of $\theta^{-1}(K)$ passes through at least $w$ vertices
of $\theta^{-1}(G)$, we may choose $H_3$ so that in addition $U(H_3) \cap U(\theta^{-1}(K))
\subseteq
V(\theta^{-1}(G))$." Here is that sentence, in the form claim (1) uses. The homeomorphism
`β` comes from `Net.exists_slide_family`, applied to the open central
segments of the long edges.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- The slide of VII (4.6), page 227. -/
theorem Net.exists_matching_slide (N : Net S) {G J K L : Drawing S}
    {K' : Drawing S'} {θ : S' → S} {ψ : N.D → S'} {γ : Set S → unitInterval → S} {μ w : ℕ}
    (hγ : EdgePar J γ)
    (hsides : ∀ e ∈ J.E, e ∩ bd S = ∅ → ∃ i : Fin N.r, ∀ t, γ e t = N.φ (N.f i t))
    (hlong : ∀ e : longSeamEdges G J μ w, Disjoint e.1 (bd S))
    (s t : longSeamEdges G J μ w → unitInterval)
    (hst : ∀ e, s e ∈ Ioo (0 : unitInterval) 1 ∧ t e ∈ Ioo (0 : unitInterval) 1 ∧ s e < t e)
    (hendsG : ∀ e, γ e.1 (s e) ∈ G.V ∧ γ e.1 (t e) ∈ G.V)
    (hendsL : ∀ e, γ e.1 (s e) ∈ L.U ∧ γ e.1 (t e) ∈ L.U)
    (hcount : ∀ e, w ≤ (γ e.1 '' Ioo (s e) (t e) ∩ G.V).ncard)
    (hKU : K.U ⊆ ⋃ e, γ e.1 '' Icc (s e) (t e))
    (hKIoo : ∀ e, ∀ r ∈ Ioo (s e) (t e), γ e.1 r ∈ K.U)
    (hoff : ∀ e, ∀ r ∈ Ioo (s e) (t e), γ e.1 r ∉ bd S ∪ L.U)
    (hθ : IsCutAlongGraph L S' θ) (hp : IsPullbackDrawing θ K K')
    (hψcut : IsCutAlongGraph K' N.D ψ) (hψc : Continuous ψ) (hψs : Function.Surjective ψ)
    (hψ : ∀ x, θ (ψ x) = N.φ x) (hinj : InjOn θ (θ ⁻¹' K.U)) :
    ∀ X : Set S', X.Finite → X ⊆ K'.U → X.ncard ≤ w →
      ∃ β : S' ≃ₜ S', (∀ x ∈ bd S', β x = x) ∧ K'.U ⊆ β '' K'.U ∧ ∀ x ∈ X, β x ∈ θ ⁻¹' G.V := by
  classical
  intro X hXf hXK hXw
  have hne : ∀ e : longSeamEdges G J μ w, e.1 ∩ bd S = ∅ := fun e =>
    disjoint_iff_inter_eq_empty.mp (hlong e)
  choose i hi using fun e : longSeamEdges G J μ w => hsides e.1 e.2.1 (hne e)
  have : Finite (longSeamEdges G J μ w) :=
    Set.Finite.to_subtype (J.finite_edges.subset fun e (he : e ∈ longSeamEdges G J μ w) => he.1)
  have hinjγ : ∀ e : longSeamEdges G J μ w, InjOn (γ e.1) (Ioo (s e) (t e)) := fun e =>
    (hγ.inj e.1 e.2.1).mono (Ioo_subset_Ioo (hst e).1.1.le (hst e).2.1.2.le)
  have hiinj : Function.Injective i := by
    intro e e' h
    apply Subtype.ext
    have hfun : γ e.1 = γ e'.1 := funext fun r => by rw [hi e r, hi e' r, h]
    rw [← hγ.image e.1 e.2.1, ← hγ.image e'.1 e'.2.1, hfun]
  have hoff' : ∀ e, ∀ r ∈ Ioo (s e) (t e), N.φ (N.f (i e) r) ∉ bd S ∪ L.U := fun e r hr => by
    rw [← hi e r]
    exact hoff e r hr
  have hsame : ∀ e, ∀ r ∈ Icc (s e) (t e), ψ (N.f (i e) r) = ψ (N.g (i e) r) := fun e =>
    N.psi_sides_eq hθ hψc hψ (i e) (hst e).2.2 (hoff' e)
  let Y : longSeamEdges G J μ w → Set unitInterval := fun e => {r ∈ Ioo (s e) (t e) | γ e.1 r ∈ G.V}
  have hYimg : ∀ e, γ e.1 '' Y e = γ e.1 '' Ioo (s e) (t e) ∩ G.V := fun e => by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨mem_image_of_mem _ hr.1, hr.2⟩
    · rintro ⟨⟨r, hr, rfl⟩, hx⟩
      exact ⟨r, ⟨hr, hx⟩, rfl⟩
  have hYinj : ∀ e, InjOn (γ e.1) (Y e) := fun e => (hinjγ e).mono fun r hr => hr.1
  have hYf : ∀ e, (Y e).Finite := fun e =>
    Set.Finite.of_finite_image (by
      rw [hYimg]
      exact G.finite_V.subset inter_subset_right) (hYinj e)
  have hcard : ∀ e, {r ∈ Ioo (s e) (t e) | ψ (N.f (i e) r) ∈ X}.ncard ≤ (Y e).ncard := by
    intro e
    have h1 : {r ∈ Ioo (s e) (t e) | ψ (N.f (i e) r) ∈ X}.ncard ≤ X.ncard := by
      refine ncard_le_ncard_of_injOn (fun r => ψ (N.f (i e) r)) (fun r hr => hr.2) ?_ hXf
      intro r hr r' hr' heq
      apply hinjγ e hr.1 hr'.1
      have := congrArg θ heq
      simp only [hψ] at this
      rw [hi e r, hi e r', this]
    have h2 : (Y e).ncard = (γ e.1 '' Ioo (s e) (t e) ∩ G.V).ncard := by
      rw [← hYimg, (hYinj e).ncard_image]
    have h3 := hcount e
    omega
  obtain ⟨β, hfix, hsurj, hmove⟩ := N.exists_slide_family hψcut.quotientMap
    (fun x y h => by rw [← hψ x, ← hψ y, h]) i hiinj s t (fun e => (hst e).1) (fun e => (hst e).2.1)
    hsame hXf Y hYf (fun e r hr => hr.1) hcard
  have hgsame : ∀ e, ∀ r ∈ Ioo (s e) (t e), N.φ (N.g (i e) r) = N.φ (N.f (i e) r) := fun e r hr
    => by
    rw [← hψ, ← hψ, hsame e r ⟨hr.1.le, hr.2.le⟩]
  have hfix' : ∀ x ∈ bd N.D, N.φ x ∈ bd S ∪ L.U → β (ψ x) = ψ x := by
    intro x hx hb
    refine hfix x hx fun e => ⟨?_, ?_⟩
    · rintro ⟨r, hr, rfl⟩
      exact hoff' e r hr hb
    · rintro ⟨r, hr, rfl⟩
      rw [hgsame e r hr] at hb
      exact hoff' e r hr hb
  have hfbd : ∀ (j : Fin N.r) (r : unitInterval), N.f j r ∈ bd N.D := fun j r =>
    N.range_f_subset_bd j (mem_range_self r)
  have hend : ∀ e, β (ψ (N.f (i e) (s e))) = ψ (N.f (i e) (s e)) ∧
      β (ψ (N.f (i e) (t e))) = ψ (N.f (i e) (t e)) := fun e => by
    refine ⟨hfix' _ (hfbd _ _) (.inr ?_), hfix' _ (hfbd _ _) (.inr ?_)⟩
    · rw [← hi e]
      exact (hendsL e).1
    · rw [← hi e]
      exact (hendsL e).2
  have hstruct : ∀ y ∈ K'.U, ∃ e, ∃ r ∈ Icc (s e) (t e), y = ψ (N.f (i e) r) := by
    intro y hy
    have hyK : θ y ∈ K.U := by
      rw [hp.1] at hy
      exact hy
    obtain ⟨e, r, hr, hrr⟩ := mem_iUnion.mp (hKU hyK)
    refine ⟨e, r, hr, hinj hyK ?_ ?_⟩
    · change θ (ψ _) ∈ K.U
      rw [hψ, ← hi e, hrr]
      exact hyK
    · rw [hψ, ← hi e, hrr]
  have hcases : ∀ e, ∀ r ∈ Icc (s e) (t e), r = s e ∨ r = t e ∨ r ∈ Ioo (s e) (t e) := by
    intro e r hr
    rcases hr.1.eq_or_lt with h | h
    · exact .inl h.symm
    · rcases hr.2.eq_or_lt with h' | h'
      · exact .inr (.inl h')
      · exact .inr (.inr ⟨h, h'⟩)
  refine ⟨β, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hψs x
    have hyD : y ∈ bd N.D := by
      rw [← hψcut.preimage_bd_union_U]
      exact .inl hx
    refine hfix' y hyD ?_
    rw [← hψ]
    have : ψ y ∈ θ ⁻¹' (bd S ∪ L.U) := by
      rw [hθ.preimage_bd_union_U]
      exact hx
    exact this
  · intro y hy
    obtain ⟨e, r, hr, rfl⟩ := hstruct y hy
    rcases hcases e r hr with rfl | rfl | hr'
    · exact ⟨_, hy, (hend e).1⟩
    · exact ⟨_, hy, (hend e).2⟩
    · obtain ⟨r₀, hr₀, hb⟩ := hsurj e r hr'
      refine ⟨ψ (N.f (i e) r₀), ?_, hb⟩
      rw [hp.1]
      change θ (ψ _) ∈ K.U
      rw [hψ, ← hi e]
      exact hKIoo e r₀ hr₀
  · intro x hx
    obtain ⟨e, r, hr, rfl⟩ := hstruct x (hXK hx)
    rcases hcases e r hr with rfl | rfl | hr'
    · rw [(hend e).1]
      change θ (ψ _) ∈ G.V
      rw [hψ, ← hi e]
      exact (hendsG e).1
    · rw [(hend e).2]
      change θ (ψ _) ∈ G.V
      rw [hψ, ← hi e]
      exact (hendsG e).2
    · obtain ⟨r', hr'Y, hb⟩ := hmove e r hr' hx
      rw [hb]
      change θ (ψ _) ∈ G.V
      rw [hψ, ← hi e]
      exact hr'Y.2

end GraphMinor.GM07
