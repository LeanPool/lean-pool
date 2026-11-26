/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscUnion
public import LeanPool.GraphMinor.Surface.PlaneDisc
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Maps between closed discs with a fixed part of the boundary

We build the homeomorphism behind the step "Then `Γ'` is a painting in `Σ'`" of the proof of (9.3)
of Graph Minors XVII, page 184.
Let `Q` and `Q'` be closed discs with boundaries `K ∪ G` and `K ∪ E`, for lines `G` and `E` with the
same ends as `K`. Then there
is a homeomorphism of `Q` onto `Q'` that fixes `K`, maps `G` onto `E`, and maps a given inner point
of `G` to a given inner point of
`E` (`exists_disc_map`). The boundary map extends over the discs by the Schoenflies theorem.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- A power map of the unit interval onto itself moves any inner point to any other. -/
theorem exists_interval_map {t t' : 𝕀} (h0 : t ≠ 0) (h1 : t ≠ 1) (h0' : t' ≠ 0) (h1' : t' ≠ 1) :
    ∃ ρ : 𝕀 → 𝕀, Continuous ρ ∧ Function.Injective ρ ∧ ρ 0 = 0 ∧ ρ 1 = 1 ∧ ρ t = t' := by
  have hp : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
  have hl : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
  have hp' : (0 : ℝ) < t' := lt_of_le_of_ne t'.2.1 fun h => h0' (Subtype.ext h.symm)
  have hl' : (t' : ℝ) < 1 := lt_of_le_of_ne t'.2.2 fun h => h1' (Subtype.ext h)
  have hlog : Real.log t < 0 := Real.log_neg hp hl
  have hlog' : Real.log t' < 0 := Real.log_neg hp' hl'
  set α : ℝ := Real.log t' / Real.log t with hα
  have hαp : 0 < α := div_pos_of_neg_of_neg hlog' hlog
  refine ⟨fun s => ⟨(s : ℝ) ^ α, Real.rpow_nonneg s.2.1 _, Real.rpow_le_one s.2.1 s.2.2 hαp.le⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.rpow_const fun _ => .inr hαp.le) _
  · intro a b hab
    have h3 : (a : ℝ) ^ α = (b : ℝ) ^ α := congrArg Subtype.val hab
    exact Subtype.ext (Real.rpow_left_injOn hαp.ne' a.2.1 b.2.1 h3)
  · exact Subtype.ext (by simp [Real.zero_rpow hαp.ne'])
  · exact Subtype.ext (by simp)
  · refine Subtype.ext ?_
    change (t : ℝ) ^ α = t'
    rw [Real.rpow_def_of_pos hp, hα, mul_div_cancel₀ _ hlog.ne, Real.exp_log hp']

variable {X : Type*} [TopologicalSpace X]

/-- **A homeomorphism of closed discs with prescribed boundary.** -/
theorem exists_disc_map {Q Q' K G E : Set X} {a b z z' : X} (hQ : IsClosedDisc Q)
  (hQ' : IsClosedDisc Q')
    (hK : IsLineWithEnds K a b) (hG : IsLineWithEnds G a b) (hE : IsLineWithEnds E a b)
    (hbQ : discBd Q = K ∪ G) (hbQ' : discBd Q' = K ∪ E) (hKG : K ∩ G = {a, b}) (hKE : K ∩ E
      = {a, b})
    (hz : z ∈ G \ {a, b}) (hz' : z' ∈ E \ {a, b}) :
    ∃ f : X → X, ContinuousOn f Q ∧ InjOn f Q ∧ f '' Q = Q' ∧ (∀ x ∈ K, f x = x) ∧ f z = z'
      ∧ f '' G = E := by
  classical
  obtain ⟨h, g, c⟩ := hQ.exists_isChart
  obtain ⟨h', g', c'⟩ := hQ'.exists_isChart
  obtain ⟨fK, hK0, hK1⟩ := hK
  obtain ⟨fG, hG0, hG1⟩ := hG
  obtain ⟨fE, hE0, hE1⟩ := hE
  let ζ : 𝕀 → X := fun s => (fK s).1
  let γ : 𝕀 → X := fun s => (fG s).1
  let ε : 𝕀 → X := fun s => (fE s).1
  have hζ : Continuous ζ := continuous_subtype_val.comp fK.continuous
  have hγ : Continuous γ := continuous_subtype_val.comp fG.continuous
  have hε : Continuous ε := continuous_subtype_val.comp fE.continuous
  have iζ : Function.Injective ζ := fun u v h => fK.injective (Subtype.ext h)
  have iγ : Function.Injective γ := fun u v h => fG.injective (Subtype.ext h)
  have iε : Function.Injective ε := fun u v h => fE.injective (Subtype.ext h)
  have rζ : range ζ = K := by
    ext x
    exact ⟨by rintro ⟨u, rfl⟩; exact (fK u).2, fun hx => ⟨fK.symm ⟨x, hx⟩, by simp [ζ]⟩⟩
  have rγ : range γ = G := by
    ext x
    exact ⟨by rintro ⟨u, rfl⟩; exact (fG u).2, fun hx => ⟨fG.symm ⟨x, hx⟩, by simp [γ]⟩⟩
  have rε : range ε = E := by
    ext x
    exact ⟨by rintro ⟨u, rfl⟩; exact (fE u).2, fun hx => ⟨fE.symm ⟨x, hx⟩, by simp [ε]⟩⟩
  obtain ⟨t, rfl⟩ : z ∈ range γ := rγ ▸ hz.1
  obtain ⟨t', rfl⟩ : z' ∈ range ε := rε ▸ hz'.1
  have ht0 : t ≠ 0 := fun h3 => hz.2 (.inl (by rw [h3]; exact hG0))
  have ht1 : t ≠ 1 := fun h3 => hz.2 (.inr (by rw [h3]; exact hG1))
  have ht0' : t' ≠ 0 := fun h3 => hz'.2 (.inl (by rw [h3]; exact hE0))
  have ht1' : t' ≠ 1 := fun h3 => hz'.2 (.inr (by rw [h3]; exact hE1))
  obtain ⟨ρ, hρ, iρ, ρ0, ρ1, ρt⟩ := exists_interval_map ht0 ht1 ht0' ht1'
  let ε' : 𝕀 → X := ε ∘ ρ
  have hsurj : range ρ = univ := by
    have hsub := intermediate_value_univ (0 : 𝕀) 1 hρ
    refine eq_univ_of_forall fun y => hsub ?_
    rw [ρ0, ρ1]
    exact ⟨unitInterval.nonneg y, unitInterval.le_one y⟩
  have rK : ∀ s, ζ s ∈ K := fun s => (fK s).2
  have rG : ∀ s, γ s ∈ G := fun s => (fG s).2
  have rE : ∀ s, ε s ∈ E := fun s => (fE s).2
  have bK : ∀ s, ζ s ∈ discBd Q := fun s => hbQ ▸ .inl (rK s)
  have bG : ∀ s, γ s ∈ discBd Q := fun s => hbQ ▸ .inr (rG s)
  have bK' : ∀ s, ζ s ∈ discBd Q' := fun s => hbQ' ▸ .inl (rK s)
  have bE : ∀ s, ε s ∈ discBd Q' := fun s => hbQ' ▸ .inr (rE s)
  have onQ : ∀ s, ζ s ∈ Q := fun s => discBd_subset _ (bK s)
  have onG : ∀ s, γ s ∈ Q := fun s => discBd_subset _ (bG s)
  have onQ' : ∀ s, ζ s ∈ Q' := fun s => discBd_subset _ (bK' s)
  have onE : ∀ s, ε s ∈ Q' := fun s => discBd_subset _ (bE s)
  have hinjh : InjOn h Q := c.gh.injOn
  have hinjh' : InjOn h' Q' := c'.gh.injOn
  have arc : ∀ {h₀ : X → ℂ} {D : Set X} {e : 𝕀 → X}, ContinuousOn h₀ D → InjOn h₀ D → Continuous e →
      Function.Injective e → (∀ s, e s ∈ D) → IsArcMap (h₀ ∘ e) := fun hc hi he hie hm =>
    ⟨hc.comp_continuous he hm, fun u v huv => hie (hi (hm u) (hm v) huv)⟩
  have mm : ∀ s u, ζ s = γ u → (s = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 1) := fun s u hsu => by
    have h3 : ζ s ∈ K ∩ G := ⟨rK s, hsu ▸ rG u⟩
    rw [hKG] at h3
    rcases h3 with h3 | h3
    · exact .inl ⟨iζ (h3.trans hK0.symm), iγ ((hsu.symm.trans h3).trans hG0.symm)⟩
    · exact .inr ⟨iζ (h3.trans hK1.symm), iγ ((hsu.symm.trans h3).trans hG1.symm)⟩
  have mm' : ∀ s u, ζ s = ε' u → (s = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 1) := fun s u hsu => by
    have h3 : ζ s ∈ K ∩ E := ⟨rK s, hsu ▸ rE _⟩
    rw [hKE] at h3
    rcases h3 with h3 | h3
    · refine .inl ⟨iζ (h3.trans hK0.symm), iρ (iε ?_)⟩
      show ε (ρ u) = ε (ρ 0)
      rw [ρ0]
      exact (hsu.symm.trans h3).trans hE0.symm
    · refine .inr ⟨iζ (h3.trans hK1.symm), iρ (iε ?_)⟩
      show ε (ρ u) = ε (ρ 1)
      rw [ρ1]
      exact (hsu.symm.trans h3).trans hE1.symm
  have e0 : γ 0 = ζ 0 := hG0.trans hK0.symm
  have e1 : γ 1 = ζ 1 := hG1.trans hK1.symm
  have e0' : ε' 0 = ζ 0 := by
    change ε (ρ 0) = _
    rw [ρ0]
    exact hE0.trans hK0.symm
  have e1' : ε' 1 = ζ 1 := by
    change ε (ρ 1) = _
    rw [ρ1]
    exact hE1.trans hK1.symm
  obtain ⟨h₀, k₀, m, hc, hd⟩ := exists_bdMatch_of_arcs (c := h ∘ ζ) (d := h ∘ γ) (c' := h' ∘ ζ) (d'
    := h' ∘ ε')
    (arc c.hc hinjh hζ iζ onQ) (arc c.hc hinjh hγ iγ onG) (arc c'.hc hinjh' hζ iζ onQ')
    (arc c'.hc hinjh' (hε.comp hρ) (iε.comp iρ) fun s => onE _)
    (by simp [e0]) (by simp [e1]) (by simp [e0']) (by simp [e1'])
    (fun s u hsu => mm s u (hinjh (onQ s) (onG u) hsu))
    (fun s u hsu => mm' s u (hinjh' (onQ' s) (onE _) hsu))
  have sph : range (h ∘ ζ) ∪ range (h ∘ γ) = sphere 0 1 := by
    rw [range_comp, range_comp, ← image_union, rζ, rγ, ← hbQ, c.bd]
  have sph' : range (h' ∘ ζ) ∪ range (h' ∘ ε') = sphere 0 1 := by
    have : range ε' = E := by
      change range (ε ∘ ρ) = E
      rw [range_comp]
      rw [hsurj, image_univ, rε]
    rw [range_comp, range_comp, ← image_union, rζ, this, ← hbQ', c'.bd]
  rw [sph, sph'] at m
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner ⟨φ₀⟩ ⟨φ₀⟩ m
  rw [closedInner_sphere] at m'
  have hψsph : EqOn ψ h₀ (sphere 0 1) := hψ
  have bh : ∀ {x}, x ∈ discBd Q → h x ∈ sphere (0 : ℂ) 1 := fun hx => c.bd ▸ mem_image_of_mem h hx
  refine ⟨g' ∘ ψ ∘ h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact c'.gc.comp (m'.2.2.2.2.1.comp c.hc c.hm) (m'.1.comp c.hm)
  · intro x hx y hy hxy
    have h3 : ψ (h x) = ψ (h y) := c'.hg.injOn (m'.1 (c.hm hx)) (m'.1 (c.hm hy)) hxy
    exact hinjh hx hy (m'.2.2.1.injOn (c.hm hx) (c.hm hy) h3)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact c'.gm (m'.1 (c.hm hx))
    · intro hy
      refine ⟨g (χ (h' y)), c.gm (m'.2.1 (c'.hm hy)), ?_⟩
      change g' (ψ (h (g (χ (h' y))))) = y
      rw [c.hg (m'.2.1 (c'.hm hy)), m'.2.2.2.1 (c'.hm hy)]
      exact c'.gh hy
  · intro x hx
    obtain ⟨s, rfl⟩ : x ∈ range ζ := rζ ▸ hx
    change g' (ψ (h (ζ s))) = ζ s
    rw [hψsph (bh (bK s))]
    have := hc s
    simp only [Function.comp] at this
    rw [this]
    exact c'.gh (onQ' s)
  · change g' (ψ (h (γ t))) = ε t'
    rw [hψsph (bh (bG t))]
    have := hd t
    simp only [Function.comp, ε', ρt] at this
    rw [this]
    exact c'.gh (onE _)
  · have hval : ∀ s, g' (ψ (h (γ s))) = ε (ρ s) := fun s => by
      rw [hψsph (bh (bG s))]
      have := hd s
      simp only [Function.comp, ε'] at this
      rw [this, c'.gh (onE _)]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, rfl⟩ : x ∈ range γ := rγ ▸ hx
      change g' (ψ (h (γ s))) ∈ E
      rw [hval]
      exact rE _
    · intro hy
      obtain ⟨u, rfl⟩ : y ∈ range ε := rε ▸ hy
      obtain ⟨s, rfl⟩ : u ∈ range ρ := by
        rw [hsurj]
        exact mem_univ _
      exact ⟨γ s, rG s, hval s⟩

end GraphMinor.GM17
