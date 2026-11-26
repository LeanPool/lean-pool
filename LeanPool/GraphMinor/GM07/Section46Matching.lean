/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PullForest
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.NetExists

/-!
# The lifted matching in VII (4.6)

On page 226, `θ⁻¹(K)` is a matching in `Σ′`, and `Δ` is obtained from `Σ′`
by cutting along it. Here we take three facts about `K`: each vertex
lies in the closure of exactly one edge, each edge has two ends, and `θ`
is one-to-one over `U(K)`. The pullback is then a matching. The cut map
`ψ` inherits its properties from `φ`.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

/-- The property that every vertex ends exactly one edge, which has two different ends. -/
@[expose] def IsPairing (K : Drawing S) : Prop :=
  ∀ v ∈ K.V, ∃ e ∈ K.E, v ∈ closure e ∧ (tilde e).ncard = 2 ∧
    ∀ e' ∈ K.E, v ∈ closure e' → e' = e

theorem IsPairing.vertexValency_eq_one {K : Drawing S} (h : IsPairing K) {v : S} (hv : v ∈ K.V) :
    vertexValency K v = 1 := by
  obtain ⟨e, he, hve, hcard, huniq⟩ := h v hv
  have hA : {f ∈ K.E | K.VertexIncident v f ∧ (tilde f).ncard = 2} = {e} := by
    ext f
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hf, hi, -⟩
      exact huniq f hf hi.2.2
    · rintro rfl
      exact ⟨he, ⟨hv, .inl he, hve⟩, hcard⟩
  have hB : {f ∈ K.E | K.VertexIncident v f ∧ (tilde f).ncard = 1} = ∅ := by
    ext f
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hf, hi, hone⟩
    rw [huniq f hf hi.2.2, hcard] at hone
    omega
  unfold vertexValency
  rw [hA, hB]
  simp

theorem IsPairing.isGraphForest {K : Drawing S} (h : IsPairing K) : IsGraphForest K.toGraph := by
  intro u W hW
  match W, hW with
  | .nil _, _ => rfl
  | .cons (u := u) (v := v) (e := e) hlink rest, hW =>
    have hab : u ≠ v := by
      rintro rfl
      obtain ⟨e₀, he₀, hve₀, hcard, huniq⟩ := h u hlink.2.1
      have heq := huniq e hlink.1 (hlink.2.2.2.symm.subset (by simp) |>.1)
      subst heq
      rw [tilde_eq_closure_inter_V K he₀, hlink.2.2.2] at hcard
      simp at hcard
    match rest, hW with
    | .nil _, _ => exact (hab rfl).elim
    | .cons (e := e₂) hlink₂ rest₂, hW =>
      have hmem : ∀ {f x y}, K.toGraph.IsLink f x y → x ∈ closure f := fun hl =>
        (hl.2.2.2.symm.subset (by simp)).1
      obtain ⟨e₀, he₀, _, _, huniq⟩ := h _ hlink₂.2.1
      have h1 : e = e₀ := huniq e hlink.1 ((hlink.2.2.2.symm.subset (by simp)).1)
      have h2 : e₂ = e₀ := huniq e₂ hlink₂.1 (hmem hlink₂)
      have hnd := hW.2
      simp [GraphWalk.edges, h1, h2] at hnd

/-- The pullback of `K` under `θ` is a matching, in VII (4.6), page 226. -/
theorem exists_lifted_matching (hS : IsSurface S) {L K : Drawing S} {θ : S' → S}
    (hθ : IsCutAlongGraph L S' θ) (hK : IsPairing K) (hKp : K.IsProper) (hKL : K.V ⊆ L.U)
    (hKn : K.IsNormal L.U) (hinj : InjOn θ (θ ⁻¹' K.U)) :
    ∃ K' : Drawing S', IsPullbackDrawing θ K K' ∧ IsMatching K' ∧ IsPairing K' := by
  classical
  have hF : IsSurfaceForest K := ⟨hKp, hK.isGraphForest⟩
  obtain ⟨K', hp, hprop, hE⟩ := exists_pullback hS hθ hF hKn
  have hs := hθ.quotientMap.surjective
  have hlift : ∀ e ∈ K.E, θ ⁻¹' e ∈ K'.E ∧ θ '' closure (θ ⁻¹' e) = closure e ∧
      InjOn θ (closure (θ ⁻¹' e)) := by
    intro e he
    obtain ⟨y, hy⟩ := he.1
    obtain ⟨y', rfl⟩ := hs y
    have hyU : θ y' ∈ K.U \ K.V := he.2.1 hy
    have hy' : y' ∈ K'.U \ K'.V := by
      rw [hp.1, hp.2]
      exact hyU
    have he' : pathComponentIn (K'.U \ K'.V) y' ∈ K'.E := pathComponentIn_mem_arcComponentsIn hy'
    obtain ⟨e₁, he₁, heq, him, hi⟩ := hE _ he'
    have hmem : y' ∈ pathComponentIn (K'.U \ K'.V) y' := mem_pathComponentIn_self hy'
    have hy₁ : θ y' ∈ e₁ := by
      rw [heq] at hmem
      exact hmem
    have hee : e₁ = e := arcComponentsIn_eq_of_mem he₁ he hy₁ hy
    subst hee
    rw [heq] at he'
    rw [heq] at him hi
    exact ⟨he', him, hi⟩
  have hclosure : ∀ e ∈ K.E, ∀ x, θ x ∈ closure e → x ∈ closure (θ ⁻¹' e) := by
    intro e he x hx
    obtain ⟨hl, him, -⟩ := hlift e he
    rw [← him] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    have hxU : θ x ∈ K.U := K.closure_subset_U he (him ▸ ⟨x', hx', hxx⟩)
    have : x' = x := hinj (show θ x' ∈ K.U from hxx ▸ hxU) hxU hxx
    exact this ▸ hx'
  have hpair : IsPairing K' := by
    intro x hx
    have hxV : θ x ∈ K.V := by
      rw [hp.2] at hx
      exact hx
    obtain ⟨e, he, hxe, hcard, huniq⟩ := hK _ hxV
    obtain ⟨hl, him, hi⟩ := hlift e he
    refine ⟨θ ⁻¹' e, hl, hclosure e he x hxe, ?_, ?_⟩
    · have hti : θ '' tilde (θ ⁻¹' e) = tilde e := by
        rw [tilde_eq_closure_inter_V K' hl, tilde_eq_closure_inter_V K he, hp.2]
        ext z
        constructor
        · rintro ⟨w, ⟨hw, hwV⟩, rfl⟩
          exact ⟨him ▸ mem_image_of_mem θ hw, hwV⟩
        · rintro ⟨hz, hzV⟩
          rw [← him] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          exact ⟨w, ⟨hw, hzV⟩, rfl⟩
      have hsub : tilde (θ ⁻¹' e) ⊆ closure (θ ⁻¹' e) := sdiff_subset
      rw [← hcard, ← hti, (hi.mono hsub).ncard_image]
    · intro e'' he'' hxe''
      obtain ⟨e₂, he₂, heq, him₂, -⟩ := hE e'' he''
      have hmem : θ x ∈ closure e₂ := him₂ ▸ mem_image_of_mem θ hxe''
      rw [heq, huniq e₂ he₂ hmem]
  refine ⟨K', hp, ⟨hprop, ?_, fun v hv => hpair.vertexValency_eq_one hv⟩, hpair⟩
  intro x hx
  rw [hp.2] at hx
  rw [← hθ.preimage_bd_union_U]
  exact .inr (hKL hx)

/-- The map `ψ` cuts `Δ` from `Σ′` along the matching, in VII (4.6), page 226. -/
theorem Net.isCutAlongGraph_psi {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']
    (N : Net S) {L K : Drawing S} {K' : Drawing S'} {θ : S' → S} {ψ : N.D → S'}
    (hθ : IsCutAlongGraph L S' θ) (hp : IsPullbackDrawing θ K K') (hK' : IsMatching K')
    (hK'p : IsPairing K') (hψc : Continuous ψ) (hψs : Function.Surjective ψ)
    (hψ : ∀ x, θ (ψ x) = N.φ x) (hcover : bd S ∪ L.U ∪ K.U = N.seamU) :
    IsCutAlongGraph K' N.D ψ := by
  have hD := N.isSurface_D
  have : CompactSpace N.D := hD.1
  have hS' := hθ.isSurface
  have : T2Space S' := hS'.2.1
  have hbd : ψ ⁻¹' (bd S' ∪ K'.U) = bd N.D := by
    rw [← N.preimage_seamU, ← hcover, ← hθ.preimage_bd_union_U, hp.1, ← preimage_union,
      ← preimage_comp]
    congr 1
    exact funext hψ
  refine ⟨hK'.1, ?_, hD, hψc.isClosedMap.isQuotientMap hψc hψs, hbd, ?_, ?_⟩
  · intro v hv
    obtain ⟨e, he, hve, -, -⟩ := hK'p v hv
    exact ⟨e, he, hv, .inl he, hve⟩
  · intro x hx y hxy
    exact N.interior_inj x hx y (by rw [← hψ, ← hψ, hxy])
  · intro z
    obtain ⟨x, rfl⟩ := hψs z
    apply (N.finite_preimage_singleton (N.φ x)).subset
    intro y hy
    have hy' : ψ y = ψ x := hy
    change N.φ y = N.φ x
    rw [← hψ, ← hψ, hy']

end GraphMinor.GM07
