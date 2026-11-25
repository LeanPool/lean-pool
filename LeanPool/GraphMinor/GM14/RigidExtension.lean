/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidSphere
public import LeanPool.GraphMinor.GM14.RigidMap
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.Surface.Schoenflies
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# (6.4)

We move the drawings in `Δ` to one of the two closed discs of the unit circle in the sphere, apply
`sphere_core` there, and move the homeomorphism back. It is the identity off `Δ` (`exists_extend`).
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- A homeomorphism of a closed set that fixes its frontier extends by the identity. -/
theorem exists_extend {X : Type u} [TopologicalSpace X] {Δ : Set X} (hc : IsClosed Δ) {k k' : X → X}
    (hP : PH Δ Δ k k') (hfix : ∀ x ∈ frontier Δ, k x = x) (hfix' : ∀ x ∈ frontier Δ, k' x = x) :
    ∃ ψ : X ≃ₜ X, EqOn ψ k Δ ∧ ψ '' Δ = Δ := by
  classical
  have hcont : ∀ {j : X → X}, ContinuousOn j Δ → (∀ x ∈ frontier Δ, j x = x) →
      Continuous fun x => if x ∈ Δ then j x else x := by
    intro j hj hf
    refine continuous_if (fun a ha => hf a ha) ?_ continuous_id.continuousOn
    have : closure {x | x ∈ Δ} = Δ := hc.closure_eq
    rw [this]
    exact hj
  have hi : ∀ {j j' : X → X}, PH Δ Δ j j' → ∀ x, (if (if x ∈ Δ then j x else x) ∈ Δ then
      j' (if x ∈ Δ then j x else x) else (if x ∈ Δ then j x else x)) = x := by
    intro j j' hj x
    by_cases hx : x ∈ Δ
    · simp only [hx, ite_true, hj.1 hx]
      exact hj.2.2.1 hx
    · simp [hx]
  let ψ : X ≃ₜ X :=
    { toFun := fun x => if x ∈ Δ then k x else x
      invFun := fun x => if x ∈ Δ then k' x else x
      left_inv := hi hP
      right_inv := hi hP.symm
      continuous_toFun := hcont hP.2.2.2.2.1 hfix
      continuous_invFun := hcont hP.2.2.2.2.2 hfix' }
  have hEq : EqOn ψ k Δ := fun x hx => ite_eq_left hx
  refine ⟨ψ, hEq, ?_⟩
  rw [hEq.image_eq]
  exact hP.image_eq

theorem chart_bd {W : Type*} [TopologicalSpace W] {E : Set W} {p : W → ℂ} {q : ℂ → W}
    (ch : IsChart E p q) : q '' sphere 0 1 ⊆ discBd E := by
  rintro _ ⟨z, hz, rfl⟩
  rw [← ch.bd] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rwa [ch.gh (Surface.discBd_subset E hw)]

/-- Inverse homeomorphisms from any closed disc to a closed disc in another space, boundary to
boundary. -/
theorem exists_disc_map {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {D : Set
  X}
    {D' : Set Y} (hD : IsClosedDisc D) (hD' : IsClosedDisc D') :
    ∃ f f', PH D D' f f' ∧ f '' discBd D ⊆ discBd D' ∧ f' '' discBd D' ⊆ discBd D := by
  obtain ⟨a, b, c⟩ := hD.exists_isChart
  obtain ⟨a', b', c'⟩ := hD'.exists_isChart
  have h₁ : PH D (closedBall 0 1) a b := ⟨c.hm, c.gm, c.gh, c.hg, c.hc, c.gc⟩
  have h₂ : PH D' (closedBall 0 1) a' b' := ⟨c'.hm, c'.gm, c'.gh, c'.hg, c'.hc, c'.gc⟩
  refine ⟨b' ∘ a, b ∘ a', h₁.comp h₂.symm, ?_, ?_⟩
  · rw [image_comp]
    refine Subset.trans (image_mono ?_) (chart_bd c')
    rw [c.bd]
  · rw [image_comp]
    refine Subset.trans (image_mono ?_) (chart_bd c)
    rw [c'.bd]

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **Graph Minors XIV, (6.4)** (page 34), in the form that its use in (6.5) needs. -/
theorem extension_64 {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ
  = discBd Δ) {H₁ H₂ : Drawing S}
    (hU₁ : H₁.U ⊆ Δ) (hU₂ : H₂.U ⊆ Δ) (hn₁ : H₁.U ∩ subBd Δ ⊆ H₁.V) (hn₂ : H₂.U ∩ subBd Δ ⊆ H₂.V)
    (hV : H₁.V ∩ subBd Δ = H₂.V ∩ subBd Δ) (φ : Iso H₁.toGraph H₂.toGraph)
    (hφ : ∀ v : V(H₁.toGraph), v.1 ∈ subBd Δ → (φ.vertexEquiv v).1 = v.1)
    (hr : ∀ F : Set S, F ⊆ Δ → IsOArc F → F ∩ H₁.U ⊆ H₁.V → (F ∩ H₁.V).ncard ≤ 2 →
      ∃ Δ' : Set S, Δ' ⊆ Δ ∧ IsDial H₁ F Δ') :
    ∃ ψ : S ≃ₜ S, ψ '' Δ = Δ ∧ (∀ x ∈ subBd Δ, ψ x = x) ∧
      (∀ v : V(H₁.toGraph), ψ v.1 = (φ.vertexEquiv v).1) ∧
      ∀ e : E(H₁.toGraph), ψ '' e.1 = (φ.edgeEquiv e).1 := by
  classical
  let T := OnePoint EuclideanPlane
  have hsph : IsSphere T := ⟨Homeomorph.refl _⟩
  obtain ⟨hS, hconn⟩ := IsSphere.isClosedSurface hsph
  have hSurf : IsSurface T := hS.isSurface
  have hO : IsOArc (sph '' sphere (0 : ℂ) 1) :=
    isOArc_image isOpenEmbedding_sph.isEmbedding oArc_sphere
  obtain ⟨D₁, D₂, -, hd₁, hd₂, hb₁, hb₂, hcov, hcap, -, -⟩ := sphere_disc T hsph _ hO
  set C : Set T := sph '' sphere (0 : ℂ) 1 with hC
  obtain ⟨f, f', hP, hf₁, hf₂⟩ := exists_disc_map hΔ hd₁
  have hAc : IsCompact Δ := hΔ.isCompact
  have hBc : IsCompact D₁ := hd₁.isCompact
  have hsbD : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hfC : ∀ {x}, x ∈ subBd Δ → f x ∈ C := fun {x} hx => by
    have h₁ : x ∈ discBd Δ := hbdΔ ▸ hx
    rw [← hb₁]
    exact hf₁ (mem_image_of_mem f h₁)
  have hfC' : ∀ {y}, y ∈ C → f' y ∈ subBd Δ := fun {y} hy => by
    rw [← hb₁] at hy
    rw [hbdΔ]
    exact hf₂ (mem_image_of_mem f' hy)
  have hsubΔ : subBd Δ ⊆ Δ := by
    rw [hbdΔ]
    exact Surface.discBd_subset Δ
  have hCD : C ⊆ D₁ := by
    rw [← hb₁]
    exact Surface.discBd_subset D₁
  have hcapi : ∀ {H : Drawing S}, H.U ⊆ Δ → H.U ∩ subBd Δ ⊆ H.V → f '' H.U ∩ C ⊆ f '' H.V := by
    rintro H hH hn _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have h₁ := hfC' hxC
    rw [hP.left (hH hx)] at h₁
    exact mem_image_of_mem f (hn ⟨hx, h₁⟩)
  have hVi : ∀ {H H' : Drawing S}, H.U ⊆ Δ → H.V ∩ subBd Δ = H'.V ∩ subBd Δ →
      f '' H.V ∩ C ⊆ f '' H'.V ∩ C := by
    rintro H H' hH hv _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have h₁ := hfC' hxC
    rw [hP.left (hH (H.V_subset_U hx))] at h₁
    have h₂ : x ∈ H'.V ∩ subBd Δ := hv ▸ ⟨hx, h₁⟩
    exact ⟨mem_image_of_mem f h₂.1, hxC⟩
  let M₁ := mapD hP hAc H₁ hU₁
  let M₂ := mapD hP hAc H₂ hU₂
  let ι₁ := mapIso hP hAc H₁ hU₁
  let ι₂ := mapIso hP hAc H₂ hU₂
  let φ' : Iso M₁.toGraph M₂.toGraph :=
    { vertexEquiv := ι₁.vertexEquiv.symm.trans (φ.vertexEquiv.trans ι₂.vertexEquiv)
      edgeEquiv := ι₁.edgeEquiv.symm.trans (φ.edgeEquiv.trans ι₂.edgeEquiv)
      isLink_iff := by
        intro e x y
        obtain ⟨e₀, rfl⟩ := ι₁.edgeEquiv.surjective e
        obtain ⟨x₀, rfl⟩ := ι₁.vertexEquiv.surjective x
        obtain ⟨y₀, rfl⟩ := ι₁.vertexEquiv.surjective y
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
        rw [← ι₁.isLink_iff, ← ι₂.isLink_iff, ← φ.isLink_iff] }
  have hφ'v : ∀ v : V(H₁.toGraph), (φ'.vertexEquiv (ι₁.vertexEquiv v)).1 = f (φ.vertexEquiv v).1
    := by
    intro v
    change (ι₂.vertexEquiv (φ.vertexEquiv (ι₁.vertexEquiv.symm (ι₁.vertexEquiv v)))).1 = _
    rw [Equiv.symm_apply_apply]
    exact mapIso_vertex hP hAc H₂ hU₂ _
  have hφ'e : ∀ e : E(H₁.toGraph), (φ'.edgeEquiv (ι₁.edgeEquiv e)).1 = f '' (φ.edgeEquiv e).1 := by
    intro e
    change (ι₂.edgeEquiv (φ.edgeEquiv (ι₁.edgeEquiv.symm (ι₁.edgeEquiv e)))).1 = _
    rw [Equiv.symm_apply_apply]
    exact mapIso_edge hP hAc H₂ hU₂ _
  obtain ⟨h, hhD, hhC, hhV, hhE⟩ := sphere_core hSurf hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap
    (H₁ := M₁) (H₂ := M₂) (hP.image_sub hU₁) (hP.image_sub hU₂) (hcapi hU₁ hn₁) (hcapi hU₂ hn₂)
    (subset_antisymm (hVi hU₁ hV) (hVi hU₂ hV.symm)) φ'
    (by
      intro w hw
      have hv : ι₁.vertexEquiv (ι₁.vertexEquiv.symm w) = w := Equiv.apply_symm_apply _ _
      obtain ⟨v, rfl⟩ : ∃ v, w = ι₁.vertexEquiv v := ⟨_, hv.symm⟩
      have hvb : v.1 ∈ subBd Δ := by
        have h₁ : f v.1 ∈ C := hw
        have h₂ := hfC' h₁
        rwa [hP.left (hU₁ (H₁.V_subset_U v.2))] at h₂
      rw [hφ'v, hφ v hvb]
      rfl)
    (isRigidIn_mapD hP hAc (by rw [hsbD]; exact image_subset_iff.mpr fun _ hx => hfC hx)
      (by rw [hsbD]; exact image_subset_iff.mpr fun _ hx => hfC' hx) H₁ hU₁ hr)
  have hH : PH D₁ D₁ h h.symm := by
    refine ⟨?_, ?_, fun x _ => h.symm_apply_apply x, fun x _ => h.apply_symm_apply x,
      h.continuous.continuousOn, h.symm.continuous.continuousOn⟩
    · exact fun x hx => hhD ▸ mem_image_of_mem h hx
    · intro y hy
      rw [← hhD] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
  have hk := (hP.comp hH).comp hP.symm
  have hfix : ∀ x ∈ subBd Δ, f' (h (f x)) = x := fun x hx => by
    rw [hhC _ (hfC hx)]
    exact hP.left (hsubΔ hx)
  have hfix' : ∀ x ∈ subBd Δ, f' (h.symm (f x)) = x := fun x hx => by
    have : h.symm (f x) = f x := by
      rw [Homeomorph.symm_apply_eq]
      exact (hhC _ (hfC hx)).symm
    rw [this]
    exact hP.left (hsubΔ hx)
  obtain ⟨ψ, hψ, hψD⟩ := exists_extend hΔ.isClosed hk
    (fun x hx => hfix x (subBd_eq_frontier Δ ▸ hx))
    (fun x hx => hfix' x (subBd_eq_frontier Δ ▸ hx))
  refine ⟨ψ, hψD, fun x hx => ?_, fun v => ?_, fun e => ?_⟩
  · rw [hψ (hsubΔ hx)]
    exact hfix x hx
  · have hvΔ := hU₁ (H₁.V_subset_U v.2)
    rw [hψ hvΔ]
    change f' (h (f v.1)) = _
    have h₁ := hhV (ι₁.vertexEquiv v)
    change h (f v.1) = _ at h₁
    rw [h₁, hφ'v, hP.left (hU₂ (H₂.V_subset_U (φ.vertexEquiv v).2))]
  · have heΔ : e.1 ⊆ Δ := cap_image H₁ hU₁ e.2
    have he₂ : (φ.edgeEquiv e).1 ⊆ Δ := cap_image H₂ hU₂ (φ.edgeEquiv e).2
    rw [hψ.mono heΔ |>.image_eq]
    change (f' ∘ (h ∘ f)) '' e.1 = _
    rw [image_comp, image_comp]
    have h₁ := hhE (ι₁.edgeEquiv e)
    change h '' (f '' e.1) = _ at h₁
    rw [h₁, hφ'e, hP.back he₂]

end GraphMinor.GM14.Whitney
