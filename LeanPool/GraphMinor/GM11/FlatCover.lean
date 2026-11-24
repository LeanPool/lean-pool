/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.Collar

/-!
# A cover of a set by flat open sets

`flat_iUnion_cover` is a form of (11.5) of Graph Minors VII (page 251) for sets that meet in more
than one
piece. Each set `O i` has a base point in a flat set `Z`. Where `O i` and `O j` meet, the path
through a meeting
point is homotopic to a path in `Z`. Then the union of the sets `O i` is flat.

`not_flat_compl_disc` says that in a closed connected surface that is not a sphere, the outside of a
closed disc
is not included in a flat open set. The proof of (6.4) of Graph Minors XI (pages 90–91) uses this.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {T : Type u} [TopologicalSpace T]

theorem cl_trans_symm_left {a b c : T} (f : Cl a b) (g : Cl a c) : f.trans (f.symm.trans g) = g
  := by
  rw [← cl_assoc, cl_trans_symm, cl_refl_trans]

/-- A form of **(11.5)** of Graph Minors VII (page 251). -/
theorem flat_iUnion_cover {ι : Type*} {Z : Set T} (hZ : Flat Z) (O : ι → Set T) (b : ι → T)
    (hOo : ∀ i, IsOpen (O i)) (hb : ∀ i, b i ∈ O i) (hOc : ∀ i, IsPathConnected (O i))
      (hOf : ∀ i, Flat (O i))
    (hpair : ∀ i j y, y ∈ O i → y ∈ O j → ∃ (f : Cl (b i) y) (g : Cl y (b j)), Arw (O i) f ∧ Arw
      (O j) g ∧
      Arw Z (f.trans g)) : Flat (⋃ i, O i) := by
  have harw : ∀ i, ∀ x ∈ O i, ∀ y ∈ O i, ∃ f : Cl x y, Arw (O i) f := fun i x hx y hy => by
    have hj := (hOc i).joinedIn x hx y hy
    exact ⟨Cl.mk hj.somePath, hj.somePath, fun u => hj.somePath_mem u, rfl⟩
  have key : ∀ (a e : T) (p : Path a e), (∀ u, p u ∈ ⋃ i, O i) → ∀ (i₀ : ι) (α : Cl
    (b i₀) a), a ∈ O i₀ →
      Arw (O i₀) α → ∃ i, e ∈ O i ∧ ∃ (β : Cl e (b i)) (θ : Cl (b i₀) (b i)), Arw (O i) β ∧ Arw Z θ
        ∧
        α.trans ((Cl.mk p).trans β) = θ := by
    intro a e p hp i₀ α ha hα
    let Q : ∀ c : T, Cl a c → Prop := fun c f => ∃ i, c ∈ O i ∧ ∃ (β : Cl c (b i)) (θ : Cl (b i₀)
      (b i)),
      Arw (O i) β ∧ Arw Z θ ∧ α.trans (f.trans β) = θ
    refine cl_induction (𝒞 := range O) ?_ p (fun u => ?_) Q ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact hOo i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hp u)
      exact ⟨O i, ⟨i, rfl⟩, hi⟩
    · obtain ⟨f, g, hf, hg, hw⟩ := hpair i₀ i₀ a ha ha
      refine ⟨i₀, ha, α.symm, Cl.rf _, hα.symm, arw_refl hw.left_mem, ?_⟩
      rw [cl_refl_trans, cl_trans_symm]
    · rintro c d f r _ ⟨j, rfl⟩ hr ⟨i, hc, β, θ, hβ, hθ, e⟩
      have hc' : c ∈ O j := by simpa using hr 0
      have hd' : d ∈ O j := by simpa using hr 1
      obtain ⟨f', g', hf', hg', hw⟩ := hpair i j c hc hc'
      obtain ⟨β', hβ'⟩ := harw j d hd' (b j) (hb j)
      have h₁ : f' = β.symm := (hOf i).eq hf' hβ.symm
      have h₂ : (Cl.mk r).trans β' = g' := (hOf j).eq ((Arw.of_path r hr).trans hβ') hg'
      refine ⟨j, hd', β', θ.trans (f'.trans g'), hβ', hθ.trans hw, ?_⟩
      rw [h₁, ← e]
      simp only [cl_assoc, ← h₂, cl_trans_symm_left]
  intro a e p q hp hq
  obtain ⟨i₀, ha⟩ := mem_iUnion.mp (by simpa using hp 0 : a ∈ ⋃ i, O i)
  obtain ⟨α, hα⟩ := harw i₀ _ (hb i₀) a ha
  obtain ⟨i, hi, β, θ, hβ, hθ, e₁⟩ := key a e p hp i₀ α ha hα
  obtain ⟨j, hj, β', θ', hβ', hθ', e₂⟩ := key a e q hq i₀ α ha hα
  obtain ⟨f, g, hf, hg, hw⟩ := hpair i j e hi hj
  have h₁ : f = β.symm := (hOf i).eq hf hβ.symm
  have h₂ : g = β' := (hOf j).eq hg hβ'
  have h₃ : θ' = θ.trans (f.trans g) := hZ.eq hθ' (hθ.trans hw)
  refine Path.Homotopic.Quotient.eq.mp (cl_cancel α g ?_)
  rw [h₂, e₂, h₃, ← e₁, h₁, h₂]
  simp only [cl_assoc, cl_trans_symm_left]

/-- The inclusion of `T` in the subtype `univ`. -/
def toUniv : C(T, (univ : Set T)) := ⟨fun x => ⟨x, trivial⟩, by fun_prop⟩

/-- Flatness in `T` is flatness in the subtype `univ`. -/
theorem flat_univ_iff {A : Set T} : Flat (Subtype.val ⁻¹' A : Set (univ : Set T)) ↔ Flat A := by
  constructor
  · intro h a b p q hp hq
    have := (h (p.map toUniv.continuous) (q.map toUniv.continuous) hp hq).map ⟨Subtype.val,
      continuous_subtype_val⟩
    exact this
  · intro h a b p q hp hq
    have := (h (p.map continuous_subtype_val) (q.map continuous_subtype_val) hp hq).map toUniv
    exact this

/-- An `O`-arc in a flat set is null-homotopic. -/
theorem null_of_flat {K F : Set T} (hK : Flat K) (hF : IsOArc F) (hFK : F ⊆ K) :
  IsNullHomotopicOArc F := by
  have hK' := flat_univ_iff.mpr hK
  obtain ⟨ψ⟩ := id hF
  let φ : C(Circle, T) := ⟨fun x => (ψ x).1, continuous_subtype_val.comp ψ.continuous⟩
  let a : (univ : Set T) := ⟨φ (arcParam 1 0), trivial⟩
  let γ : Path a a := ⟨⟨fun t => ⟨φ (arcParam 1 t), trivial⟩, by fun_prop⟩, rfl, Subtype.ext
    (by simp [a])⟩
  have hγ : ∀ u, γ u ∈ (Subtype.val ⁻¹' K : Set (univ : Set T)) := fun u => hFK (ψ _).2
  have hh : γ.Homotopic (Path.refl a) := hK' _ _ hγ fun _ => by simpa using hγ 0
  exact ⟨ψ, a.1, a.2, closedCurvesHomotopicIn_of_path 1 φ (ContinuousMap.const _ a.1) γ
    (Path.refl a) (fun _ => rfl)
    (fun _ => rfl) hh⟩

/-- In a closed connected surface that is not a sphere, the outside of a closed disc does not lie in
a flat set. -/
theorem not_flat_compl_disc {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
  (hS : IsClosedSurface S)
    (hns : ¬ IsSphere S) {Δ K : Set S} (hΔ : IsClosedDisc Δ) (hsub : Δᶜ ⊆ K) (hf : Flat K) : False
      := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨Δ', hΔ', h₁, -⟩ := exists_disc_around hman hΔ (fun x _ => hS.2.2 x) isOpen_univ
    (subset_univ _)
  have hO := IsClosedDisc.isOArc_discBd hΔ'
  have hif : Δ' \ discBd Δ' = interior Δ' := by
    have := IsClosedDisc.frontier_eq_discBd hS hΔ'
    rw [← this, frontier, (IsClosedDisc.isCompact hΔ').isClosed.closure_eq]
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      by_contra h
      exact h₂ ⟨h₁, h⟩
    · exact fun h => ⟨interior_subset h, fun h' => h'.2 h⟩
  let Y : Set S := (interior Δ')ᶜ
  have hYc : IsClosed Y := isOpen_interior.isClosed_compl
  have hbY : discBd Δ' ⊆ Y := fun x hx hi => by
    rw [← hif] at hi
    exact hi.2 hx
  have hYK : Y ⊆ K := fun x hx => hsub fun hxΔ => hx (hif ▸ h₁ hxΔ)
  obtain ⟨a, ha⟩ := (infinite_of_isOArc hO).nonempty
  obtain ⟨N, hNU, -⟩ := exists_drawing_on_oArc hO (finite_singleton a) (singleton_nonempty a)
    (singleton_subset_iff.mpr ha)
  have hYn : IsNice Y := ⟨N, isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) (hNU ▸ hbY) (by
    rw [hNU, frontier_compl, ← IsClosedDisc.frontier_eq_discBd hS hΔ']
    exact frontier_interior_subset)⟩
  have hu : Y ≠ univ := fun h => by
    obtain ⟨x, hx⟩ := (infinite_of_isOArc (IsClosedDisc.isOArc_discBd hΔ)).nonempty
    exact (h ▸ mem_univ x : x ∈ Y) (hif ▸ h₁ (discBd_subset Δ hx))
  obtain ⟨E, hE, -, hYE⟩ := theorem_7_5_proof hS hYc hYn hu (finite_empty)
    (disjoint_empty _) fun F hFY hF => by
    rw [sdiff_empty]
    exact null_of_flat hf hF (hFY.trans hYK)
  obtain ⟨D, ⟨hDE, hD, hb, -⟩, -⟩ := disc_oArc E (discBd Δ') hE (hbY.trans hYE) hO
  obtain rfl : D = Δ' := eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hD hΔ' hb
  have huE : E = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ interior D
    · exact hDE (interior_subset hx)
    · exact hYE hx
  have hfr := IsClosedDisc.frontier_eq_discBd hS hE
  rw [huE, frontier_univ] at hfr
  have hO' := IsClosedDisc.isOArc_discBd hE
  rw [huE, ← hfr] at hO'
  exact (infinite_of_isOArc hO').nonempty.ne_empty rfl

end GraphMinor.GM11
