/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4
public import LeanPool.GraphMinor.GM16.SpanTransport
public import LeanPool.GraphMinor.GM20.Draw10
public import LeanPool.GraphMinor.Surface.HandleModel

/-!
# The surface tower

We prove `SurfaceTowerStatement`, which Graph Minors XVI, (3.1) needs (page 54).

Fix a finite graph `L`. By `Draw.exists_canBeDrawn`, there is `L₀` such that `L` can be drawn in
every model `Σ(a, b, 0)` with `L₀ ≤ a` or `L₀ ≤ b`. So a surface in which `L` cannot be drawn has `2
a + b ≤ 3 L₀`. Adding a crosscap raises `2 a + b` by one (`crosscap_model`), and adding a handle
raises it by two (`handle_model`). So the tower lists every model `Σ(a, b, 0)` with `2 a + b ≤ N`,
for `N = 3 L₀ + 2`, in the order of `2 a + b`. The surface after a step is homeomorphic to a later
member of the list, and spans move along homeomorphisms by `IsSigmaSpan.transport`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM15

universe u v w u' v'

/-- The handles of the surface at position `k` of the tower. The position is `e (N + 1) + x` for the
Euler genus `e`, and `x` picks the number of handles. -/
def towerA (N k : ℕ) : ℕ := min (k % (N + 1)) (k / (N + 1) / 2)

/-- The cross-caps of the surface at position `k` of the tower. -/
def towerB (N k : ℕ) : ℕ := k / (N + 1) - 2 * towerA N k

theorem tower_genus (N k : ℕ) : 2 * towerA N k + towerB N k = k / (N + 1) := by
  have : towerA N k ≤ k / (N + 1) / 2 := min_le_right _ _
  simp only [towerB]
  omega

theorem tower_index {N a b : ℕ} (h : 2 * a + b ≤ N) : towerA N ((2 * a + b) * (N + 1) + a) = a
  ∧ towerB N ((2 * a + b) * (N + 1) + a) = b := by
  have ha : a < N + 1 := by omega
  have h1 : ((2 * a + b) * (N + 1) + a) / (N + 1) = 2 * a + b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((2 * a + b) * (N + 1) + a) % (N + 1) = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : towerA N ((2 * a + b) * (N + 1) + a) = a := by
    simp only [towerA, h1, h2]
    omega
  refine ⟨h3, ?_⟩
  simp only [towerB, h1, h3]
  omega

theorem bd_model (a b : ℕ) : bd (SurfaceModel a b 0) = ∅ := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b 0
  have := ht
  have h1 := ncard_cuffs hf
  have hfin := (cuff_statement.{0} _ (isSurface_model a b 0).1).2.1
  have h2 : cuffs (SurfaceModel a b 0) = ∅ := (ncard_eq_zero hfin).mp h1
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  have h3 : connectedComponentIn (bd (SurfaceModel a b 0)) x ∈ cuffs (SurfaceModel a b 0)
    := ⟨x, hx, rfl⟩
  rw [h2] at h3
  exact h3

theorem isClosedSurface_ulift (a b : ℕ) : IsClosedSurface (ULift.{w} (SurfaceModel a b 0)) := by
  have hS := (isSurface_model a b 0).1
  have := hS.1
  have := hS.2.1
  let ψ : ULift.{w} (SurfaceModel a b 0) ≃ₜ SurfaceModel a b 0 := Homeomorph.ulift
  refine ⟨inferInstance, ψ.isEmbedding.t2Space, fun x => ?_⟩
  refine (isInteriorPoint_homeomorph_iff ψ x).mp ?_
  by_contra h
  have h1 : ψ x ∈ bd (SurfaceModel a b 0) := h
  rw [bd_model] at h1
  exact h1

/-- A graph is drawn in all models of large genus, as a graph in the sense of Graph Minors XVI. -/
theorem exists_drawn {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hV : V(L).Finite)
  (hE : E(L).Finite) :
    ∃ L₀, ∀ a b : ℕ, L₀ ≤ a ∨ L₀ ≤ b → CanBeDrawnIn (ULift.{w} (SurfaceModel a b 0)) L := by
  let H : Hypergraph α' β' := Hypergraph.ofGraph L hV hE
  have hG : H.IsGraph := by
    intro e he
    obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have hsub : H.ends e ⊆ {x, y} := by
      rintro w ⟨z, hz⟩
      rcases hz.left_eq_or_eq hl with h | h
      · exact .inl h
      · exact .inr h
    refine ⟨⟨x, ⟨y, hl⟩⟩, ?_⟩
    calc (H.ends e).ncard ≤ ({x, y} : Set α').ncard := ncard_le_ncard hsub (by simp)
      _ ≤ 2 := ncard_insert_le _ _ |>.trans (by simp)
  obtain ⟨L₀, hL⟩ := GM20.Draw.exists_canBeDrawn H hG
  refine ⟨L₀, fun a b hab => ?_⟩
  have := (isSurface_model a b 0).1.2.1
  obtain ⟨ν, F, h1, h2, h3, h4, h5⟩ := hL a b 0 hab
  let ψ : SurfaceModel a b 0 ≃ₜ ULift.{w} (SurfaceModel a b 0) := Homeomorph.ulift.symm
  refine ⟨ψ ∘ ν, fun e => ψ '' F e, ψ.injective.comp_injOn h1, ?_, ?_, ?_, ?_⟩
  · intro e he u₁ u₂ hl hne
    exact GM20.Draw.image_isLineWithEnds ψ (h2 e he u₁ u₂ hl.inc_left hl.inc_right hne)
  · intro e he x hl
    have he' : H.ends e = {x} := by
      ext w
      constructor
      · rintro ⟨z, hz⟩
        exact mem_singleton_iff.mpr ((Graph.IsLink.left_eq_or_eq hz hl).elim id id)
      · rintro rfl
        exact ⟨w, hl⟩
    obtain ⟨h6, h7⟩ := h3 e he x he'
    obtain ⟨g⟩ := h6
    exact ⟨⟨g.trans (ψ.image _)⟩, mem_image_of_mem _ h7⟩
  · intro e he f hf hef w hw
    rw [← image_inter ψ.injective] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨v, hv, rfl⟩ := h4 e he f hf hef hx
    exact ⟨v, hv, rfl⟩
  · intro e he v hv hm
    obtain ⟨z, hz, hez⟩ := hm
    exact h5 e he v hv (ψ.injective hez ▸ hz)

theorem isSphere_tower {a b : ℕ} (ha : a = 0) (hb : b = 0) : IsSphere (ULift.{w}
  (SurfaceModel a b 0)) := by
  subst ha hb
  obtain ⟨E⟩ := isSphere_model
  exact ⟨Homeomorph.ulift.trans E⟩

/-- One step from a closed connected surface with a model gives a surface with a model of larger `2
a + b`, by at most two. -/
theorem step_model {S S' : Type w} [TopologicalSpace S] [TopologicalSpace S'] [ConnectedSpace S]
  [ConnectedSpace S'] {a b : ℕ} (e : S ≃ₜ SurfaceModel a b 0)
    (h : IsObtainedByAddingHandleOrCrosscap S S') :
    ∃ a' b', Nonempty (S' ≃ₜ SurfaceModel a' b' 0) ∧ 2 * a + b < 2 * a' + b' ∧ 2 * a' + b'
      ≤ 2 * a + b + 2 := by
  have hb : bd S = ∅ := by
    rw [← image_bd_homeomorph e.symm, bd_model, image_empty]
  rcases h with ⟨hS, hS', hb', Λ₁, Λ₂, S₁, S₂, hΛ₁, hΛ₂, hd, -, -, hu, h1, h2, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨hS,
    hS', hb', Λ, S₁, S₂, hΛ, -, hu, h1, h2, ⟨e₁⟩, ⟨e₂⟩⟩
  · obtain ⟨a', b', h3, h4⟩ := handle_model hS hb hS' hb' hΛ₁ hΛ₂ hd hu h1 h2 e₁ e₂ e
    exact ⟨a', b', h3, by omega, by omega⟩
  · obtain ⟨a', b', h3, h4⟩ := crosscap_model hS hb hS' hb' hΛ hu h1 h2 e₁ e₂ e
    exact ⟨a', b', h3, by omega, by omega⟩

/-- **The surface tower.** Every finite graph has a tower of closed connected surfaces that starts
with the sphere and is closed under adding a handle or a crosscap to a surface in which the graph
cannot be drawn. -/
theorem surfaceTower : SurfaceTowerStatement.{u, v, w, u', v'} := by
  intro α' β' L hV hE
  obtain ⟨L₀, hL⟩ := exists_drawn.{w} L hV hE
  let N : ℕ := 3 * L₀ + 2
  refine ⟨{ n := (N + 1) * (N + 1)
            one_le_n := Nat.mul_pos (by omega) (by omega)
            Surf := fun i => ULift.{w} (SurfaceModel (towerA N i) (towerB N i) 0)
            topSpace := fun _ => inferInstance
            t2Space := fun i => (isClosedSurface_ulift _ _).2.1
            isClosedSurface := fun i => isClosedSurface_ulift _ _
            isConnected := fun i => ?_
            isSphere_zero := isSphere_tower (by simp [towerA]) (by simp [towerB, towerA])
            step_index := ?_ }⟩
  · have := (isSurface_model (towerA N i) (towerB N i) 0).2
    exact Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
  · intro i hnot α β G θ_star φ T_star S' _ _ H' η' θ_span' T' hcl hconn hadd hφ hspan
    have hc := (isSurface_model (towerA N i) (towerB N i) 0).2
    have hci : ConnectedSpace (ULift.{w} (SurfaceModel (towerA N i) (towerB N i) 0)) :=
      Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous
    have hsmall : towerA N i < L₀ ∧ towerB N i < L₀ := by
      by_contra h
      exact hnot (hL _ _ (by omega))
    obtain ⟨a', b', ⟨e'⟩, h3, h4⟩ := step_model (Homeomorph.ulift : ULift.{w} (SurfaceModel
      (towerA N i) (towerB N i) 0) ≃ₜ _) hadd
    have hle : 2 * a' + b' ≤ N := by
      simp only [N]
      omega
    obtain ⟨ea, eb⟩ := tower_index hle
    set k := (2 * a' + b') * (N + 1) + a' with hk
    have hkn : k < (N + 1) * (N + 1) := by
      have : (2 * a' + b' + 1) * (N + 1) ≤ (N + 1) * (N + 1) := Nat.mul_le_mul_right _ (by omega)
      have h5 : a' < N + 1 := by omega
      rw [Nat.add_mul] at this
      omega
    have hik : (i : ℕ) < k := by
      have h5 := tower_genus N i
      have h6 : ∀ m : ℕ, m < (m / (N + 1) + 1) * (N + 1) := fun m => by
        rw [Nat.mul_comm]
        exact Nat.lt_mul_div_succ m (by omega)
      replace h6 := h6 i
      have h7 : ((i : ℕ) / (N + 1) + 1) * (N + 1) ≤ (2 * a' + b') * (N + 1)
        := Nat.mul_le_mul_right _ (by omega)
      omega
    have hψ : ∀ x y, x = a' → y = b' → Nonempty (S' ≃ₜ ULift.{w} (SurfaceModel x y 0)) := by
      rintro _ _ rfl rfl
      exact ⟨e'.trans Homeomorph.ulift.symm⟩
    obtain ⟨ψ⟩ := hψ _ _ ea eb
    have : T2Space (ULift.{w} (SurfaceModel (towerA N k) (towerB N k) 0)) :=
      (isClosedSurface_ulift _ _).2.1
    exact ⟨⟨k, hkn⟩, hik, mapDrawingHomeo ψ H', SpanEmbedding.mapHomeo ψ η', θ_span', mapT ψ T',
      hφ, IsSigmaSpan.transport ψ hspan⟩

end GraphMinor.GM16
