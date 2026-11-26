/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section12d
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors XVII, Section 13: the complexity of a portrayal

This file proves (13.2) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 205. We read the number `4a + 2b + c` from the model criterion, and the
number of cuffs is `c`.

- **(13.2)** (`theorem_13_2`, page 205).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v u' v'

/-- The number of cuffs of a surface homeomorphic to `Σ(a, b, c)` is `c`. -/
theorem ncard_cuffs_of_homeo {S : Type} [TopologicalSpace S] {a b c : ℕ}
  (e : S ≃ₜ SurfaceModel a b c) : (cuffs S).ncard = c := by
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  let := ht
  rw [ncard_cuffs_congr e]
  exact ncard_cuffs hf

/-- The number `4a + 2b + c` depends only on the surface. -/
theorem model_rank_eq {S : Type} [TopologicalSpace S] {a b c a' b' c' : ℕ}
  (e : S ≃ₜ SurfaceModel a b c) (e' : S ≃ₜ SurfaceModel a' b' c') :
    4 * a + 2 * b + c = 4 * a' + 2 * b' + c' := by
  obtain ⟨h3, h4, -⟩ := (modelCriterion.2 a b c a' b' c').mp ⟨e.symm.trans e'⟩
  omega

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {G : Hypergraph α β} {G' :
  Hypergraph α' β'}

theorem Portrayal.hp_eq (p : ℕ) (π : Portrayal G) {a b c : ℕ} (e : π.S ≃ₜ SurfaceModel a b c) :
    π.hp p = (4 * a + 2 * b + c) ^ 2 * p + π.totalCuffWarp := by
  have h : sInf {k : ℕ | ∃ a b c : ℕ, Nonempty (π.S ≃ₜ SurfaceModel a b c) ∧ 4 * a + 2 * b + c = k}
    = 4 * a + 2 * b + c := by
    refine le_antisymm (Nat.sInf_le ⟨a, b, c, ⟨e⟩, rfl⟩) (le_csInf ⟨_, a, b, c, ⟨e⟩, rfl⟩ ?_)
    rintro _ ⟨a', b', c', ⟨e'⟩, rfl⟩
    exact (model_rank_eq e e').le
  unfold Portrayal.hp
  simp only [h]

theorem Portrayal.finite_cuffs (π : Portrayal G) : (cuffs π.S).Finite :=
  (cuff_statement.{0} π.S π.isSurface).2.1

theorem Portrayal.totalCuffWarp_eq (π : Portrayal G) : π.totalCuffWarp
  = ∑ Θ ∈ π.finite_cuffs.toFinset, π.warpAt Θ := by
  unfold Portrayal.totalCuffWarp
  rw [dite_eq_left π.finite_cuffs]

theorem Portrayal.totalCuffWarp_le (π : Portrayal G) {p c : ℕ} (hw : π.warp ≤ p) (hc :
  (cuffs π.S).ncard = c) : π.totalCuffWarp ≤ c * p := by
  rw [π.totalCuffWarp_eq]
  refine (Finset.sum_le_card_nsmul _ _ p fun Θ hΘ => ?_).trans ?_
  · exact (π.warpAt_le_warp (π.finite_cuffs.mem_toFinset.1 hΘ)).trans hw
  · rw [smul_eq_mul, ← Set.ncard_eq_toFinset_card _ π.finite_cuffs, hc]

/-- **Graph Minors XVII, (13.2)** (page 205): "Let $p \ge 1$, and let $\pi$, $\pi'$ be portrayals of
$G$, $G'$ respectively. If $\pi$ has warp $\le p$, and $\pi'$ is simpler than $\pi$, then $h_p(\pi')
< h_p(\pi)$." -/
theorem theorem_13_2_proof {p : ℕ} (hp : 1 ≤ p) (π : Portrayal G) (π' : Portrayal G') (hw : π.warp
  ≤ p) (hs : π'.IsSimpler π) :
    π'.hp p < π.hp p := by
  rcases hs with ⟨hS, hle⟩ | ⟨ψ, hle, Θ₀, hΘ₀, hlt⟩
  · obtain ⟨a', b', c', a, b, c, ⟨e'⟩, ⟨e⟩, -, -, hrk⟩ := hS
    rw [π'.hp_eq p e', π.hp_eq p e]
    have hr' := π'.totalCuffWarp_le (hle.trans hw) (ncard_cuffs_of_homeo e')
    set g' := 4 * a' + 2 * b' + c'
    set g := 4 * a + 2 * b + c
    have hc' : c' ≤ g' := by omega
    have h1 : c' * p ≤ g' * p := Nat.mul_le_mul_right p hc'
    have h2 : g' + 1 ≤ g := hrk
    have h3 : g' * g' + g' < g * g := by nlinarith
    have h4 : (g' * g' + g' + 1) * p ≤ (g * g) * p := Nat.mul_le_mul_right p h3
    have hpos : 0 < p := hp
    have h5 : g' ^ 2 * p + c' * p < g ^ 2 * p := by nlinarith
    omega
  · obtain ⟨a, b, c, ⟨e⟩⟩ := classification π.S π.isSurface π.connected
    rw [π'.hp_eq p (ψ.trans e), π.hp_eq p e, π'.totalCuffWarp_eq, π.totalCuffWarp_eq]
    refine Nat.add_lt_add_left ?_ _
    have hinj : Set.InjOn (fun Θ : Set π'.S => ψ '' Θ) (cuffs π'.S) := fun _ _ _ _ h
      => ψ.injective.image_injective h
    have him : (fun Θ : Set π'.S => ψ '' Θ) '' cuffs π'.S = cuffs π.S := by
      refine Subset.antisymm ?_ fun Φ hΦ =>
        ⟨ψ.symm '' Φ, image_cuff_mem_cuffs ψ.symm hΦ, by ext x; simp⟩
      rintro _ ⟨Θ, hΘ, rfl⟩
      exact image_cuff_mem_cuffs ψ hΘ
    have hsum : ∑ Φ ∈ π.finite_cuffs.toFinset, π.warpAt Φ = ∑ Θ ∈ π'.finite_cuffs.toFinset,
      π.warpAt (ψ '' Θ) := by
      symm
      refine Finset.sum_bij (fun Θ _ => ψ '' Θ) ?_ ?_ ?_ fun _ _ => rfl
      · intro Θ hΘ
        exact π.finite_cuffs.mem_toFinset.2 (image_cuff_mem_cuffs ψ (π'.finite_cuffs.mem_toFinset.1
          hΘ))
      · intro Θ _ Θ' _ h
        exact ψ.injective.image_injective h
      · intro Φ hΦ
        exact ⟨ψ.symm '' Φ,
          π'.finite_cuffs.mem_toFinset.2
            (image_cuff_mem_cuffs ψ.symm (π.finite_cuffs.mem_toFinset.1 hΦ)), by ext x; simp⟩
    rw [hsum]
    exact Finset.sum_lt_sum (fun Θ hΘ => hle Θ (π'.finite_cuffs.mem_toFinset.1 hΘ)) ⟨Θ₀,
      π'.finite_cuffs.mem_toFinset.2 hΘ₀, hlt⟩

end GraphMinor.GM17
