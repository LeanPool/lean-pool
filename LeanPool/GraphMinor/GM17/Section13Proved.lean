/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section13d
public import LeanPool.GraphMinor.Surface.DrawCarry

import LeanPool.GraphMinor.GM17.Section8Proved

/-!
# Graph Minors XVII, (13.4)

(13.4) follows the paper's proof (page 207): a planar `H` is handled by (13.1) directly; otherwise
`a*`, `b*` are chosen with `2a* + b*` maximum such that `H` cannot be drawn in `Σ(a*, b*, 0)`, and
`q = 4a* + 2b* + q₀`. That maximum exists because `H` can be drawn in `Σ(a, b, c)` once `a` or `b`
is
large (`GM20.Draw.exists_canBeDrawn`).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- **Graph Minors XVII, (13.4)** (page 206): "For any graph $H$ and standard $\sigma$, there are
numbers $p, q, z$ and $\theta > z$, such that for every graph $G$ and every tangle $\mathscr{T}$ in
$G$ of order $\ge \theta$, either (i) $\mathscr{T}$ controls an $H$-minor of $G$, or (ii) there
exists $Z \subseteq V(G)$ with $|Z| \le z$, and a $(\mathscr{T} \setminus Z)$-central portrayal $\pi
= (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$ with warp $\le p$, such that $\Sigma$
has $\le q$ cuffs, $H$ cannot be drawn in $\Sigma$, and $\pi$ is $\sigma(\Sigma, p, |Z|)$-redundant
and true." -/
theorem theorem_13_4_proof {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph)
    (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (hσ : IsStandard σ) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
        π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧ ¬ CanBeDrawn π.S H ∧ π.IsTrue
          (deleteVerticesTangle G Z 𝒯 θ') ∧
        π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S p Z.ncard) := by
  classical
  obtain ⟨p₀, q₀, z₀, θ₀, hz₀, h1⟩ := GraphMinor.GM17.theorem_13_1_proof.{u, v} H hH
  -- "If $H$ is planar, let $p, q, z, \theta$ be as in (13.1); then the theorem is satisfied (for
  -- (13.1)(ii) cannot hold since $H$ is planar)."
  by_cases hplanar : CanBeDrawn (SurfaceModel 0 0 0) H
  · refine ⟨p₀, q₀, z₀, θ₀, hz₀, ?_⟩
    intro α β G hG θ' 𝒯 h𝒯 hθ
    rcases h1 G hG θ' 𝒯 h𝒯 hθ with hctrl | ⟨Z₀, -, -, π₀, -, -, -, hdr₀⟩
    · exact .inl hctrl
    · exfalso
      obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification π₀.S π₀.isSurface π₀.connected
      have : T2Space π₀.S := π₀.isSurface.2.1
      have : T2Space (SurfaceModel a₀ b₀ c₀) := e₀.symm.isEmbedding.t2Space
      exact hdr₀ (GM20.Draw.CanBeDrawn.map e₀.symm
        (canBeDrawn_of_le hH (Nat.zero_le a₀) (Nat.zero_le b₀) hplanar))
  -- "Choose $a^*, b^* \ge 0$ with $2a^* + b^*$ maximum so that $H$ cannot be drawn in
  -- $\Sigma(a^*, b^*, 0)$." The maximum exists, since `H` can be drawn when `a` or `b` is large.
  obtain ⟨L, hL⟩ := GM20.Draw.exists_canBeDrawn H hH
  have hsmall : ∀ a b : ℕ, ¬ CanBeDrawn (SurfaceModel a b 0) H → 2 * a + b < 3 * L + 1 := by
    intro a b hn
    have : T2Space (SurfaceModel a b 0) := (isSurface_model a b 0).1.2.1
    by_contra hlt
    exact hn (hL a b 0 (by omega))
  let Pm : ℕ → Prop := fun n => ∃ a b : ℕ, 2 * a + b = n ∧ ¬ CanBeDrawn (SurfaceModel a b 0) H
  have hP0 : Pm 0 := ⟨0, 0, rfl, hplanar⟩
  let m := Nat.findGreatest Pm (3 * L)
  obtain ⟨aS, bS, hmS, -⟩ : Pm m := Nat.findGreatest_spec (P := Pm) (Nat.zero_le _) hP0
  have hmax : ∀ a b : ℕ, ¬ CanBeDrawn (SurfaceModel a b 0) H → 2 * a + b ≤ 2 * aS + bS := by
    intro a b hn
    have hle : 2 * a + b ≤ m :=
      Nat.le_findGreatest (P := Pm) (by have := hsmall a b hn; omega) ⟨a, b, rfl, hn⟩
    omega
  set p := max p₀ 1 with hpdef
  have hp : 1 ≤ p := le_max_right _ _
  -- "Let $q = 4a^* + 2b^* + q_0$, and let $h = p(q^2 + q_0)$."
  set q := 4 * aS + 2 * bS + q₀ with hq
  obtain ⟨θ₁, z, hz, hzz, h3⟩ := theorem_13_3_proof.{u, v} σ hσ hp (q ^ 2 * p + q₀ * p) z₀
  refine ⟨p, q, z, max θ₀ θ₁, lt_max_of_lt_right hz, ?_⟩
  intro α β G hG θ' 𝒯 h𝒯 hθ
  rcases h1 G hG θ' 𝒯 h𝒯 ((le_max_left _ _).trans hθ) with hctrl | ⟨Z₀, hZ₀, hc₀, π₀, hcen₀, hw₀,
    hcu₀, hdr₀⟩
  · exact .inl hctrl
  refine .inr ?_
  have hθ₁ : θ₁ ≤ θ' := (le_max_right _ _).trans hθ
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification π₀.S π₀.isSurface π₀.connected
  have hc₀c : c₀ ≤ q₀ := by
    have h₁ := ncard_cuffs_of_homeo e₀
    have h₂ : ((cuffs π₀.S).ncard : ℕ∞) = (cuffs π₀.S).encard := π₀.finite_cuffs.cast_ncard_eq
    rw [← h₂, h₁] at hcu₀
    exact_mod_cast hcu₀
  -- $H$ cannot be drawn in $\Sigma(a_0, b_0, 0)$, since it cannot be drawn in $\Sigma_0$, and so
  -- $2a_0 + b_0 \le 2a^* + b^*$ by the choice of $a^*, b^*$.
  have hab : 2 * a₀ + b₀ ≤ 2 * aS + bS := by
    refine hmax a₀ b₀ fun hd => ?_
    have : T2Space π₀.S := π₀.isSurface.2.1
    have : T2Space (SurfaceModel a₀ b₀ c₀) := e₀.symm.isEmbedding.t2Space
    exact hdr₀ (GM20.Draw.CanBeDrawn.map e₀.symm (canBeDrawn_of_le hH le_rfl le_rfl hd))
  -- "$4a_0 + 2b_0 + c_0 \le 4a^* + 2b^* + q_0 = q$"
  have hrank₀ : 4 * a₀ + 2 * b₀ + c₀ ≤ q := by omega
  have hh : π₀.hp p ≤ q ^ 2 * p + q₀ * p := by
    rw [π₀.hp_eq p e₀]
    have h₁ := π₀.totalCuffWarp_le (p := p) (hw₀.trans (le_max_left _ _)) (ncard_cuffs_of_homeo e₀)
    have h₂ : (4 * a₀ + 2 * b₀ + c₀) ^ 2 * p ≤ q ^ 2 * p := Nat.mul_le_mul_right _
      (Nat.pow_le_pow_left hrank₀ 2)
    have h₃ : c₀ * p ≤ q₀ * p := Nat.mul_le_mul_right _ hc₀c
    omega
  obtain ⟨Z, -, hZ, hcZ, π, hcen, hrel, hred⟩ := h3 G hG θ' 𝒯 h𝒯 hθ₁ Z₀ hZ₀ hc₀ π₀ hcen₀ (hw₀.trans
    (le_max_left _ _)) hh
  have hzθ : Z.ncard < θ' := by omega
  have ht := GM10.theorem_8_5_proof hG h𝒯 hZ hzθ
  obtain ⟨π', htrue, hres, hred'⟩ := exists_true_resembling ht hcen hred
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification π.S π.isSurface π.connected
  have hstep : (4 * a + 2 * b + c ≤ q) ∧ ¬ CanBeDrawn π.S H := by
    rcases hrel with hs | hs
    · rcases hs with ⟨hS, -⟩ | ⟨ψ, -, -⟩
      · refine ⟨?_, fun hd => hdr₀ (hS.canBeDrawn hH hd)⟩
        obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, ⟨e₁⟩, ⟨e₂⟩, -, -, hlt⟩ := hS
        have h₁ := model_rank_eq e e₁
        have h₂ := model_rank_eq e₀ e₂
        omega
      · exact ⟨by rwa [model_rank_eq e (ψ.trans e₀)],
          fun hd => hdr₀ (GM20.Draw.CanBeDrawn.map ψ hd)⟩
    · obtain ⟨ψ, -⟩ := hs
      exact ⟨by rwa [model_rank_eq e (ψ.trans e₀)],
        fun hd => hdr₀ (GM20.Draw.CanBeDrawn.map ψ hd)⟩
  obtain ⟨ψ', -⟩ := id hres
  have hwarp : π'.warp ≤ p := by
    rw [hres.warp_eq]
    rcases hrel with hs | hs
    · exact hs.warp_le.trans (hw₀.trans (le_max_left _ _))
    · rw [hs.warp_eq]
      exact hw₀.trans (le_max_left _ _)
  refine ⟨Z, hZ, hcZ, π', hwarp, ?_, fun hd => hstep.2 (GM20.Draw.CanBeDrawn.map ψ' hd), htrue, ?_⟩
  · have h₁ := ncard_cuffs_of_homeo (ψ'.trans e)
    rw [← π'.finite_cuffs.cast_ncard_eq, h₁]
    have : c ≤ q := by omega
    exact_mod_cast this
  · rw [hσ π'.S π.S p Z.ncard π'.isSurface π'.connected π.isSurface π.connected ⟨ψ'⟩]
    exact hred'

end GraphMinor.GM17
