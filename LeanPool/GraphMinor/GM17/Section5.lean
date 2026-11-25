/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs2

public import LeanPool.GraphMinor.GM17.Section4
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.DiscsInSurface
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors XVII, Section 5: Simplifying a Portrayal

This file formalizes Section 5 (pages 170–173) of Robertson and Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:

- Construction of the shrunken painting $\Gamma'$ (`Painting.isShrunkenFrom_of_disc`,
  `Painting.exists_isShrunkenFrom`) when shrinking an internal cell $c \in C(\Gamma)$ from a node
  $n \in \tilde{c}$.
- **(5.1)** (`theorem_5_1`, `one_le_warp_of_isZeroRedundant`, page 171): If $\pi$ is a 0-redundant
  $\mathcal{T}$-central portrayal of $G$, then for each cuff $\Theta$ of $\Sigma$, $\pi$ has warp
  $\ge 1$ at $\Theta$, and hence $\operatorname{warp}(\pi) \ge 1$.
- **(5.2)** (`Portrayal.shrinkCell`, `theorem_5_2`, page 171): Shrinking an internal cell $c$ from
  a node $n \in \tilde{c}$ when $\gamma(n) \notin V(\alpha(c))$ yields a truer portrayal $\pi'$ that
  resembles $\pi$ and preserves $\mathcal{T}$-centrality.
- **(5.3)** (`theorem_5_3`, page 172): Cutting $\Sigma$ along a $\Gamma$-normal $I$-arc $F$ with
  ends $n_1, n_2$ such that $\beta(n_1) = \beta(n_2) = F \cap \operatorname{dom}(\gamma) =
  \emptyset$
  yields a closed disc $\Delta \subseteq \Sigma$ with $F \subseteq \operatorname{bd}(\Delta)
  \subseteq
  F \cup \operatorname{bd}(\Sigma)$ and $\alpha(\Delta)$ small.
- **(5.4)** (`theorem_5_4`, page 173): Cutting $\Sigma$ along a $\Gamma$-normal $O$-arc $F$ with
  $F \cap \operatorname{dom}(\gamma) = \emptyset$ yields a closed disc $\Delta \subseteq \Sigma$
  with $\operatorname{bd}(\Delta) = F$ and $\alpha(\Delta)$ small.
The portrayal deductions that use painting results are proved in `Section5Proved`.
-/

public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

local notation "𝕀" => unitInterval

universe u v

/-! ## 1. Shrinking a Cell from a Node (Page 171) -/

/-- If $\Delta$ and $D$ are closed discs with $\Delta \subseteq D$, then every point of
$\Delta \cap \operatorname{bd}(D)$ belongs to $\operatorname{bd}(\Delta)$. -/
theorem disc_inter_discBd_subset_discBd {S : Type*} [TopologicalSpace S]
    {D Δ : Set S} (hD : IsClosedDisc D) (hΔ : IsClosedDisc Δ) (hsub : Δ ⊆ D) :
    Δ ∩ discBd D ⊆ discBd Δ := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨d1, d2⟩ := c.disc_h hsub hΔ
  have hbd_sub : discBd Δ ⊆ D := (discBd_subset Δ).trans hsub
  have hG : Nonempty (Circle ≃ₜ h '' discBd Δ) := c.oArc_h hbd_sub hΔ.isOArc_discBd
  have heq : h '' Δ = closedInner (h '' discBd Δ) := eq_closedInner_of_discBd hG d1 d2
  have hdisj : Disjoint (inner (h '' discBd Δ)) (sphere 0 1) :=
    (components_closedBall_sdiff hG (c.image_subset hbd_sub)).2.1
  rintro x ⟨hxΔ, hxbd⟩
  have hxhΔ : h x ∈ inner (h '' discBd Δ) ∪ h '' discBd Δ := by
    rw [← closedInner, ← heq]
    exact mem_image_of_mem h hxΔ
  have hxhs : h x ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem h hxbd
  rcases hxhΔ with hxin | ⟨y, hy, hyx⟩
  · exact (Set.disjoint_left.mp hdisj hxin hxhs).elim
  · have hyx' : y = x := c.gh.injOn (hbd_sub hy) (hsub hxΔ) hyx
    exact hyx' ▸ hy

/-- In the closed unit disc of $\mathbb{C}$, for any boundary point $z_0 \in S^1$ and any finite
subset $K \subseteq S^1 \setminus \{z_0\}$, there is a closed disc $Z \subseteq \overline{B}(0, 1)$
with $z_0 \notin Z$ and $K \subseteq Z$. -/
private theorem exists_shrunken_disc_complex {z₀ : ℂ} (hz₀ : z₀ ∈ sphere (0 : ℂ) 1)
    {K : Set ℂ} (hKfin : K.Finite) (hKsub : K ⊆ sphere (0 : ℂ) 1 \ {z₀}) :
    ∃ Z : Set ℂ, IsClosedDisc Z ∧ Z ⊆ closedBall (0 : ℂ) 1 ∧ z₀ ∉ Z ∧ K ⊆ Z := by
  let t₀ : Circle := ⟨z₀, hz₀⟩
  have hex_ε : ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ K, ε ≤ dist w z₀ := by
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨1, one_pos, fun _ hw => hw.elim⟩
    · obtain ⟨w₀, hw₀K, hmin⟩ :=
        Finset.exists_min_image hKfin.toFinset (fun w => dist w z₀) (hKfin.toFinset_nonempty.mpr
          hKne)
      rw [Finite.mem_toFinset] at hw₀K
      have hw₀_ne : w₀ ≠ z₀ := (hKsub hw₀K).2
      exact ⟨dist w₀ z₀, dist_pos.mpr hw₀_ne, fun w hw => hmin w (hKfin.mem_toFinset.mpr hw)⟩
  obtain ⟨ε, hεpos, hεK⟩ := hex_ε
  set η : ℝ := min (ε / 2) 1 with hη_def
  have hηpos : 0 < η := lt_min (half_pos hεpos) one_pos
  have hηle1 : η ≤ 1 := min_le_right _ _
  have hηlt_pi : η < Real.pi := lt_of_le_of_lt hηle1 (by linarith [Real.two_le_pi])
  have hηlt_ε : η < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hεpos)
  have hgap : 0 < 2 * Real.pi - 2 * η := by linarith
  let P : ℝ → ℂ := fun θ => ((t₀ * Circle.exp θ : Circle) : ℂ)
  have hP_cont : Continuous P :=
    continuous_subtype_val.comp (continuous_const.mul Circle.exp.continuous)
  have hP_sphere : ∀ θ, P θ ∈ sphere (0 : ℂ) 1 := fun θ => (t₀ * Circle.exp θ).2
  have hP_zero : P 0 = z₀ := by
    change ((t₀ * Circle.exp 0 : Circle) : ℂ) = z₀
    rw [Circle.exp_zero, mul_one]
  have hP_dist : ∀ θ, |θ| ≤ η → dist (P θ) z₀ ≤ η := by
    intro θ hθ
    have h1 : ((t₀ * Circle.exp θ : Circle) : ℂ) - (t₀ : ℂ) =
        t₀ * (Complex.exp (Complex.I * θ) - 1) := by
      rw [Circle.coe_mul, Circle.coe_exp]
      ring_nf
    have h2 : dist (P θ) z₀ ≤ |θ| := by
      change dist ((t₀ * Circle.exp θ : Circle) : ℂ) (t₀ : ℂ) ≤ |θ|
      rw [dist_eq_norm, h1, norm_mul, Circle.norm_coe, one_mul]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    exact h2.trans hθ
  have hP_inj : ∀ θ₁ θ₂, |θ₁ - θ₂| < 2 * Real.pi → P θ₁ = P θ₂ → θ₁ = θ₂ := by
    intro θ₁ θ₂ hdiff hEq
    have h1 : t₀ * Circle.exp θ₁ = t₀ * Circle.exp θ₂ := Subtype.ext hEq
    have h2 : Circle.exp θ₁ = Circle.exp θ₂ := mul_left_cancel h1
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
    have hle : (m : ℝ) * (2 * Real.pi) = θ₁ - θ₂ := by linarith
    have habs := abs_lt.mp hdiff
    have hm1 : (m : ℝ) < 1 := by
      by_contra hc; rw [not_lt] at hc; nlinarith [Real.pi_pos]
    have hm2 : (-1 : ℝ) < m := by
      by_contra hc; rw [not_lt] at hc; nlinarith [Real.pi_pos]
    have hm3 : m < 1 := by exact_mod_cast hm1
    have hm4 : -1 < m := by exact_mod_cast hm2
    have hm0 : m = 0 := by omega
    subst hm0
    push_cast at hle
    linarith
  let c₀ : 𝕀 → ℂ := fun s => P (η + (2 * Real.pi - 2 * η) * (s : ℝ))
  have hc₀_angle : ∀ s : 𝕀, η ≤ η + (2 * Real.pi - 2 * η) * (s : ℝ) ∧
      η + (2 * Real.pi - 2 * η) * (s : ℝ) ≤ 2 * Real.pi - η := fun s => by
    constructor <;> nlinarith [s.2.1, s.2.2]
  have hc₀ : IsArcMap c₀ := by
    refine ⟨hP_cont.comp (continuous_const.add (continuous_const.mul continuous_subtype_val)),
      fun s₁ s₂ hEq => ?_⟩
    have ha₁ := hc₀_angle s₁
    have ha₂ := hc₀_angle s₂
    have hθ := hP_inj _ _ (abs_lt.mpr ⟨by linarith, by linarith⟩) hEq
    exact Subtype.ext (mul_left_cancel₀ hgap.ne' (by linarith))
  let r : 𝕀 → ℝ := fun s => 1 - (s : ℝ) * (1 - (s : ℝ))
  have hr_pos : ∀ s : 𝕀, 0 < r s := fun s => by
    have hs0 := s.2.1
    have hs1 := s.2.2
    have hsq : 0 ≤ ((s : ℝ) - 1 / 2) ^ 2 := sq_nonneg _
    dsimp [r]
    nlinarith
  have hr_le : ∀ s : 𝕀, r s ≤ 1 := fun s => by
    dsimp [r]
    nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)]
  let e : 𝕀 → ℂ := fun s => (r s : ℂ) * P (η - 2 * η * (s : ℝ))
  have he_norm : ∀ s : 𝕀, ‖e s‖ = r s := fun s => by
    simp only [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr_pos s).le,
      mem_sphere_zero_iff_norm.mp (hP_sphere _), mul_one]
  have he_angle : ∀ s : 𝕀, -η ≤ η - 2 * η * (s : ℝ) ∧ η - 2 * η * (s : ℝ) ≤ η := fun s => by
    constructor <;> nlinarith [s.2.1, s.2.2]
  have he : IsArcMap e := by
    refine ⟨(Complex.continuous_ofReal.comp (continuous_const.sub
        (continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)))).mul
        (hP_cont.comp (continuous_const.sub (continuous_const.mul continuous_subtype_val))),
      fun s₁ s₂ hEq => ?_⟩
    have hn : r s₁ = r s₂ := by rw [← he_norm s₁, ← he_norm s₂, hEq]
    have hcr : (r s₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr_pos s₁).ne'
    have hP_eq : P (η - 2 * η * (s₁ : ℝ)) = P (η - 2 * η * (s₂ : ℝ)) := by
      apply mul_left_cancel₀ hcr
      calc (r s₁ : ℂ) * P (η - 2 * η * (s₁ : ℝ)) = e s₁ := rfl
        _ = e s₂ := hEq
        _ = (r s₁ : ℂ) * P (η - 2 * η * (s₂ : ℝ)) := by simp [e, hn]
    have ha₁ := he_angle s₁
    have ha₂ := he_angle s₂
    have hθ := hP_inj _ _
      (abs_lt.mpr ⟨by linarith [ha₁.1, ha₂.2, hηlt_pi], by linarith [ha₁.2, ha₂.1, hηlt_pi]⟩) hP_eq
    have hmul : (2 * η) * (s₁ : ℝ) = (2 * η) * (s₂ : ℝ) := by linarith [hθ]
    have h2η : (2 * η : ℝ) ≠ 0 := by positivity
    exact Subtype.ext (mul_left_cancel₀ h2η hmul)
  have hc₀_0 : c₀ 0 = e 0 := by
    simp [c₀, e, r]
  have hc₀_1 : c₀ 1 = e 1 := by
    simp only [c₀, e, r, Icc.coe_one, mul_one, sub_self, mul_zero, sub_zero, Complex.ofReal_one,
      one_mul, P]
    congr 2
    have h2pi : η + (2 * Real.pi - 2 * η) = (η - 2 * η) + 2 * Real.pi := by ring
    rw [h2pi, Circle.exp_add, Circle.exp_two_pi, mul_one]
  have he_sphere : ∀ t : 𝕀, e t ∈ sphere (0 : ℂ) 1 → t = 0 ∨ t = 1 := by
    intro t ht
    have hn : r t = 1 := by rw [← he_norm t, mem_sphere_zero_iff_norm.mp ht]
    have hmul : (t : ℝ) * (1 - (t : ℝ)) = 0 := by dsimp [r] at hn; linarith
    rcases mul_eq_zero.mp hmul with ht0 | ht1
    · exact Or.inl (Subtype.ext ht0)
    · have h1 : (t : ℝ) = 1 := by linarith
      exact Or.inr (Subtype.ext h1)
  have hmeet : ∀ s t : 𝕀, c₀ s = e t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have het : e t ∈ sphere (0 : ℂ) 1 := hst ▸ hP_sphere _
    rcases he_sphere t het with rfl | rfl
    · exact Or.inl ⟨hc₀.2 (hst.trans hc₀_0.symm), rfl⟩
    · exact Or.inr ⟨hc₀.2 (hst.trans hc₀_1.symm), rfl⟩
  have hG : Nonempty (Circle ≃ₜ (range c₀ ∪ range e : Set ℂ)) :=
    oArc_of_two_arcs hc₀ he hc₀_0 hc₀_1 hmeet
  have hG_sub : range c₀ ∪ range e ⊆ closedBall (0 : ℂ) 1 := by
    rintro z (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact sphere_subset_closedBall (hP_sphere _)
    · exact mem_closedBall_zero_iff.mpr (by rw [he_norm]; exact hr_le t)
  obtain ⟨hZ_disc, _⟩ := isClosedDisc_closedInner hG
  have hZ_sub : closedInner (range c₀ ∪ range e) ⊆ closedBall (0 : ℂ) 1 :=
    closedInner_subset_closedBall hG hG_sub
  have hZ_disj : Disjoint (inner (range c₀ ∪ range e)) (sphere (0 : ℂ) 1) :=
    (components_closedBall_sdiff hG hG_sub).2.1
  refine ⟨closedInner (range c₀ ∪ range e), hZ_disc, hZ_sub, ?_, ?_⟩
  · rintro (hz₀_in | ⟨s, hs⟩ | ⟨t, ht⟩)
    · exact Set.disjoint_left.mp hZ_disj hz₀_in hz₀
    · have ha := hc₀_angle s
      have hEq : P (η + (2 * Real.pi - 2 * η) * (s : ℝ)) = P 0 := hs.trans hP_zero.symm
      have hθ := hP_inj _ 0 (abs_lt.mpr ⟨by linarith, by linarith⟩) hEq
      linarith
    · rcases he_sphere t (ht.symm ▸ hz₀) with rfl | rfl
      · have hEq : P η = P 0 := by simpa [e, r, hP_zero] using ht
        have hθ := hP_inj η 0 (abs_lt.mpr ⟨by linarith, by linarith⟩) hEq
        linarith
      · have hEq : P (-η) = P 0 := by
          have ht' : e 1 = z₀ := ht
          simp only [e, r, Icc.coe_one, sub_self, mul_zero, sub_zero, Complex.ofReal_one,
            one_mul, mul_one] at ht'
          rw [show η - 2 * η = -η by ring] at ht'
          exact ht'.trans hP_zero.symm
        have hθ := hP_inj (-η) 0 (abs_lt.mpr ⟨by linarith, by linarith⟩) hEq
        linarith
  · intro w hwK
    obtain ⟨hw_sphere, _⟩ := hKsub hwK
    obtain ⟨θ, hθ₁, hθ₂, hθ_eq⟩ :=
      exists_angle_near t₀ ⟨w, hw_sphere⟩ η hηpos.le hηlt_pi.le
    have hPw : P θ = w := (congrArg Subtype.val hθ_eq).symm
    have hθ_ge : η ≤ θ := by
      by_contra hlt
      rw [not_le] at hlt
      have hd : dist w z₀ ≤ η := by
        rw [← hPw]
        exact hP_dist θ (abs_le.mpr ⟨hθ₁, hlt.le⟩)
      linarith [hεK w hwK]
    refine Or.inr (Or.inl ⟨⟨(θ - η) / (2 * Real.pi - 2 * η),
      div_nonneg (sub_nonneg.mpr hθ_ge) hgap.le,
      (div_le_one hgap).mpr (by linarith)⟩, ?_⟩)
    dsimp [c₀]
    rw [mul_div_cancel₀ _ hgap.ne', add_sub_cancel, hPw]

/-- In any closed disc $D$, given a boundary point $n \in \operatorname{bd}(D)$ and a finite subset
$K \subseteq \operatorname{bd}(D) \setminus \{n\}$, there exists a closed disc $\Delta \subseteq D$
such that $n \notin \Delta$ and $K \subseteq \Delta$ (and hence $K \subseteq
\operatorname{bd}(\Delta)$). -/
theorem exists_shrunken_disc {S : Type*} [TopologicalSpace S]
    {D : Set S} (hD : IsClosedDisc D) {n : S} (hn : n ∈ discBd D)
    {K : Set S} (hKfin : K.Finite) (hKsub : K ⊆ discBd D \ {n}) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ D ∧ n ∉ Δ ∧ K ⊆ Δ ∧ K ⊆ discBd Δ := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hz₀ : h n ∈ sphere (0 : ℂ) 1 := by
    rw [← c.bd]
    exact mem_image_of_mem h hn
  have hKh_sub : h '' K ⊆ sphere (0 : ℂ) 1 \ {h n} := by
    rintro _ ⟨x, hxK, rfl⟩
    obtain ⟨hx_bd, hx_ne⟩ := hKsub hxK
    refine ⟨?_, fun hEq => hx_ne (c.gh.injOn (discBd_subset D hx_bd) (discBd_subset D hn) hEq)⟩
    rw [← c.bd]
    exact mem_image_of_mem h hx_bd
  obtain ⟨Z, hZ_disc, hZ_sub, hz₀_not, hKZ⟩ :=
    exists_shrunken_disc_complex hz₀ (hKfin.image h) hKh_sub
  obtain ⟨hΔ_disc, _⟩ := c.disc_g hZ_sub hZ_disc
  have hΔ_sub : g '' Z ⊆ D := c.g_subset hZ_sub
  have hn_not : n ∉ g '' Z := by
    rintro ⟨z, hzZ, hgz⟩
    have hzh : z = h n := by
      rw [← hgz, c.hg (hZ_sub hzZ)]
    exact hz₀_not (hzh ▸ hzZ)
  have hK_sub_Δ : K ⊆ g '' Z := by
    intro x hxK
    have hxD : x ∈ D := discBd_subset D (hKsub hxK).1
    exact ⟨h x, hKZ (mem_image_of_mem h hxK), c.gh hxD⟩
  have hK_bd : K ⊆ discBd (g '' Z) := fun x hxK =>
    disc_inter_discBd_subset_discBd hD hΔ_disc hΔ_sub ⟨hK_sub_Δ hxK, (hKsub hxK).1⟩
  exact ⟨g '' Z, hΔ_disc, hΔ_sub, hn_not, hK_sub_Δ, hK_bd⟩

/-- Given a painting $\Gamma$ in a Hausdorff space $S$, an internal cell $c \in C(\Gamma)$,
a node $n \in \tilde{c}$, and a closed disc $\Delta \subseteq \bar{c}$ with $n \notin \Delta$ and
$\tilde{c} \setminus \{n\} \subseteq \Delta$, the set $U' = (U(\Gamma) \setminus c) \cup \Delta$
with node set $N' = N(\Gamma)$ forms a painting $\Gamma'$ in $S$ obtained from $\Gamma$ by
shrinking $c$ from $n$.
Graph Minors XVII, Section 5 (page 171). -/
theorem Painting.isShrunkenFrom_of_disc {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c : Set S} (hc : Γ.IsInternalCell c) {n : S} (hn : n ∈ tilde c)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hΔ_sub : Δ ⊆ closure c)
    (hnΔ : n ∉ Δ) (htilde_sub : tilde c \ {n} ⊆ Δ) :
    ∃ Γ' : Painting S, Γ.IsShrunkenFrom Γ' c n Δ := by
  have hcC : c ∈ Γ.C := hc.1
  have hD : IsClosedDisc (closure c) := Γ.isClosedDisc_closure_cell hcC
  have htilde_bdD : tilde c \ {n} ⊆ discBd (closure c) :=
    sdiff_subset.trans (Γ.tilde_subset_discBd hcC)
  have htilde_bdΔ : tilde c \ {n} ⊆ discBd Δ := fun x hx =>
    disc_inter_discBd_subset_discBd hD hΔ hΔ_sub ⟨htilde_sub hx, htilde_bdD hx⟩
  have htilde_fin : (tilde c \ {n}).Finite :=
    (Γ.finite_tilde_cell hcC).subset sdiff_subset
  set c' : Set S := Δ \ (tilde c \ {n})
  have hc'_diff_fin : (Δ \ c').Finite := by
    refine htilde_fin.subset fun x hx => ?_
    simp only [c', mem_sdiff] at hx
    by_contra hnot
    exact hx.2 ⟨hx.1, hnot⟩
  have hc'_path : IsPathConnected c' :=
    isPathConnected_of_isClosedDisc_finite_diff hΔ sdiff_subset hc'_diff_fin
  have hcl_c' : closure c' = Δ :=
    closure_eq_of_isClosedDisc_finite_diff hΔ sdiff_subset hc'_diff_fin
  have htilde_c' : tilde c' = tilde c \ {n} := by
    rw [tilde_diff_eq_of_isClosedDisc_finite hΔ htilde_fin, inter_eq_right.mpr htilde_sub]
  have hcl_c_diff : closure c \ Γ.N = c := Γ.closure_cell_diff_N hcC
  have hcl_c_inter : closure c ∩ Γ.N = tilde c := Γ.closure_cell_inter_N hcC
  have hΔ_inter_N : Δ ∩ Γ.N = tilde c \ {n} := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxΔ, hxN⟩
      have hxt : x ∈ tilde c := by
        rw [← hcl_c_inter]
        exact ⟨hΔ_sub hxΔ, hxN⟩
      exact ⟨hxt, fun hxn => hnΔ (mem_singleton_iff.mp hxn ▸ hxΔ)⟩
    · intro x hx
      exact ⟨htilde_sub hx, Γ.tilde_subset_N hcC hx.1⟩
  have hc'_eq : Δ \ Γ.N = c' := by
    ext x
    simp only [c', ← hΔ_inter_N, mem_sdiff, mem_inter_iff]
    tauto
  set F : Set S := ((Γ.U \ c) ∪ Δ) \ Γ.N
  have hcov : ⋃₀ ((Γ.C \ {c}) ∪ {c'}) = F := by
    ext x
    simp only [F, mem_sUnion, mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨d, ⟨hdC, hdc⟩ | rfl, hxd⟩
      · have hxUN : x ∈ Γ.U \ Γ.N := Γ.cell_subset_diff hdC hxd
        have hxc : x ∉ c := fun hxc => hdc (Γ.cell_eq_of_mem hdC hcC hxd hxc)
        exact ⟨Or.inl ⟨hxUN.1, hxc⟩, hxUN.2⟩
      · have hxΔN : x ∈ Δ \ Γ.N := by rwa [hc'_eq]
        exact ⟨Or.inr hxΔN.1, hxΔN.2⟩
    · rintro ⟨⟨hxU, hxc⟩ | hxΔ, hxN⟩
      · have hxUN : x ∈ Γ.U \ Γ.N := ⟨hxU, hxN⟩
        rw [← Γ.sUnion_cells, mem_sUnion] at hxUN
        obtain ⟨d, hdC, hxd⟩ := hxUN
        have hdc : d ≠ c := fun hEq => hxc (hEq ▸ hxd)
        exact ⟨d, Or.inl ⟨hdC, hdc⟩, hxd⟩
      · have hxc' : x ∈ c' := by rw [← hc'_eq]; exact ⟨hxΔ, hxN⟩
        exact ⟨c', Or.inr rfl, hxc'⟩
  have hC'_fin : ((Γ.C \ {c}) ∪ {c'}).Finite :=
    (Γ.finite_cells.subset sdiff_subset).union (finite_singleton c')
  have hC'_ne : ∀ d ∈ (Γ.C \ {c}) ∪ {c'}, d.Nonempty := by
    rintro d (⟨hdC, _⟩ | rfl)
    · exact Γ.cell_nonempty hdC
    · exact hc'_path.nonempty
  have hC'_path : ∀ d ∈ (Γ.C \ {c}) ∪ {c'}, IsPathConnected d := by
    rintro d (⟨hdC, _⟩ | rfl)
    · exact Γ.cell_isPathConnected hdC
    · exact hc'_path
  have hC'_disj : ∀ d₁ ∈ (Γ.C \ {c}) ∪ {c'}, ∀ d₂ ∈ (Γ.C \ {c}) ∪ {c'},
      d₁ ≠ d₂ → Disjoint d₁ d₂ := by
    rintro d₁ (⟨hd₁C, hd₁c⟩ | rfl) d₂ (⟨hd₂C, hd₂c⟩ | rfl) hne
    · exact Γ.cell_disjoint hd₁C hd₂C hne
    · refine Set.disjoint_left.mpr fun x hxd₁ hxc' => ?_
      have hx_inter : x ∈ closure d₁ ∩ closure c := ⟨subset_closure hxd₁, hΔ_sub hxc'.1⟩
      rw [Γ.closure_cell_inter_closure_cell hd₁C hcC hd₁c] at hx_inter
      exact (Γ.cell_subset_diff hd₁C hxd₁).2 (Γ.tilde_subset_N hd₁C hx_inter.1)
    · refine Set.disjoint_left.mpr fun x hxc' hxd₂ => ?_
      have hx_inter : x ∈ closure c ∩ closure d₂ := ⟨hΔ_sub hxc'.1, subset_closure hxd₂⟩
      rw [Γ.closure_cell_inter_closure_cell hcC hd₂C (Ne.symm hd₂c)] at hx_inter
      exact (Γ.cell_subset_diff hd₂C hxd₂).2 (Γ.tilde_subset_N hd₂C hx_inter.2)
    · exact (hne rfl).elim
  have hC'_closed : ∀ d ∈ (Γ.C \ {c}) ∪ {c'}, closure d ∩ F = d := by
    rintro d (⟨hdC, hdc⟩ | rfl)
    · refine Subset.antisymm ?_ fun x hxd => ⟨subset_closure hxd, ?_⟩
      · rintro x ⟨hxd_cl, -, hxN⟩
        rw [← Γ.closure_cell_diff_N hdC]
        exact ⟨hxd_cl, hxN⟩
      · rw [← hcov]
        exact mem_sUnion.mpr ⟨d, Or.inl ⟨hdC, hdc⟩, hxd⟩
    · refine Subset.antisymm ?_ fun x hxc' => ⟨subset_closure hxc', ?_⟩
      · rintro x ⟨hxc'_cl, -, hxN⟩
        rw [hcl_c'] at hxc'_cl
        rw [← hc'_eq]
        exact ⟨hxc'_cl, hxN⟩
      · rw [← hcov]
        exact mem_sUnion.mpr ⟨c', Or.inr rfl, hxc'⟩
  have hC'_eq : arcComponentsIn F = (Γ.C \ {c}) ∪ {c'} :=
    arcComponentsIn_eq_of_finite_cover hC'_fin hcov hC'_ne hC'_path hC'_disj hC'_closed
  have hU'_closed : IsClosed ((Γ.U \ c) ∪ Δ) := by
    have hU'_eq : (Γ.U \ c) ∪ Δ = Γ.N ∪ ⋃ d ∈ (Γ.C \ {c}) ∪ {c'}, closure d := by
      ext x
      simp only [mem_union, mem_sdiff, mem_iUnion, mem_singleton_iff]
      constructor
      · rintro (⟨hxU, hxc⟩ | hxΔ)
        · by_cases hxN : x ∈ Γ.N
          · exact Or.inl hxN
          · have hxF : x ∈ F := ⟨Or.inl ⟨hxU, hxc⟩, hxN⟩
            rw [← hcov, mem_sUnion] at hxF
            obtain ⟨d, hd, hxd⟩ := hxF
            exact Or.inr ⟨d, hd, subset_closure hxd⟩
        · rw [← hcl_c'] at hxΔ
          exact Or.inr ⟨c', Or.inr rfl, hxΔ⟩
      · rintro (hxN | ⟨d, ⟨hdC, hdc⟩ | rfl, hxd⟩)
        · exact Or.inl ⟨Γ.N_subset hxN, fun hxc => (Γ.cell_subset_diff hcC hxc).2 hxN⟩
        · by_cases hxc : x ∈ c
          · exfalso
            have hx_inter : x ∈ closure d ∩ closure c := ⟨hxd, subset_closure hxc⟩
            rw [Γ.closure_cell_inter_closure_cell hdC hcC hdc] at hx_inter
            exact (Γ.cell_subset_diff hcC hxc).2 (Γ.tilde_subset_N hcC hx_inter.2)
          · exact Or.inl ⟨Γ.closure_cell_subset_U hdC hxd, hxc⟩
        · rw [hcl_c'] at hxd
          exact Or.inr hxd
    rw [hU'_eq]
    exact Γ.finite_N.isClosed.union (hC'_fin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hc'_bd : ¬ (c' ∩ bd S).Nonempty := by
    rintro ⟨x, hxc', hxbd⟩
    have hx_cl_bd : x ∈ closure c ∩ bd S := ⟨hΔ_sub hxc'.1, hxbd⟩
    have hxN : x ∈ Γ.N := by
      by_contra hxN
      have hxc : x ∈ c := by
        rw [← hcl_c_diff]
        exact ⟨hx_cl_bd.1, hxN⟩
      exact hc.2 ⟨x, hxc, hxbd⟩
    have hxΔ : x ∈ Δ \ Γ.N := by rwa [hc'_eq]
    exact hxΔ.2 hxN
  let Γ' : Painting S :=
    { U := (Γ.U \ c) ∪ Δ
      N := Γ.N
      isClosed_U := hU'_closed
      N_subset := fun x hxN =>
        Or.inl ⟨Γ.N_subset hxN, fun hxc => (Γ.cell_subset_diff hcC hxc).2 hxN⟩
      finite_N := Γ.finite_N
      finite_cells := by rw [hC'_eq]; exact hC'_fin
      cell_disc := by
        intro d hd
        rw [hC'_eq] at hd
        rcases hd with ⟨hdC, _⟩ | rfl
        · exact Γ.cell_disc d hdC
        · refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hcl_c']
            exact hΔ
          · rw [hcl_c', htilde_c']
            exact htilde_bdΔ
          · rw [htilde_c']
            exact htilde_fin
          · rw [htilde_c']
            exact Nat.le_trans (ncard_le_ncard sdiff_subset (Γ.finite_tilde_cell hcC))
              (Γ.ncard_tilde_cell_le hcC)
      bd_subset := fun x hxbd =>
        Or.inl ⟨Γ.bd_subset hxbd, fun hxc => hc.2 ⟨x, hxc, hxbd⟩⟩
      border_cell := by
        intro d hd hdbd
        rw [hC'_eq] at hd
        rcases hd with ⟨hdC, _⟩ | rfl
        · exact Γ.border_cell d hdC hdbd
        · exact (hc'_bd hdbd).elim }
  have hΓ'C : Γ'.C = (Γ.C \ {c}) ∪ {c'} := hC'_eq
  refine ⟨Γ', hc, hn, hΔ, hΔ_sub, hnΔ, htilde_sub, rfl, rfl, ?_, hc'_bd, htilde_c', hΓ'C⟩
  rw [hΓ'C]
  exact Or.inr rfl

/-- Given a painting $\Gamma$ in a Hausdorff space $S$, an internal cell $c \in C(\Gamma)$, and a
node $n \in \tilde{c}$, there exist a closed disc $\Delta \subseteq \bar{c}$ and a painting
$\Gamma'$ in $S$ obtained from $\Gamma$ by shrinking $c$ from $n$.
Graph Minors XVII, Section 5 (page 171). -/
theorem Painting.exists_isShrunkenFrom {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c : Set S} (hc : Γ.IsInternalCell c) {n : S} (hn : n ∈ tilde c) :
    ∃ (Δ : Set S) (Γ' : Painting S), Γ.IsShrunkenFrom Γ' c n Δ := by
  have hcC : c ∈ Γ.C := hc.1
  have hD : IsClosedDisc (closure c) := Γ.isClosedDisc_closure_cell hcC
  have hn_bd : n ∈ discBd (closure c) := Γ.tilde_subset_discBd hcC hn
  have hK_fin : (tilde c \ {n}).Finite :=
    (Γ.finite_tilde_cell hcC).subset sdiff_subset
  have hK_sub : tilde c \ {n} ⊆ discBd (closure c) \ {n} :=
    fun _ hx => ⟨Γ.tilde_subset_discBd hcC hx.1, hx.2⟩
  obtain ⟨Δ, hΔ, hΔ_sub, hnΔ, hK_Δ, -⟩ := exists_shrunken_disc hD hn_bd hK_fin hK_sub
  obtain ⟨Γ', hsh⟩ := Γ.isShrunkenFrom_of_disc hc hn hΔ hΔ_sub hnΔ hK_Δ
  exact ⟨Δ, Γ', hsh⟩

/-! ## 2. Shrinking a Cell in a Portrayal: (5.2) (Page 171) -/

private theorem shrunk_cell_not_mem_old {S : Type} [TopologicalSpace S]
    {Γ Γ' : Painting S} {c₀ : Set S} {n : S} {Δ : Set S}
    (hsh : Γ.IsShrunkenFrom Γ' c₀ n Δ) :
    Δ \ (tilde c₀ \ {n}) ∉ Γ.C \ {c₀} := by
  let c' : Set S := Δ \ (tilde c₀ \ {n})
  have hc₀C : c₀ ∈ Γ.C := hsh.1.1
  have hc'C : c' ∈ Γ'.C := hsh.2.2.2.2.2.2.2.2.1
  rintro ⟨hc'Γ, hc'ne⟩
  obtain ⟨x, hxc'⟩ := Γ'.cell_nonempty hc'C
  have hx_inter : x ∈ closure c' ∩ closure c₀ := ⟨subset_closure hxc', hsh.2.2.2.1 hxc'.1⟩
  rw [Γ.closure_cell_inter_closure_cell hc'Γ hc₀C hc'ne] at hx_inter
  exact (Γ.cell_subset_diff hc'Γ hxc').2 (Γ.tilde_subset_N hc'Γ hx_inter.1)

private theorem shrunk_cell_cases {S : Type} [TopologicalSpace S]
    {Γ Γ' : Painting S} {c₀ : Set S} {n : S} {Δ : Set S}
    (hsh : Γ.IsShrunkenFrom Γ' c₀ n Δ) {d : Set S} (hd : d ∈ Γ'.C) :
    (d ∈ Γ.C \ {c₀} ∧ d ≠ Δ \ (tilde c₀ \ {n})) ∨ d = Δ \ (tilde c₀ \ {n}) := by
  rw [hsh.2.2.2.2.2.2.2.2.2.2.2] at hd
  rcases hd with hd | rfl
  · exact Or.inl ⟨hd, fun hEq => shrunk_cell_not_mem_old hsh (hEq ▸ hd)⟩
  · exact Or.inr rfl

/-- Given a portrayal $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G$, an internal cell
$c_0 \in C(\Gamma)$, a node $n \in \tilde{c}_0$ such that
$n \in \operatorname{dom}(\gamma) \implies \gamma(n) \notin V(\alpha(c_0))$, and a painting
$\Gamma'$ obtained from $\Gamma$ by shrinking $c_0$ from $n$ using $\Delta$, the portrayal
$\pi' = (\Sigma, \Gamma', \alpha', \beta, \gamma)$ obtained from $\pi$ by shrinking $c_0$ from $n$,
where $\alpha'(c') = \alpha(c_0)$ for $c' = \Delta \setminus (\tilde{c}_0 \setminus \{n\})$ and
$\alpha'(c) = \alpha(c)$ for $c \in C(\Gamma) \setminus \{c_0\}$.
Graph Minors XVII, Section 5 (page 171). -/
@[expose]
noncomputable def Portrayal.shrinkCell {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ : Set π.S)
    (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    Portrayal G where
  S := π.S
  top := π.top
  isSurface := π.isSurface
  connected := π.connected
  Γ := Γ'
  cellGraph := open Classical in fun d =>
    if d = Δ \ (tilde c₀ \ {n}) then π.cellGraph c₀ else π.cellGraph d
  borderSet := π.borderSet
  domγ := π.domγ
  nodeVertex := π.nodeVertex
  cellGraph_le := by
    classical
    intro d hd
    by_cases hEq : d = Δ \ (tilde c₀ \ {n})
    · rw [ite_eq_left hEq]
      exact π.cellGraph_le c₀ hsh.1.1
    · rw [ite_eq_right hEq]
      rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, _⟩ | rfl
      · exact π.cellGraph_le d hdC
      · exact (hEq rfl).elim
  borderSet_subset := by
    rw [hsh.2.2.2.2.2.2.2.1]
    exact π.borderSet_subset
  domγ_subset := by
    rw [hsh.2.2.2.2.2.2.2.1]
    exact π.domγ_subset
  nodeVertex_mem := π.nodeVertex_mem
  nodeVertex_injOn := π.nodeVertex_injOn
  p1_vertex := by
    classical
    intro v hv
    obtain ⟨d₀, hd₀C, hvd₀⟩ := π.p1_vertex v hv
    by_cases hd₀ : d₀ = c₀
    · subst hd₀
      exact ⟨Δ \ (tilde d₀ \ {n}), hsh.2.2.2.2.2.2.2.2.1, by rwa [ite_eq_left rfl]⟩
    · have hne : d₀ ≠ Δ \ (tilde c₀ \ {n}) :=
        fun hEq => shrunk_cell_not_mem_old hsh (hEq ▸ ⟨hd₀C, hd₀⟩)
      refine ⟨d₀, ?_, ?_⟩
      · rw [hsh.2.2.2.2.2.2.2.2.2.2.2]; exact Or.inl ⟨hd₀C, hd₀⟩
      · rwa [ite_eq_right hne]
  p1_edge := by
    classical
    intro e he
    obtain ⟨d₀, hd₀C, hed₀⟩ := π.p1_edge e he
    by_cases hd₀ : d₀ = c₀
    · subst hd₀
      exact ⟨Δ \ (tilde d₀ \ {n}), hsh.2.2.2.2.2.2.2.2.1, by rwa [ite_eq_left rfl]⟩
    · have hne : d₀ ≠ Δ \ (tilde c₀ \ {n}) :=
        fun hEq => shrunk_cell_not_mem_old hsh (hEq ▸ ⟨hd₀C, hd₀⟩)
      refine ⟨d₀, ?_, ?_⟩
      · rw [hsh.2.2.2.2.2.2.2.2.2.2.2]; exact Or.inl ⟨hd₀C, hd₀⟩
      · rwa [ite_eq_right hne]
  p1_disjoint := by
    classical
    intro d₁ hd₁ d₂ hd₂ hne
    rcases shrunk_cell_cases hsh hd₁ with ⟨⟨hd₁C, hd₁c₀⟩, hd₁c'⟩ | rfl <;>
      rcases shrunk_cell_cases hsh hd₂ with ⟨⟨hd₂C, hd₂c₀⟩, hd₂c'⟩ | rfl
    · rw [ite_eq_right hd₁c', ite_eq_right hd₂c']
      exact π.p1_disjoint d₁ hd₁C d₂ hd₂C hne
    · rw [ite_eq_right hd₁c', ite_eq_left rfl]
      exact π.p1_disjoint d₁ hd₁C c₀ hsh.1.1 hd₁c₀
    · rw [ite_eq_left rfl, ite_eq_right hd₂c']
      exact π.p1_disjoint c₀ hsh.1.1 d₂ hd₂C (Ne.symm hd₂c₀)
    · exact (hne rfl).elim
  p2 := by
    classical
    intro d hd m hm
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
    · rw [ite_eq_right hdc']
      exact π.p2 d hdC m hm
    · rw [ite_eq_left rfl]
      rw [hsh.2.2.2.2.2.2.2.2.2.2.1] at hm
      exact π.p2 c₀ hsh.1.1 m ⟨hm.1.1, hm.2⟩
  p3_notMem := π.p3_notMem
  p3_subset := by
    classical
    intro d hd hdbd m hm
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
    · rw [ite_eq_right hdc']
      exact π.p3_subset d hdC hdbd m hm
    · exact (hsh.2.2.2.2.2.2.2.2.2.1 hdbd).elim
  p4_disjoint := by
    rw [hsh.2.2.2.2.2.2.2.1]
    exact π.p4_disjoint
  p4_notMem := by
    rw [hsh.2.2.2.2.2.2.2.1]
    exact π.p4_notMem
  p5 := by
    classical
    intro d hd hdbd v hv ⟨d₂, hd₂, hd₂_ne, hv₂⟩
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, hdc₀⟩, hdc'⟩ | rfl
    · rw [ite_eq_right hdc'] at hv
      rcases shrunk_cell_cases hsh hd₂ with ⟨⟨hd₂C, _⟩, hd₂c'⟩ | rfl
      · rw [ite_eq_right hd₂c'] at hv₂
        exact π.p5 d hdC hdbd v hv ⟨d₂, hd₂C, hd₂_ne, hv₂⟩
      · rw [ite_eq_left rfl] at hv₂
        exact π.p5 d hdC hdbd v hv ⟨c₀, hsh.1.1, Ne.symm hdc₀, hv₂⟩
    · rw [ite_eq_left rfl] at hv
      rcases shrunk_cell_cases hsh hd₂ with ⟨⟨hd₂C, hd₂c₀⟩, hd₂c'⟩ | rfl
      · rw [ite_eq_right hd₂c'] at hv₂
        obtain ⟨m, ⟨hm_tilde, hm_γ⟩, rfl⟩ :=
          π.p5 c₀ hsh.1.1 hsh.1.2 v hv ⟨d₂, hd₂C, hd₂c₀, hv₂⟩
        have hmn : m ≠ n := fun hEq => hn_γ (hEq ▸ hm_γ) (hEq ▸ hv)
        rw [hsh.2.2.2.2.2.2.2.2.2.2.1]
        exact ⟨m, ⟨⟨hm_tilde, hmn⟩, hm_γ⟩, rfl⟩
      · exact (hd₂_ne rfl).elim
  p6 := by
    classical
    intro d hd hdbd v hv ⟨d₂, hd₂, hd₂_ne, hv₂⟩
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, hdc₀⟩, hdc'⟩ | rfl
    · rw [ite_eq_right hdc'] at hv
      rcases shrunk_cell_cases hsh hd₂ with ⟨⟨hd₂C, _⟩, hd₂c'⟩ | rfl
      · rw [ite_eq_right hd₂c'] at hv₂
        exact π.p6 d hdC hdbd v hv ⟨d₂, hd₂C, hd₂_ne, hv₂⟩
      · rw [ite_eq_left rfl] at hv₂
        exact π.p6 d hdC hdbd v hv ⟨c₀, hsh.1.1, Ne.symm hdc₀, hv₂⟩
    · exact (hsh.2.2.2.2.2.2.2.2.2.1 hdbd).elim
  p7 := by
    rw [hsh.2.2.2.2.2.2.2.1]
    exact π.p7

/-- Shrinking an internal cell preserves $\mathcal{T}$-centrality.
Graph Minors XVII, (5.2) (page 171). -/
theorem Portrayal.shrinkCell_isCentral {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G) (hT : π.IsCentral 𝒯)
    (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ : Set π.S)
    (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    (π.shrinkCell Γ' c₀ n Δ hsh hn_γ).IsCentral 𝒯 := by
  classical
  dsimp only [Portrayal.IsCentral, Portrayal.shrinkCell]
  intro d hd
  rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
  · rw [ite_eq_right hdc']
    exact hT d hdC
  · rw [ite_eq_left rfl]
    exact hT c₀ hsh.1.1

/-- Shrinking an internal cell produces a portrayal that resembles $\pi$.
Graph Minors XVII, (5.2) (page 171). -/
theorem Portrayal.shrinkCell_resembles {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ : Set π.S)
    (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    (π.shrinkCell Γ' c₀ n Δ hsh hn_γ).Resembles π := by
  classical
  let c' : Set π.S := Δ \ (tilde c₀ \ {n})
  have hc₀_bd : ¬ (c₀ ∩ bd π.S).Nonempty := hsh.1.2
  have hc'_bd : ¬ (c' ∩ bd π.S).Nonempty := hsh.2.2.2.2.2.2.2.2.2.1
  have hΓ'C : Γ'.C = (π.Γ.C \ {c₀}) ∪ {c'} := hsh.2.2.2.2.2.2.2.2.2.2.2
  dsimp only [Portrayal.Resembles, Portrayal.warpAt, Portrayal.cellWarp, Portrayal.CellWarpLE,
    Portrayal.borderPlus, Portrayal.shrinkCell]
  refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
  have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
  rw [himg]
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  congr 1
  ext p
  constructor
  · rintro ⟨d, hd, hdΘ, rfl⟩
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
    · refine ⟨d, hdC, hdΘ, ?_⟩
      congr 1
      ext q
      rw [ite_eq_right hdc']
    · exact (hc'_bd (hdΘ.mono (inter_subset_inter_right _ hΘ_bd))).elim
  · rintro ⟨d, hdC, hdΘ, rfl⟩
    have hdc₀ : d ≠ c₀ := fun hEq => hc₀_bd ((hEq ▸ hdΘ).mono (inter_subset_inter_right _ hΘ_bd))
    have hdc' : d ≠ c' := by rintro rfl; exact shrunk_cell_not_mem_old hsh ⟨hdC, hdc₀⟩
    refine ⟨d, ?_, hdΘ, ?_⟩
    · rw [hΓ'C]
      exact Or.inl ⟨hdC, hdc₀⟩
    · congr 1
      ext q
      rw [ite_eq_right hdc']

/-- Shrinking an internal cell produces a portrayal that is strictly truer than $\pi$.
Graph Minors XVII, Section 8 (page 182) and (5.2) (page 171). -/
theorem Portrayal.shrinkCell_isTruer {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ : Set π.S)
    (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    (π.shrinkCell Γ' c₀ n Δ hsh hn_γ).IsTruer π := by
  classical
  let c' : Set π.S := Δ \ (tilde c₀ \ {n})
  have hc₀C : c₀ ∈ π.Γ.C := hsh.1.1
  have hc₀_bd : ¬ (c₀ ∩ bd π.S).Nonempty := hsh.1.2
  have hn_tilde : n ∈ tilde c₀ := hsh.2.1
  have hc'_bd : ¬ (c' ∩ bd π.S).Nonempty := hsh.2.2.2.2.2.2.2.2.2.1
  have htilde_c' : tilde c' = tilde c₀ \ {n} := hsh.2.2.2.2.2.2.2.2.2.2.1
  have hΓ'C : Γ'.C = (π.Γ.C \ {c₀}) ∪ {c'} := hsh.2.2.2.2.2.2.2.2.2.2.2
  set q := (tilde c₀).ncard with hq_def
  have hq_le : q ≤ 3 := π.Γ.ncard_tilde_cell_le hc₀C
  have hq_pos : 1 ≤ q :=
    (ncard_pos (π.Γ.finite_tilde_cell hc₀C)).mpr ⟨n, hn_tilde⟩
  have hncard_c' : (tilde c').ncard = q - 1 := by
    rw [htilde_c', ncard_sdiff_singleton_of_mem hn_tilde]
  let k : Fin 6 := ⟨3 - q, by omega⟩
  have hk_val : k.1 = 3 - q := rfl
  dsimp only [Portrayal.IsTruer, Portrayal.truth, Portrayal.shrinkCell]
  refine ⟨k, fun i hik => ?_, ?_⟩
  · have hik_val : i.1 < 3 - q := hik
    have hi4 : i.1 < 4 := by omega
    have hqi : q < 3 - i.1 := by omega
    rw [ite_eq_left hi4, ite_eq_left hi4]
    congr 1
    ext d
    simp only [mem_sep_iff, hΓ'C, mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨⟨hdC, _⟩ | rfl, hdbd, hdq⟩)
      · exact ⟨hdC, hdbd, hdq⟩
      · omega
    · rintro ⟨hdC, hdbd, hdq⟩
      have hdc₀ : d ≠ c₀ := by
        rintro rfl
        rw [← hq_def] at hdq
        omega
      exact ⟨Or.inl ⟨hdC, hdc₀⟩, hdbd, hdq⟩
  · have hk4 : k.1 < 4 := by omega
    have hqk : 3 - k.1 = q := by omega
    rw [ite_eq_left hk4, ite_eq_left hk4, hqk]
    set S_old := {d ∈ π.Γ.C | ¬ (d ∩ bd π.S).Nonempty ∧ (tilde d).ncard = q}
    set S_new := {d ∈ Γ'.C | ¬ (d ∩ bd π.S).Nonempty ∧ (tilde d).ncard = q}
    have hEq : S_new = S_old \ {c₀} := by
      ext d
      simp only [S_new, S_old, mem_sep_iff, hΓ'C, mem_union, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro (⟨⟨hdC, hdc₀⟩ | rfl, hdbd, hdq⟩)
        · exact ⟨⟨hdC, hdbd, hdq⟩, hdc₀⟩
        · omega
      · rintro ⟨⟨hdC, hdbd, hdq⟩, hdc₀⟩
        exact ⟨Or.inl ⟨hdC, hdc₀⟩, hdbd, hdq⟩
    have hc₀_mem : c₀ ∈ S_old := ⟨hc₀C, hc₀_bd, rfl⟩
    have hS_old_fin : S_old.Finite := π.Γ.finite_cells.subset fun _ h => h.1
    rw [hEq, ncard_sdiff_singleton_of_mem hc₀_mem]
    have hpos : 0 < S_old.ncard := (ncard_pos hS_old_fin).mpr ⟨c₀, hc₀_mem⟩
    omega

/-- **Graph Minors XVII, (5.2)** (page 171):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a hypergraph $G$. Let $c \in C(\Gamma)$ be
internal, and let $n \in \tilde{c} - \operatorname{dom}(\gamma)$. Let $\Gamma'$ be obtained by
shrinking $c$ from $n$; and let $\alpha'$ be defined by $\alpha'(c') = \alpha(c)$, where $c'$ is
the shrunken $c$, and otherwise $\alpha' = \alpha$. Then $\pi' = (\Sigma, \Gamma', \alpha', \beta,
\gamma)$ is a portrayal of $G$." (The paper omits "portrayal of a" before "hypergraph $G$".)

Moreover, if $\pi$ is $\mathcal{T}$-central, then $\pi'$ is $\mathcal{T}$-central, resembles $\pi$,
and is truer than $\pi$ (holding more generally whenever
$n \in \operatorname{dom}(\gamma) \implies \gamma(n) \notin V(\alpha(c))$). -/
theorem theorem_5_2_proof {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) [T2Space π.S]
    {c₀ : Set π.S} (hc₀ : π.Γ.IsInternalCell c₀) {n : π.S} (hn : n ∈ tilde c₀)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet) :
    ∃ (Δ : Set π.S) (Γ' : Painting π.S) (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ),
      let π' := π.shrinkCell Γ' c₀ n Δ hsh hn_γ
      (∀ 𝒯, π.IsCentral 𝒯 → π'.IsCentral 𝒯) ∧ π'.Resembles π ∧ π'.IsTruer π := by
  obtain ⟨Δ, Γ', hsh⟩ := π.Γ.exists_isShrunkenFrom hc₀ hn
  exact ⟨Δ, Γ', hsh, fun _ hT => π.shrinkCell_isCentral hT Γ' c₀ n Δ hsh hn_γ,
    π.shrinkCell_resembles Γ' c₀ n Δ hsh hn_γ,
    π.shrinkCell_isTruer Γ' c₀ n Δ hsh hn_γ⟩

/-! ## 3. Positive Warp at Cuffs of 0-Redundant Portrayals: (5.1) (Page 171) -/

/-- If a portrayal $\pi$ has warp $0$ at a cuff $\Theta \in \text{cuffs}(\Sigma)$, then
$\beta(n) = \emptyset$ for every node $n \in N(\Gamma) \cap \Theta$, and consequently every cell
$c \in C(\Gamma)$ bordering $\Theta$ satisfies the internal-cell condition **(P5)**:
$V(\alpha(c) \cap \alpha(-c)) \subseteq \gamma(\tilde{c} \cap \operatorname{dom}(\gamma))$.
Graph Minors XVII, proof of (5.1) (page 171). -/
theorem Portrayal.borderSet_eq_empty_of_warpAt_eq_zero
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    (hwarp : π.warpAt Θ = 0) :
    (∀ n ∈ π.Γ.N ∩ Θ, π.borderSet n = ∅) ∧
    (∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → ∀ v ∈ (π.cellGraph c).vertexSet,
      (∃ c' ∈ π.Γ.C, c' ≠ c ∧ v ∈ (π.cellGraph c').vertexSet) →
      v ∈ π.nodeVertex '' (tilde c ∩ π.domγ)) := by
  have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hβ : ∀ n ∈ π.Γ.N ∩ Θ, π.borderSet n = ∅ := by
    intro n hn
    have hle : (π.borderSet n).ncard ≤ 0 := hwarp ▸ π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn
    have hfin : (π.borderSet n).Finite := by
      have hΘ_bd : Θ ⊆ bd π.S := by
        rcases hΘ with ⟨x₀, _, rfl⟩
        exact connectedComponentIn_subset (bd π.S) x₀
      exact G.vertexSet_finite.subset (π.borderSet_subset n ⟨hn.1, hΘ_bd hn.2⟩)
    exact (ncard_eq_zero hfin).mp (Nat.eq_zero_of_le_zero hle)
  refine ⟨hβ, fun c hc hinter v hv hex => ?_⟩
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hcbd : (c ∩ bd π.S).Nonempty := hinter.mono (inter_subset_inter_right c hΘ_bd)
  have htilde_Θ : tilde c ⊆ π.Γ.N ∩ Θ :=
    (π.Γ.border_cell_subset_cuff hc hΘ hinter).2.2.2.1
  obtain ⟨n, hn_tilde, hvn | ⟨hn_γ, rfl⟩⟩ := π.p6 c hc hcbd v hv hex
  · rw [hβ n (htilde_Θ hn_tilde)] at hvn
    exact hvn.elim
  · exact ⟨n, ⟨hn_tilde, hn_γ⟩, rfl⟩

/-- Topological surface-capping statement for (5.1) (page 171): given a painting $\Gamma$ in a
connected compact surface $\Sigma$ and a cuff $\Theta \in \text{cuffs}(\Sigma)$, pasting a closed
disc onto $\Theta$ yields a connected compact surface $\Sigma'$, a closed embedding
$\iota \colon \Sigma \to \Sigma'$, and a painting $\Gamma' = (\iota '' U(\Gamma), \iota ''
N(\Gamma))$
in $\Sigma'$ such that $\Sigma'$ is simpler than $\Sigma$, $\operatorname{bd}(\Sigma') =
\iota '' (\operatorname{bd}(\Sigma) \setminus \Theta)$, $\text{cuffs}(\Sigma') =
\{\iota '' \Theta' \mid \Theta' \in \text{cuffs}(\Sigma) \setminus \{\Theta\}\}$, and the cells of
$\Gamma'$ are $\{\iota '' c \mid c \in C(\Gamma)\}$. -/
@[expose] def PasteCuffPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [CompactSpace S] [T2Space S] [ConnectedSpace S],
    IsSurface S → ∀ (Γ : Painting S) (Θ : Set S), Θ ∈ cuffs S →
    ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
      (_ : ConnectedSpace S'),
      IsSurface S' ∧ IsSimplerThan S' S ∧
      ∃ (ι : S → S') (Γ' : Painting S'),
        Function.Injective ι ∧
        Γ'.N = ι '' Γ.N ∧
        Γ'.C = (fun c => ι '' c) '' Γ.C ∧
        bd S' = ι '' (bd S \ Θ) ∧
        cuffs S' = (fun Θ' => ι '' Θ') '' (cuffs S \ {Θ}) ∧
        (∀ c ∈ Γ.C, tilde (ι '' c) = ι '' tilde c) ∧
        (∀ Θ' ∈ cuffs S, Θ' ≠ Θ → ∀ n₁ ∈ Γ.N ∩ Θ', ∀ n₂ ∈ Γ.N ∩ Θ',
          ∀ n₃ ∈ Γ.N ∩ Θ', ∀ n₄ ∈ Γ.N ∩ Θ',
          GM19.InOrderOn (ι '' Θ') (ι n₁) (ι n₂) (ι n₃) (ι n₄) →
          GM19.InOrderOn Θ' n₁ n₂ n₃ n₄)

/-- Corollary of (5.1) (page 171): "From (5.1), every 0-redundant $\mathscr{T}$-central portrayal
has warp $\ge 1$." -/
theorem one_le_warp_of_isZeroRedundant
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) :
    1 ≤ π.warp :=
  π.one_le_warp

/-! ## 4. Cutting Along a $\Gamma$-Normal $I$-Arc or $O$-Arc: (5.3) and (5.4) (Pages 172–173) -/

/-- Separation of $G$ of order $0$ induced by a curve $F$ with $F \cap \operatorname{dom}(\gamma) =
\emptyset$ and $\beta(n) = \emptyset$ for all $n \in F \cap N(\Gamma) \cap
\operatorname{bd}(\Sigma)$
that partitions $C(\Gamma)$ into $I_1$ and $I_2 = C(\Gamma) \setminus I_1$ so that any node in
$\tilde{c}_1 \cap \tilde{c}_2$ ($c_1 \in I_1, c_2 \in I_2$) lies in $F$: by (2.1)
(`theorem_2_1_proof`),
$(\alpha(I_1), \alpha(I_2))$ is a separation of $G$ of order $0$.
Graph Minors XVII, proofs of (5.3) and (5.4) (pages 172–173). -/
theorem Portrayal.isSeparation_order_zero_of_normal_cut
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {F : Set π.S}
    (hγ : F ∩ π.domγ = ∅)
    (hβ : ∀ n ∈ F ∩ (π.Γ.N ∩ bd π.S), π.borderSet n = ∅)
    {I₁ I₂ : Set (Set π.S)}
    (hI₁ : I₁ ⊆ π.Γ.C) (hI₂ : I₂ = π.Γ.C \ I₁)
    (hsep : ∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ ⊆ F) :
    G.IsSeparation (π.cellsUnion I₁) (π.cellsUnion I₂) ∧
    (π.cellsUnion I₁).vertexSet ∩ (π.cellsUnion I₂).vertexSet = ∅ := by
  have hunion : I₁ ∪ I₂ = π.Γ.C := by
    rw [hI₂, union_sdiff_self, union_eq_self_of_subset_left hI₁]
  have hdisj : Disjoint I₁ I₂ := by
    rw [hI₂]
    exact disjoint_sdiff_self_right
  refine ⟨π.isSeparation_cellsUnion hunion hdisj, ?_⟩
  have h21 := (theorem_2_1_proof π hunion hdisj).2
  change (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet = ∅
  rw [h21, eq_empty_iff_forall_notMem]
  rintro v (hγv | hβv)
  · simp only [mem_iUnion, mem_inter_iff] at hγv
    obtain ⟨c₁, hc₁, c₂, hc₂, ⟨n₁, ⟨hn₁c₁, hn₁γ⟩, hEq₁⟩, ⟨n₂, ⟨hn₂c₂, hn₂γ⟩, hEq₂⟩⟩ := hγv
    obtain rfl : n₁ = n₂ := π.nodeVertex_injOn hn₁γ hn₂γ (hEq₁.trans hEq₂.symm)
    have hnF : n₁ ∈ F := hsep c₁ hc₁ c₂ hc₂ ⟨hn₁c₁, hn₂c₂⟩
    have hmem : n₁ ∈ F ∩ π.domγ := ⟨hnF, hn₁γ⟩
    rw [hγ] at hmem
    exact hmem
  · simp only [mem_iUnion, mem_ofPred_eq] at hβv
    obtain ⟨n, ⟨c₁, hc₁, hc₁bd, c₂, hc₂, _, hn₁, hn₂⟩, hvn⟩ := hβv
    have hnF : n ∈ F := hsep c₁ hc₁ c₂ hc₂ ⟨hn₁, hn₂⟩
    obtain ⟨u, w, _, htilde, _, _, hu, hw⟩ := π.Γ.border_cell_exists_ends (hI₁ hc₁) hc₁bd
    have hn_bd : n ∈ π.Γ.N ∩ bd π.S := by
      rw [htilde] at hn₁
      rcases hn₁ with rfl | rfl
      · exact hu
      · exact hw
    rw [hβ n ⟨hnF, hn_bd⟩] at hvn
    exact hvn

private lemma homeomorph_image_symm_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (ψ : X ≃ₜ Y) (s : Set Y) : ψ '' (ψ.symm '' s) = s := by
  rw [image_image]
  simp [ψ.apply_symm_apply]

/-- Any homeomorphism $\psi \colon X \simeq_t Y$ maps cuffs of $X$ to cuffs of $Y$. -/
theorem image_cuff_mem_cuffs {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (ψ : X ≃ₜ Y) {Θ : Set X} (hΘ : Θ ∈ cuffs X) :
    ψ '' Θ ∈ cuffs Y := by
  rcases hΘ with ⟨x, hx, rfl⟩
  rw [ψ.image_connectedComponentIn hx, image_bd_homeomorph ψ]
  exact ⟨ψ x, image_bd_homeomorph ψ ▸ mem_image_of_mem ψ hx, rfl⟩

/-- `IsSimplerThan` is invariant under homeomorphism of the right-hand space. -/
theorem IsSimplerThan.congr_right {X Y₁ Y₂ : Type*}
    [TopologicalSpace X] [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (ψ : Y₁ ≃ₜ Y₂) :
    IsSimplerThan X Y₁ ↔ IsSimplerThan X Y₂ := by
  unfold IsSimplerThan
  constructor
  · rintro ⟨a, b, c, a', b', c', hX, ⟨hY₁⟩, hb, h1, h2⟩
    exact ⟨a, b, c, a', b', c', hX, ⟨ψ.symm.trans hY₁⟩, hb, h1, h2⟩
  · rintro ⟨a, b, c, a', b', c', hX, ⟨hY₂⟩, hb, h1, h2⟩
    exact ⟨a, b, c, a', b', c', hX, ⟨ψ.trans hY₂⟩, hb, h1, h2⟩

/-- `Portrayal.Resembles` is reflexive. -/
theorem Portrayal.Resembles.refl {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) : π.Resembles π :=
  ⟨Homeomorph.refl π.S, fun Θ _ => by simp⟩

/-- `Portrayal.Resembles` is symmetric. -/
theorem Portrayal.Resembles.symm {α₁ α₂ β₁ β₂ : Type*} {G₁ : Hypergraph α₁ β₁} {G₂ : Hypergraph α₂
  β₂}
    {π₁ : Portrayal G₁} {π₂ : Portrayal G₂} (h : π₁.Resembles π₂) :
    π₂.Resembles π₁ := by
  rcases h with ⟨ψ, hψ⟩
  refine ⟨ψ.symm, fun Φ hΦ => ?_⟩
  have hΘ : ψ.symm '' Φ ∈ cuffs π₁.S := image_cuff_mem_cuffs ψ.symm hΦ
  have hEq := hψ (ψ.symm '' Φ) hΘ
  rw [homeomorph_image_symm_image ψ Φ] at hEq
  exact hEq.symm

/-- `Portrayal.Resembles` is transitive. -/
theorem Portrayal.Resembles.trans {α₁ α₂ α₃ β₁ β₂ β₃ : Type*} {G₁ : Hypergraph α₁ β₁}
    {G₂ : Hypergraph α₂ β₂} {G₃ : Hypergraph α₃ β₃}
    {π₁ : Portrayal G₁} {π₂ : Portrayal G₂} {π₃ : Portrayal G₃}
    (h₁₂ : π₁.Resembles π₂) (h₂₃ : π₂.Resembles π₃) :
    π₁.Resembles π₃ := by
  rcases h₁₂ with ⟨ψ₁, hψ₁⟩
  rcases h₂₃ with ⟨ψ₂, hψ₂⟩
  refine ⟨ψ₁.trans ψ₂, fun Θ hΘ => ?_⟩
  have hΦ : ψ₁ '' Θ ∈ cuffs π₂.S := image_cuff_mem_cuffs ψ₁ hΘ
  change π₁.warpAt Θ = π₃.warpAt ((ψ₂ ∘ ψ₁) '' Θ)
  rw [image_comp, hψ₁ Θ hΘ, hψ₂ (ψ₁ '' Θ) hΦ]

/-- Resembling portrayals have equal warp. -/
theorem Portrayal.Resembles.warp_eq {α₁ α₂ β₁ β₂ : Type*} {G₁ : Hypergraph α₁ β₁} {G₂ : Hypergraph
  α₂ β₂}
    {π₁ : Portrayal G₁} {π₂ : Portrayal G₂} (h : π₁.Resembles π₂) :
    π₁.warp = π₂.warp := by
  classical
  rcases h with ⟨ψ, hψ⟩
  have hcuffs_iff : (cuffs π₁.S).Nonempty ↔ (cuffs π₂.S).Nonempty :=
    ⟨fun ⟨Θ, hΘ⟩ => ⟨ψ '' Θ, image_cuff_mem_cuffs ψ hΘ⟩,
     fun ⟨Φ, hΦ⟩ => ⟨ψ.symm '' Φ, image_cuff_mem_cuffs ψ.symm hΦ⟩⟩
  unfold Portrayal.warp
  by_cases hne : (cuffs π₁.S).Nonempty
  · rw [ite_eq_left hne, ite_eq_left (hcuffs_iff.mp hne)]
    refine congrArg (max 1) (congrArg sSup ?_)
    ext p
    constructor
    · rintro ⟨Θ, hΘ, rfl⟩
      exact ⟨ψ '' Θ, image_cuff_mem_cuffs ψ hΘ, hψ Θ hΘ⟩
    · rintro ⟨Φ, hΦ, rfl⟩
      have hΘ : ψ.symm '' Φ ∈ cuffs π₁.S := image_cuff_mem_cuffs ψ.symm hΦ
      refine ⟨ψ.symm '' Φ, hΘ, ?_⟩
      have hEq := hψ (ψ.symm '' Φ) hΘ
      rw [homeomorph_image_symm_image ψ Φ] at hEq
      exact hEq.symm
  · rw [ite_eq_right hne, ite_eq_right (mt hcuffs_iff.mpr hne)]

/-- Resembling portrayals have the same `IsSimpler` relation on the right. -/
theorem Portrayal.Resembles.isSimpler_iff {α₀ α₁ α₂ β₀ β₁ β₂ : Type*}
    {G₀ : Hypergraph α₀ β₀} {G₁ : Hypergraph α₁ β₁} {G₂ : Hypergraph α₂ β₂}
    {π₀ : Portrayal G₀} {π₁ : Portrayal G₁} {π₂ : Portrayal G₂}
    (h : π₁.Resembles π₂) :
    π₀.IsSimpler π₁ ↔ π₀.IsSimpler π₂ := by
  have hw : π₁.warp = π₂.warp := h.warp_eq
  rcases h with ⟨ψ, hψ⟩
  unfold Portrayal.IsSimpler
  rw [IsSimplerThan.congr_right ψ, hw]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨φ, hle, Θ₀, hΘ₀, hlt⟩
    refine ⟨φ.trans ψ, fun Θ hΘ => ?_, Θ₀, hΘ₀, ?_⟩
    · change π₀.warpAt Θ ≤ π₂.warpAt ((ψ ∘ φ) '' Θ)
      rw [image_comp, ← hψ (φ '' Θ) (image_cuff_mem_cuffs φ hΘ)]
      exact hle Θ hΘ
    · change π₀.warpAt Θ₀ < π₂.warpAt ((ψ ∘ φ) '' Θ₀)
      rw [image_comp, ← hψ (φ '' Θ₀) (image_cuff_mem_cuffs φ hΘ₀)]
      exact hlt
  · rintro ⟨φ, hle, Θ₀, hΘ₀, hlt⟩
    refine ⟨φ.trans ψ.symm, fun Θ hΘ => ?_, Θ₀, hΘ₀, ?_⟩
    · have hΦ : (φ.trans ψ.symm) '' Θ ∈ cuffs π₁.S :=
        image_cuff_mem_cuffs (φ.trans ψ.symm) hΘ
      rw [hψ _ hΦ]
      change π₀.warpAt Θ ≤ π₂.warpAt (ψ '' ((ψ.symm ∘ φ) '' Θ))
      rw [image_comp, homeomorph_image_symm_image ψ]
      exact hle Θ hΘ
    · have hΦ₀ : (φ.trans ψ.symm) '' Θ₀ ∈ cuffs π₁.S :=
        image_cuff_mem_cuffs (φ.trans ψ.symm) hΘ₀
      rw [hψ _ hΦ₀]
      change π₀.warpAt Θ₀ < π₂.warpAt (ψ '' ((ψ.symm ∘ φ) '' Θ₀))
      rw [image_comp, homeomorph_image_symm_image ψ]
      exact hlt

/-- If $\pi_1$ resembles $\pi_2$ and $\pi_2$ is 0-redundant relative to $\mathcal{T}$, then
$\pi_1$ is also 0-redundant relative to $\mathcal{T}$. -/
theorem Portrayal.Resembles.isZeroRedundant {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {π₁ π₂ : Portrayal G} (h : π₁.Resembles π₂) (hred : π₂.IsZeroRedundant 𝒯) :
    π₁.IsZeroRedundant 𝒯 :=
  fun π₀ hT hsimp => hred π₀ hT (h.isSimpler_iff.mp hsimp)

/-- If $\pi'$ is a portrayal of $G / Z$ ($|Z| \le z$) that resembles a $z$-redundant portrayal
$\pi$ of $G$, then $\pi'$ is 0-redundant relative to $\mathcal{T} / Z$.
Graph Minors XVII, proofs of (6.3) and (6.4) (page 175). -/
theorem Portrayal.Resembles.isZeroRedundant_quotient
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ z : ℕ}
    {Z : Set α} {π : Portrayal G} {π' : Portrayal (quotientVertices G Z)}
    (h : π'.Resembles π) (hred : π.IsRedundant 𝒯 θ z)
    (hZ : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ z) :
    π'.IsZeroRedundant (quotientTangle G 𝒯 Z) :=
  fun π₀ hT hsimp => hred.2 Z hZ hZ_card π₀ hT (h.isSimpler_iff.mp hsimp)

/-- Shrinking an internal cell $c_0$ from $n$ preserves $\Gamma$-normality of any set $F$. -/
theorem Painting.IsNormal.of_isShrunkenFrom {S : Type} [TopologicalSpace S]
    {Γ Γ' : Painting S} {c₀ : Set S} {n : S} {Δ : Set S} {F : Set S}
    (hnorm : Γ.IsNormal F) (hsh : Γ.IsShrunkenFrom Γ' c₀ n Δ) :
    Γ'.IsNormal F := by
  have hU_sub : Γ'.U ⊆ Γ.U := by
    rw [hsh.2.2.2.2.2.2.1]
    rintro x (⟨hxU, _⟩ | hxΔ)
    · exact hxU
    · exact Γ.isClosed_U.closure_subset_iff.mpr (Γ.cell_subset_U hsh.1.1) (hsh.2.2.2.1 hxΔ)
  intro x ⟨hxF, hxU'⟩
  rw [hsh.2.2.2.2.2.2.2.1]
  exact hnorm ⟨hxF, hU_sub hxU'⟩

private lemma frontier_closedDisc_subset_discBd {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsSurface S) {D : Set S} (hD : IsClosedDisc D) :
    frontier D ⊆ discBd D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have h_open : IsOpen (g '' Metric.ball (0 : ℂ) 1) := c.isOpen_image_ball hS.2.2
  have h_sub_int : g '' Metric.ball (0 : ℂ) 1 ⊆ interior D :=
    h_open.subset_interior_iff.mpr (c.g_subset Metric.ball_subset_closedBall)
  intro x ⟨hx_cl, hx_not_int⟩
  have hxD : x ∈ D := (isClosed_of_isClosedDisc hD).closure_eq ▸ hx_cl
  rw [← (c.union_ball).1] at hxD
  exact hxD.resolve_left fun hx_ball => hx_not_int (h_sub_int hx_ball)

/-- Shrinking an internal cell $c_0$ from $n$ preserves $\alpha(D)$ for every closed disc
$D \subseteq \Sigma$ whose boundary is contained in $F \cup \operatorname{bd}(\Sigma)$ for a
$\Gamma$-normal set $F$. -/
theorem Portrayal.shrinkCell_areaGraph_eq {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) [T2Space π.S]
    (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ : Set π.S)
    (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ)
    (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet)
    {F D : Set π.S} (hnorm : π.Γ.IsNormal F)
    (hD : IsClosedDisc D) (hDbd : discBd D ⊆ F ∪ bd π.S) :
    (π.shrinkCell Γ' c₀ n Δ hsh hn_γ).areaGraph D = π.areaGraph D := by
  classical
  let c' : Set π.S := Δ \ (tilde c₀ \ {n})
  have hc₀C : c₀ ∈ π.Γ.C := hsh.1.1
  have hc₀_bd : ¬ (c₀ ∩ bd π.S).Nonempty := hsh.1.2
  have hc'C : c' ∈ Γ'.C := hsh.2.2.2.2.2.2.2.2.1
  have hΓ'C : Γ'.C = (π.Γ.C \ {c₀}) ∪ {c'} := hsh.2.2.2.2.2.2.2.2.2.2.2
  have hc'_sub_c₀ : c' ⊆ c₀ := by
    intro x hx
    have hx_cl : x ∈ closure c₀ := hsh.2.2.2.1 hx.1
    have hx_not_N : x ∉ π.Γ.N := by
      intro hxN
      have hx_tilde : x ∈ tilde c₀ := by
        rw [← π.Γ.closure_cell_inter_N hc₀C]
        exact ⟨hx_cl, hxN⟩
      have hxn : x ≠ n := fun hEq => hsh.2.2.2.2.1 (hEq ▸ hx.1)
      exact hx.2 ⟨hx_tilde, hxn⟩
    rw [← π.Γ.closure_cell_diff_N hc₀C]
    exact ⟨hx_cl, hx_not_N⟩
  have hc'_sub_iff : c' ⊆ D ↔ c₀ ⊆ D := by
    refine ⟨fun hc'D => ?_, fun hc₀D => hc'_sub_c₀.trans hc₀D⟩
    by_contra hnot
    obtain ⟨y, hyc₀, hyD⟩ := not_subset.mp hnot
    obtain ⟨x, hxc'⟩ := Γ'.cell_nonempty hc'C
    have hxc₀ : x ∈ c₀ := hc'_sub_c₀ hxc'
    have hxD : x ∈ D := hc'D hxc'
    have hc₀_conn : IsPreconnected c₀ := (π.Γ.cell_isPathConnected hc₀C).isConnected.isPreconnected
    have hD_closed : IsClosed D := isClosed_of_isClosedDisc hD
    have h_open₁ : IsOpen (interior D) := isOpen_interior
    have h_open₂ : IsOpen Dᶜ := hD_closed.isOpen_compl
    have h_disj : Disjoint (c₀ ∩ interior D) (c₀ ∩ Dᶜ) :=
      disjoint_left.mpr fun z ⟨_, hz1⟩ ⟨_, hz2⟩ => hz2 (interior_subset hz1)
    have h_not_sub : ¬ c₀ ⊆ interior D ∪ Dᶜ := by
      intro hsub
      have h_ne₁ : (c₀ ∩ interior D).Nonempty := by
        rcases hsub hxc₀ with hx_int | hx_compl
        · exact ⟨x, hxc₀, hx_int⟩
        · exact (hx_compl hxD).elim
      have h_ne₂ : (c₀ ∩ Dᶜ).Nonempty := ⟨y, hyc₀, hyD⟩
      obtain ⟨z, hz⟩ := hc₀_conn (interior D) Dᶜ h_open₁ h_open₂ hsub h_ne₁ h_ne₂
      exact h_disj.le_bot ⟨⟨hz.1, hz.2.1⟩, ⟨hz.1, hz.2.2⟩⟩
    obtain ⟨z, hzc₀, hz_not⟩ := not_subset.mp h_not_sub
    have hz_fr : z ∈ frontier D := by
      rw [frontier, hD_closed.closure_eq]
      exact ⟨by_contra fun hzD => hz_not (Or.inr hzD), fun hz_int => hz_not (Or.inl hz_int)⟩
    have hz_bd : z ∈ F ∪ bd π.S :=
      hDbd (frontier_closedDisc_subset_discBd π.isSurface hD hz_fr)
    rcases hz_bd with hzF | hzbd
    · have hz_diff : z ∈ π.Γ.U \ π.Γ.N := π.Γ.cell_subset_diff hc₀C hzc₀
      exact hz_diff.2 (hnorm ⟨hzF, hz_diff.1⟩)
    · exact hc₀_bd ⟨z, hzc₀, hzbd⟩
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    ((π.shrinkCell Γ' c₀ n Δ hsh hn_γ).cellsUnion_le _) (π.cellsUnion_le _)
  · dsimp only [Portrayal.areaGraph, Portrayal.cellsUnion, Portrayal.shrinkCell]
    ext v
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨d, ⟨⟨hd, hdD⟩, _⟩, hvd⟩
      rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
      · rw [ite_eq_right hdc'] at hvd
        exact ⟨d, ⟨⟨hdC, hdD⟩, hdC⟩, hvd⟩
      · rw [ite_eq_left rfl] at hvd
        exact ⟨c₀, ⟨⟨hc₀C, hc'_sub_iff.mp hdD⟩, hc₀C⟩, hvd⟩
    · rintro ⟨d, ⟨⟨hdC, hdD⟩, _⟩, hvd⟩
      by_cases hdc₀ : d = c₀
      · subst hdc₀
        exact ⟨c', ⟨⟨hc'C, hc'_sub_iff.mpr hdD⟩, hc'C⟩, by rwa [ite_eq_left rfl]⟩
      · have hdc' : d ≠ c' := by rintro rfl; exact shrunk_cell_not_mem_old hsh ⟨hdC, hdc₀⟩
        have hd' : d ∈ Γ'.C := by rw [hΓ'C]; exact Or.inl ⟨hdC, hdc₀⟩
        exact ⟨d, ⟨⟨hd', hdD⟩, hd'⟩, by rwa [ite_eq_right hdc']⟩
  · dsimp only [Portrayal.areaGraph, Portrayal.cellsUnion, Portrayal.shrinkCell]
    ext e
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨d, ⟨⟨hd, hdD⟩, _⟩, hed⟩
      rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, _⟩, hdc'⟩ | rfl
      · rw [ite_eq_right hdc'] at hed
        exact ⟨d, ⟨⟨hdC, hdD⟩, hdC⟩, hed⟩
      · rw [ite_eq_left rfl] at hed
        exact ⟨c₀, ⟨⟨hc₀C, hc'_sub_iff.mp hdD⟩, hc₀C⟩, hed⟩
    · rintro ⟨d, ⟨⟨hdC, hdD⟩, _⟩, hed⟩
      by_cases hdc₀ : d = c₀
      · subst hdc₀
        exact ⟨c', ⟨⟨hc'C, hc'_sub_iff.mpr hdD⟩, hc'C⟩, by rwa [ite_eq_left rfl]⟩
      · have hdc' : d ≠ c' := by rintro rfl; exact shrunk_cell_not_mem_old hsh ⟨hdC, hdc₀⟩
        have hd' : d ∈ Γ'.C := by rw [hΓ'C]; exact Or.inl ⟨hdC, hdc₀⟩
        exact ⟨d, ⟨⟨hd', hdD⟩, hd'⟩, by rwa [ite_eq_right hdc']⟩

/-- The finite set of pairs $(c, n)$ where $c \in C(\Gamma)$ is an internal cell and
$n \in \tilde{c} \cap F$. -/
private def internalNodesOn {S : Type} [TopologicalSpace S] (Γ : Painting S) (F : Set S) :
    Set (Set S × S) :=
  {p ∈ Γ.C ×ˢ Γ.N | ¬ (p.1 ∩ bd S).Nonempty ∧ p.2 ∈ tilde p.1 ∩ F}

private lemma finite_internalNodesOn {S : Type} [TopologicalSpace S] (Γ : Painting S) (F : Set S) :
    (internalNodesOn Γ F).Finite :=
  (Γ.finite_cells.prod Γ.finite_N).subset fun _ h => h.1

private lemma ncard_internalNodesOn_lt_of_isShrunkenFrom {S : Type} [TopologicalSpace S]
    {Γ Γ' : Painting S} {c₀ : Set S} {n : S} {Δ F : Set S}
    (hsh : Γ.IsShrunkenFrom Γ' c₀ n Δ) (hnF : n ∈ F) :
    (internalNodesOn Γ' F).ncard < (internalNodesOn Γ F).ncard := by
  classical
  let c' : Set S := Δ \ (tilde c₀ \ {n})
  have hc₀C : c₀ ∈ Γ.C := hsh.1.1
  have hc₀_bd : ¬ (c₀ ∩ bd S).Nonempty := hsh.1.2
  have hn_tilde : n ∈ tilde c₀ := hsh.2.1
  have hΓ'N : Γ'.N = Γ.N := hsh.2.2.2.2.2.2.2.1
  have htilde_c' : tilde c' = tilde c₀ \ {n} := hsh.2.2.2.2.2.2.2.2.2.2.1
  let f : Set S × S → Set S × S := fun p =>
    if p.1 = c' then (c₀, p.2) else p
  have hf_inj : InjOn f (internalNodesOn Γ' F) := by
    rintro ⟨d₁, m₁⟩ h₁ ⟨d₂, m₂⟩ h₂ hEq
    dsimp only [f] at hEq
    rcases shrunk_cell_cases hsh h₁.1.1 with ⟨⟨_, hd₁c₀⟩, hd₁c'⟩ | rfl <;>
      rcases shrunk_cell_cases hsh h₂.1.1 with ⟨⟨_, hd₂c₀⟩, hd₂c'⟩ | rfl
    · rw [ite_eq_right hd₁c', ite_eq_right hd₂c'] at hEq
      exact hEq
    · rw [ite_eq_right hd₁c', ite_eq_left rfl] at hEq
      exact (hd₁c₀ (Prod.ext_iff.mp hEq).1).elim
    · rw [ite_eq_left rfl, ite_eq_right hd₂c'] at hEq
      exact (hd₂c₀ (Prod.ext_iff.mp hEq).1.symm).elim
    · rw [ite_eq_left rfl, ite_eq_left rfl] at hEq
      exact Prod.ext rfl (Prod.ext_iff.mp hEq).2
  have hf_sub : f '' (internalNodesOn Γ' F) ⊆ internalNodesOn Γ F \ {(c₀, n)} := by
    rintro _ ⟨⟨d, m⟩, ⟨⟨hd, hmN⟩, hdbd, hm_tilde, hmF⟩, rfl⟩
    rw [hΓ'N] at hmN
    dsimp only [f]
    rcases shrunk_cell_cases hsh hd with ⟨⟨hdC, hdc₀⟩, hdc'⟩ | rfl
    · rw [ite_eq_right hdc']
      exact ⟨⟨⟨hdC, hmN⟩, hdbd, hm_tilde, hmF⟩, fun hEq => hdc₀ (Prod.ext_iff.mp hEq).1⟩
    · rw [ite_eq_left rfl]
      rw [htilde_c'] at hm_tilde
      exact ⟨⟨⟨hc₀C, hmN⟩, hc₀_bd, hm_tilde.1, hmF⟩,
        fun hEq => hm_tilde.2 (Prod.ext_iff.mp hEq).2⟩
  have hmem : (c₀, n) ∈ internalNodesOn Γ F :=
    ⟨⟨hc₀C, Γ.tilde_subset_N hc₀C hn_tilde⟩, hc₀_bd, hn_tilde, hnF⟩
  have hfin : (internalNodesOn Γ F).Finite := finite_internalNodesOn Γ F
  have hfin_sdiff : (internalNodesOn Γ F \ {(c₀, n)}).Finite := hfin.subset sdiff_subset
  calc (internalNodesOn Γ' F).ncard
      = (f '' (internalNodesOn Γ' F)).ncard := hf_inj.ncard_image.symm
    _ ≤ (internalNodesOn Γ F \ {(c₀, n)}).ncard := ncard_le_ncard hf_sub hfin_sdiff
    _ = (internalNodesOn Γ F).ncard - 1 := ncard_sdiff_singleton_of_mem hmem
    _ < (internalNodesOn Γ F).ncard := by
        have hpos : 0 < (internalNodesOn Γ F).ncard := (ncard_pos hfin).mpr ⟨(c₀, n), hmem⟩
        omega

/-- Step 1 of the proof of (5.3) and (5.4) (pages 172–173): by repeatedly applying (5.2)
(`Portrayal.shrinkCell`) and inducting on the number of pairs $(c, n)$ with $c \in C(\Gamma)$
internal and $n \in \tilde{c} \cap F$, any property $P(\pi, F)$ that is preserved under shrinking an
internal cell $c_0$ from $n \in \tilde{c}_0 \cap F$ and holds whenever
$\tilde{c} \cap F = \emptyset$ for all internal cells $c \in C(\Gamma)$ holds for every
0-redundant $\mathcal{T}$-central portrayal $\pi$ and every $\Gamma$-normal subset
$F \subseteq \Sigma$ with $F \cap \operatorname{dom}(\gamma) = \emptyset$. -/
theorem Portrayal.induction_shrink_internal_cells {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {P : ∀ (π : Portrayal G), Set π.S → Prop}
    (hbase : ∀ (π : Portrayal G) [CompactSpace π.S] [T2Space π.S],
      π.IsCentral 𝒯 → π.IsZeroRedundant 𝒯 →
      ∀ (F : Set π.S), π.Γ.IsNormal F → F ∩ π.domγ = ∅ →
      (∀ c ∈ π.Γ.C, π.Γ.IsInternalCell c → Disjoint (tilde c) F) →
      P π F)
    (hstep : ∀ (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
      (Γ' : Painting π.S) (c₀ : Set π.S) (n : π.S) (Δ₀ : Set π.S)
      (hsh : π.Γ.IsShrunkenFrom Γ' c₀ n Δ₀)
      (hn_γ : n ∈ π.domγ → π.nodeVertex n ∉ (π.cellGraph c₀).vertexSet)
      (F : Set π.S), π.Γ.IsNormal F →
      P (π.shrinkCell Γ' c₀ n Δ₀ hsh hn_γ) F → P π F)
    (π : Portrayal G) [CompactSpace π.S] [T2Space π.S]
    (hT : π.IsCentral 𝒯) (hred : π.IsZeroRedundant 𝒯)
    {F : Set π.S} (hnorm : π.Γ.IsNormal F) (hFγ : F ∩ π.domγ = ∅) :
    P π F := by
  suffices hmain : ∀ k : ℕ, ∀ (π₁ : Portrayal G) [CompactSpace π₁.S] [T2Space π₁.S],
      π₁.IsCentral 𝒯 → π₁.IsZeroRedundant 𝒯 →
      ∀ (F₁ : Set π₁.S), π₁.Γ.IsNormal F₁ → F₁ ∩ π₁.domγ = ∅ →
      (internalNodesOn π₁.Γ F₁).ncard ≤ k → P π₁ F₁ by
    exact hmain (internalNodesOn π.Γ F).ncard π hT hred F hnorm hFγ le_rfl
  intro k
  induction k with
  | zero =>
    intro π₁ _ _ hT₁ hred₁ F₁ hnorm₁ hF₁γ hle
    refine hbase π₁ hT₁ hred₁ F₁ hnorm₁ hF₁γ ?_
    intro c hc hc_int
    rw [disjoint_left]
    intro n hn_tilde hnF
    have hmem : (c, n) ∈ internalNodesOn π₁.Γ F₁ :=
      ⟨⟨hc, π₁.Γ.tilde_subset_N hc hn_tilde⟩, hc_int.2, hn_tilde, hnF⟩
    have hpos : 0 < (internalNodesOn π₁.Γ F₁).ncard :=
      (ncard_pos (finite_internalNodesOn π₁.Γ F₁)).mpr ⟨(c, n), hmem⟩
    omega
  | succ k ih =>
    intro π₁ _ _ hT₁ hred₁ F₁ hnorm₁ hF₁γ hle
    by_cases hex : ∃ c ∈ π₁.Γ.C, π₁.Γ.IsInternalCell c ∧ ∃ n ∈ tilde c, n ∈ F₁
    · obtain ⟨c₀, _, hc₀_int, n, hn_tilde, hnF⟩ := hex
      have hn_not_γ : n ∉ π₁.domγ := fun hnγ =>
        eq_empty_iff_forall_notMem.mp hF₁γ n ⟨hnF, hnγ⟩
      have hn_γ : n ∈ π₁.domγ → π₁.nodeVertex n ∉ (π₁.cellGraph c₀).vertexSet :=
        fun hnγ => (hn_not_γ hnγ).elim
      obtain ⟨Δ₀, Γ₂, hsh⟩ := π₁.Γ.exists_isShrunkenFrom hc₀_int hn_tilde
      let π₂ := π₁.shrinkCell Γ₂ c₀ n Δ₀ hsh hn_γ
      have : CompactSpace π₂.S := π₂.isSurface.1
      have : T2Space π₂.S := π₂.isSurface.2.1
      have : ConnectedSpace π₂.S := π₂.connected
      have hT₂ : π₂.IsCentral 𝒯 := π₁.shrinkCell_isCentral hT₁ Γ₂ c₀ n Δ₀ hsh hn_γ
      have hres₂ : π₂.Resembles π₁ := π₁.shrinkCell_resembles Γ₂ c₀ n Δ₀ hsh hn_γ
      have hred₂ : π₂.IsZeroRedundant 𝒯 := hres₂.isZeroRedundant hred₁
      have hnorm₂ : Γ₂.IsNormal F₁ := hnorm₁.of_isShrunkenFrom hsh
      have hlt : (internalNodesOn Γ₂ F₁).ncard < (internalNodesOn π₁.Γ F₁).ncard :=
        ncard_internalNodesOn_lt_of_isShrunkenFrom hsh hnF
      have hle₂ : (internalNodesOn π₂.Γ F₁).ncard ≤ k := by
        change (internalNodesOn Γ₂ F₁).ncard ≤ k
        omega
      exact hstep π₁ Γ₂ c₀ n Δ₀ hsh hn_γ F₁ hnorm₁ (ih π₂ hT₂ hred₂ F₁ hnorm₂ hF₁γ hle₂)
    · refine hbase π₁ hT₁ hred₁ F₁ hnorm₁ hF₁γ ?_
      intro c hc hc_int
      rw [disjoint_left]
      intro n hn_tilde hnF
      exact hex ⟨c, hc, hc_int, n, hn_tilde, hnF⟩

/-- If $H_1, H_2 \le G$ are vertex-disjoint subhypergraphs of $G$, any walk in $(H_1 \cup H_2)^*$
starting at a vertex in $V(H_1)$ is a walk in $H_1^*$ with the same support. -/
private lemma walk_skeleton_sup_of_disjoint {α : Type u} {β : Type v}
    {G H₁ H₂ : Hypergraph α β} (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G)
    (hdisj : H₁.vertexSet ∩ H₂.vertexSet = ∅)
    {u w : α} (hu : u ∈ H₁.vertexSet)
    (W : (H₁ ∪ H₂).skeleton.Walk u w) :
    ∃ W' : H₁.skeleton.Walk u w, W'.support = W.support := by
  induction W with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w hadj W_tail ih =>
    rcases hadj with ⟨huv, e, heu, hev⟩
    have heu₁ : H₁.Inc e u := by
      rcases heu with heu₁ | heu₂
      · exact heu₁
      · exfalso
        exact eq_empty_iff_forall_notMem.mp hdisj u ⟨hu, H₂.vertex_mem_of_inc heu₂⟩
    have hev₁ : H₁.Inc e v := by
      rcases hev with hev₁ | hev₂
      · exact hev₁
      · exfalso
        have heG : G.Inc e u := inc_of_le hH₁ heu₁
        have heH₂ : e ∈ H₂.edgeSet := H₂.edge_mem_of_inc hev₂
        have heu₂ : H₂.Inc e u := (inc_iff_of_le hH₂ heH₂).mpr heG
        exact eq_empty_iff_forall_notMem.mp hdisj u ⟨hu, H₂.vertex_mem_of_inc heu₂⟩
    have hv : v ∈ H₁.vertexSet := H₁.vertex_mem_of_inc hev₁
    have hadj₁ : H₁.skeleton.Adj u v := ⟨huv, e, heu₁, hev₁⟩
    obtain ⟨W'_tail, hsupp⟩ := ih hv
    exact ⟨SimpleGraph.Walk.cons hadj₁ W'_tail, by
      dsimp [SimpleGraph.Walk.support]
      rw [hsupp]⟩

/-- If $H_1, H_2 \le G$ are vertex-disjoint subhypergraphs of $G$ and $X \subseteq V(H_1)$, then
`LinkagePairs` in $H_1^*$ implies `LinkagePairs` in $(H_1 \cup H_2)^*$. -/
theorem linkagePairs_sup_of_disjoint {α : Type u} {β : Type v}
    {G H₁ H₂ : Hypergraph α β} (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G)
    (hdisj : H₁.vertexSet ∩ H₂.vertexSet = ∅)
    {X Y : Set α} (hX : X ⊆ H₁.vertexSet) {k : ℕ} {x y : α}
    (hlink : Portrayal.LinkagePairs H₁.skeleton X Y k x y) :
    Portrayal.LinkagePairs (H₁ ∪ H₂).skeleton X Y k x y := by
  intro P hP_disj
  have hlift : ∀ i : Fin k, ∃ Q : PathFromTo H₁.skeleton X Y,
      Q.first = (P i).first ∧ Q.last = (P i).last ∧ Q.walk.support = (P i).walk.support := by
    intro i
    obtain ⟨W', hsupp⟩ := walk_skeleton_sup_of_disjoint hH₁ hH₂ hdisj (hX (P i).first_mem)
      (P i).walk
    have hisPath : W'.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hsupp, ← SimpleGraph.Walk.isPath_def]
      exact (P i).isPath
    exact ⟨⟨(P i).first, (P i).last, W', hisPath, (P i).first_mem, (P i).last_mem⟩,
      rfl, rfl, hsupp⟩
  choose Q hQ_first hQ_last hQ_supp using hlift
  have hQ_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support} := by
    intro i j hij
    rw [hQ_supp i, hQ_supp j]
    exact hP_disj hij
  obtain ⟨i, hfirst, hlast⟩ := hlink Q hQ_disj
  exact ⟨i, (hQ_first i).symm.trans hfirst, (hQ_last i).symm.trans hlast⟩

/-- Pure surface-and-painting relation saying that $(S', \iota, \Gamma')$ is the painting on the
surface obtained from $(S, \Gamma)$ by cutting along a curve $F \subseteq S$ and keeping the cell
set $I_{\text{keep}} \subseteq C(\Gamma)$. -/
structure IsCutSidePainting (S : Type) [TopologicalSpace S]
    (Γ : Painting S) (F : Set S) (I_keep : Set (Set S))
    (S' : Type) [TopologicalSpace S'] (ι : S → S') (Γ' : Painting S') : Prop where
  /-- $\iota$ is injective. -/
  inj : Function.Injective ι
  /-- Every cell of $I_{\text{keep}}$ maps to a cell of $\Gamma'$. -/
  cells_sub : (fun c => ι '' c) '' I_keep ⊆ Γ'.C
  /-- $C(\Gamma')$ is nonempty. -/
  cells_nonempty : Γ'.C.Nonempty
  /-- Every active node of $I_{\text{keep}}$ outside $F$ maps to a node of $\Gamma'$. -/
  nodes_sub : ι '' {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c} ⊆ Γ'.N
  /-- A node outside $F$ lies in $\tilde{c}$ exactly when its image lies in the corresponding set of
  $\iota '' c$, for every $c \in I_{\text{keep}}$. At an end of $F$ this can fail: the surface
  $\Gamma_0$ of the
  proof of (5.3) has two copies of such an end, one for each side of $F$. -/
  tilde_image : ∀ c ∈ I_keep, ∀ n ∉ F, ι n ∈ tilde (ι '' c) ↔ n ∈ tilde c
  /-- Border cell preservation for $c \in I_{\text{keep}}$. -/
  bd_cell_iff : ∀ c ∈ I_keep, ((ι '' c) ∩ bd S').Nonempty ↔ (c ∩ bd S).Nonempty
  /-- Boundary node preservation for active nodes of $I_{\text{keep}}$ outside $F$. -/
  bd_node_iff : ∀ n ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c}, ι n ∈ bd S' ↔ n ∈ bd S
  /-- Any new cell in $C(\Gamma') \setminus (\text{image}(\iota) '' I_{\text{keep}})$ has no active
  nodes from $I_{\text{keep}} \setminus F$. -/
  new_cell_disjoint : ∀ d ∈ Γ'.C, d ∉ (fun c => ι '' c) '' I_keep →
    Disjoint (tilde d) (ι '' {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c})
  /-- Separation of cuffs on $S'$ corresponds either to distinct cuffs of $S$ or to separation along
  a cuff of $S$ by nodes of $F$. -/
  cuff_sep : ∀ Φ ∈ cuffs S',
    ∀ n₁ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c}, ι n₁ ∈ Φ →
    ∀ n₂ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c}, ι n₂ ∉ Φ →
    ∃ Θ ∈ cuffs S, n₁ ∈ Θ ∧
      (n₂ ∉ Θ ∨ (n₂ ∈ Θ ∧ ∃ a ∈ F ∩ (Γ.N ∩ Θ), ∃ b ∈ F ∩ (Γ.N ∩ Θ),
        GM19.InOrderOn Θ n₁ a n₂ b))
  /-- Cyclic order on a cuff $\Phi$ of $S'$ lifts to a cuff $\Theta$ of $S$. -/
  cuff_order : ∀ Φ ∈ cuffs S',
    ∀ x₁ ∈ Γ'.N ∩ Φ, ∀ x₂ ∈ Γ'.N ∩ Φ, ∀ x₃ ∈ Γ'.N ∩ Φ, ∀ x₄ ∈ Γ'.N ∩ Φ,
    GM19.InOrderOn Φ x₁ x₂ x₃ x₄ →
    ∀ n₁ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c}, x₁ = ι n₁ →
    ∀ n₃ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c}, x₃ = ι n₃ →
    ∀ Θ ∈ cuffs S, n₁ ∈ Θ → n₃ ∈ Θ →
    (∃ a ∈ F ∩ (Γ.N ∩ Θ), ∃ b ∈ F ∩ (Γ.N ∩ Θ), GM19.InOrderOn Θ n₁ a n₃ b) ∨
    (∃ n₂ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c} ∩ Θ, x₂ = ι n₂ ∧
      ∃ b ∈ (F ∩ (Γ.N ∩ Θ)) ∪ {m ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c} ∩ Θ | x₄ = ι m},
        GM19.InOrderOn Θ n₁ n₂ n₃ b) ∨
    (∃ n₄ ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c} ∩ Θ, x₄ = ι n₄ ∧
      ∃ a ∈ (F ∩ (Γ.N ∩ Θ)) ∪ {m ∈ {n ∈ Γ.N \ F | ∃ c ∈ I_keep, n ∈ tilde c} ∩ Θ | x₂ = ι m},
        GM19.InOrderOn Θ n₁ a n₃ n₄)

private lemma exists_cuff_of_mem_bd {S : Type*} [TopologicalSpace S] {x : S} (hx : x ∈ bd S) :
    ∃ Θ ∈ cuffs S, x ∈ Θ :=
  ⟨connectedComponentIn (bd S) x, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

private lemma Painting.border_cell_subset_bd {S : Type} [TopologicalSpace S]
    (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    tilde c ⊆ bd S := by
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  intro n hn
  rw [htilde] at hn
  rcases hn with rfl | rfl
  · exact hu.2
  · exact hv.2

@[simp]
theorem Portrayal.cellsUnion_empty_vertexSet {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) : (π.cellsUnion ∅).vertexSet = ∅ := by
  ext v
  simp [Portrayal.cellsUnion]

@[simp]
theorem Portrayal.cellsUnion_empty_edgeSet {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) : (π.cellsUnion ∅).edgeSet = ∅ := by
  ext e
  simp [Portrayal.cellsUnion]

theorem Portrayal.isSmallWrt_cellsUnion_empty {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (π : Portrayal G) (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ) :
    IsSmallWrt 𝒯 (π.cellsUnion ∅) := by
  have hcov : (∅ : Set (Set π.S)) ∪ π.Γ.C = π.Γ.C := empty_union _
  have hdisj : Disjoint (∅ : Set (Set π.S)) π.Γ.C := Set.empty_disjoint _
  have hsep : G.IsSeparation (π.cellsUnion ∅) (π.cellsUnion π.Γ.C) :=
    π.isSeparation_cellsUnion hcov hdisj
  have hord : separationOrder (π.cellsUnion ∅) (π.cellsUnion π.Γ.C) < θ := by
    unfold separationOrder
    have hinter : (π.cellsUnion ∅ ∩ π.cellsUnion π.Γ.C).vertexSet = ∅ := by
      rw [inter_vertexSet, π.cellsUnion_empty_vertexSet, empty_inter]
    rw [hinter, ncard_empty]
    exact hθ
  rcases hTangle.axiom1 hsep hord with h1 | h2
  · exact ⟨π.cellsUnion π.Γ.C, h1⟩
  · exfalso
    have hV : (π.cellsUnion π.Γ.C).vertexSet = G.vertexSet :=
      congrArg Hypergraph.vertexSet π.cellsUnion_C
    exact hTangle.axiom3 h2 hV

private def cutSideNodes {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (F : Set π.S) (kept : Set (Set π.S)) : Set π.S :=
  {n ∈ π.Γ.N \ F | ∃ c ∈ kept, n ∈ tilde c}

open Classical in
private noncomputable def cutSideGraph {α : Type u} {β : Type v} {G : Hypergraph α β}
    {S' : Type} (π : Portrayal G) (absorbed : Set (Set π.S))
    (baseGraph : Set S' → Hypergraph α β) (distinguished d : Set S') : Hypergraph α β :=
  if d = distinguished then baseGraph d ∪ π.cellsUnion absorbed else baseGraph d

open Classical in
private noncomputable def assembleCutSidePortrayal
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {F : Set π.S} {I_keep I_absorb : Set (Set π.S)}
    {S' : Type} [tS' : TopologicalSpace S'] [connS' : ConnectedSpace S']
    (hsS' : IsSurface S') {ι : π.S → S'} {Γ' : Painting S'}
    (hcut : IsCutSidePainting π.S π.Γ F I_keep S' ι Γ')
    (hI_keep : I_keep ⊆ π.Γ.C) (hI_absorb : I_absorb = π.Γ.C \ I_keep)
    (hV_disj : (π.cellsUnion I_keep).vertexSet ∩ (π.cellsUnion I_absorb).vertexSet = ∅)
    (hFγ : F ∩ π.domγ = ∅)
    (baseGraph : Set S' → Hypergraph α β) (d₀ : Set S') (hd₀_mem : d₀ ∈ Γ'.C)
    (hbase_eq : ∀ c ∈ I_keep, baseGraph (ι '' c) = π.cellGraph c)
    (hbase_bot : ∀ d ∉ (fun c => ι '' c) '' I_keep, baseGraph d = π.cellsUnion ∅)
    (hbase_le : ∀ d, baseGraph d ≤ G)
    (hbase_sub_keep : ∀ d, (baseGraph d).vertexSet ⊆ (π.cellsUnion I_keep).vertexSet)
    (hle_α' : ∀ d, baseGraph d ≤ cutSideGraph π I_absorb baseGraph d₀ d)
    (β' : S' → Set α) (γ' : S' → α)
    (hβ'_eq : ∀ n ∈ cutSideNodes π F I_keep, β' (ι n) = π.borderSet n)
    (hβ'_empty : ∀ x ∉ ι '' cutSideNodes π F I_keep, β' x = ∅)
    (hγ'_eq : ∀ n, γ' (ι n) = π.nodeVertex n)
    (hbp_F : ∀ n ∈ F ∩ (π.Γ.N ∩ bd π.S), ∀ v : α,
      ¬ (v ∈ π.borderSet n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n))
    (hbp_sep_Θ : ∀ {Θ : Set π.S}, Θ ∈ cuffs π.S → ∀ {n₁ n₂ a b : π.S},
      n₁ ∈ π.Γ.N ∩ Θ → n₂ ∈ π.Γ.N ∩ Θ → a ∈ F ∩ (π.Γ.N ∩ Θ) →
        b ∈ F ∩ (π.Γ.N ∩ Θ) → GM19.InOrderOn Θ n₁ a n₂ b → ∀ v : α,
        v ∈ π.borderSet n₁ ∨ n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁ →
        v ∈ π.borderSet n₂ ∨ n₂ ∈ π.domγ ∧ v = π.nodeVertex n₂ → False)
    (hbp_same_cuff : ∀ {n₁ n₂ : π.S} {Θ : Set π.S}, Θ ∈ cuffs π.S →
      n₁ ∈ π.Γ.N ∩ Θ → n₂ ∈ π.Γ.N → ∀ v : α,
        v ∈ π.borderSet n₁ ∨ n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁ →
        n₂ ∈ bd π.S ∧ v ∈ π.borderSet n₂ ∨ n₂ ∈ π.domγ ∧ v = π.nodeVertex n₂ → n₂ ∈ Θ) :
    Portrayal G where
  S := S'
  top := tS'
  isSurface := hsS'
  connected := connS'
  Γ := Γ'
  cellGraph := cutSideGraph π I_absorb baseGraph d₀
  borderSet := β'
  domγ := ι '' (cutSideNodes π F I_keep ∩ π.domγ)
  nodeVertex := γ'
  cellGraph_le := by
    intro d _
    dsimp [cutSideGraph]
    split_ifs
    · exact union_le (hbase_le d) (π.cellsUnion_le I_absorb)
    · exact hbase_le d
  borderSet_subset := by
    intro x ⟨_, hxbd⟩
    by_cases hxN₁ : x ∈ ι '' (cutSideNodes π F I_keep)
    · obtain ⟨n, hn, rfl⟩ := hxN₁
      rw [hβ'_eq n hn]
      exact π.borderSet_subset n ⟨hn.1.1, (hcut.bd_node_iff n hn).mp hxbd⟩
    · rw [hβ'_empty x hxN₁]
      exact empty_subset _
  domγ_subset := by
    refine Subset.trans (image_mono inter_subset_left) hcut.nodes_sub
  nodeVertex_mem := by
    rintro _ ⟨n, ⟨_, hnγ⟩, rfl⟩
    rw [hγ'_eq n]
    exact π.nodeVertex_mem n hnγ
  nodeVertex_injOn := by
    rintro _ ⟨n₁, ⟨_, hn₁γ⟩, rfl⟩ _ ⟨n₂, ⟨_, hn₂γ⟩, rfl⟩ hEq
    rw [hγ'_eq n₁, hγ'_eq n₂] at hEq
    rw [π.nodeVertex_injOn hn₁γ hn₂γ hEq]
  p1_vertex := by
    intro v hv
    obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
    by_cases hc_keep : c ∈ I_keep
    · refine ⟨ι '' c, hcut.cells_sub (mem_image_of_mem _ hc_keep), ?_⟩
      exact (hle_α' (ι '' c)).vertexSet_subset (by rwa [hbase_eq c hc_keep])
    · have hc_abs : c ∈ I_absorb := by
        rw [hI_absorb]
        exact ⟨hc, hc_keep⟩
      refine ⟨d₀, hd₀_mem, ?_⟩
      dsimp [cutSideGraph]
      rw [ite_eq_left rfl]
      exact Or.inr ((π.cellGraph_le_cellsUnion hc_abs hc).vertexSet_subset hvc)
  p1_edge := by
    intro e he
    obtain ⟨c, hc, hec⟩ := π.p1_edge e he
    by_cases hc_keep : c ∈ I_keep
    · refine ⟨ι '' c, hcut.cells_sub (mem_image_of_mem _ hc_keep), ?_⟩
      exact (hle_α' (ι '' c)).edgeSet_subset (by rwa [hbase_eq c hc_keep])
    · have hc_abs : c ∈ I_absorb := by
        rw [hI_absorb]
        exact ⟨hc, hc_keep⟩
      refine ⟨d₀, hd₀_mem, ?_⟩
      dsimp [cutSideGraph]
      rw [ite_eq_left rfl]
      exact Or.inr ((π.cellGraph_le_cellsUnion hc_abs hc).edgeSet_subset hec)
  p1_disjoint := by
    have hbase_disj_abs : ∀ d, Disjoint (baseGraph d).edgeSet (π.cellsUnion I_absorb).edgeSet := by
      intro d
      by_cases hd : ∃ c ∈ I_keep, d = ι '' c
      · obtain ⟨c, hc, rfl⟩ := hd
        rw [hbase_eq c hc, disjoint_left]
        intro e hec he_abs
        rw [Portrayal.cellsUnion, mem_iUnion₂] at he_abs
        obtain ⟨c₂, ⟨hc₂, hc₂C⟩, hec₂⟩ := he_abs
        have hne : c ≠ c₂ := by
          rintro rfl
          rw [hI_absorb] at hc₂
          exact hc₂.2 hc
        exact (π.p1_disjoint c (hI_keep hc) c₂ hc₂C hne).le_bot ⟨hec, hec₂⟩
      · rw [hbase_bot d (fun ⟨c, hc, hEq⟩ => hd ⟨c, hc, hEq.symm⟩),
          π.cellsUnion_empty_edgeSet]
        exact Set.empty_disjoint _
    have hbase_disj : ∀ d₁ d₂, d₁ ≠ d₂ → Disjoint (baseGraph d₁).edgeSet (baseGraph d₂).edgeSet
      := by
      intro d₁ d₂ hne
      by_cases hd₁ : ∃ c₁ ∈ I_keep, d₁ = ι '' c₁
      · by_cases hd₂ : ∃ c₂ ∈ I_keep, d₂ = ι '' c₂
        · obtain ⟨c₁, hc₁, rfl⟩ := hd₁
          obtain ⟨c₂, hc₂, rfl⟩ := hd₂
          rw [hbase_eq c₁ hc₁, hbase_eq c₂ hc₂]
          exact π.p1_disjoint c₁ (hI_keep hc₁) c₂ (hI_keep hc₂)
            (fun h => hne (congrArg _ h))
        · rw [hbase_bot d₂ (fun ⟨c, hc, hEq⟩ => hd₂ ⟨c, hc, hEq.symm⟩),
            π.cellsUnion_empty_edgeSet]
          exact Set.disjoint_empty _
      · rw [hbase_bot d₁ (fun ⟨c, hc, hEq⟩ => hd₁ ⟨c, hc, hEq.symm⟩),
          π.cellsUnion_empty_edgeSet]
        exact Set.empty_disjoint _
    intro d₁ _ d₂ _ hne
    dsimp [cutSideGraph]
    by_cases hd₁ : d₁ = d₀
    · have hd₂ : d₂ ≠ d₀ := fun h => hne (hd₁.trans h.symm)
      rw [ite_eq_left hd₁, ite_eq_right hd₂, union_edgeSet]
      exact (hbase_disj d₁ d₂ hne).union_left (hbase_disj_abs d₂).symm
    · rw [ite_eq_right hd₁]
      split_ifs with hd₂
      · rw [union_edgeSet]
        exact (hbase_disj d₁ d₂ hne).union_right (hbase_disj_abs d₁)
      · exact hbase_disj d₁ d₂ hne
  p2 := by
    rintro d hd _ ⟨hx_tilde, ⟨n, ⟨hnN₁, hnγ⟩, rfl⟩⟩
    have hd_mem : d ∈ (fun c => ι '' c) '' I_keep := by
      by_contra hd_not
      exact (hcut.new_cell_disjoint d hd hd_not).le_bot ⟨hx_tilde, mem_image_of_mem ι hnN₁⟩
    obtain ⟨c, hc, rfl⟩ := hd_mem
    replace hx_tilde := (hcut.tilde_image c hc n hnN₁.1.2).mp hx_tilde
    rw [hγ'_eq n]
    exact (hle_α' (ι '' c)).vertexSet_subset
      (by rw [hbase_eq c hc]; exact π.p2 c (hI_keep hc) n ⟨hx_tilde, hnγ⟩)
  p3_notMem := by
    rintro _ ⟨⟨n, ⟨hnN₁, hnγ⟩, rfl⟩, hxbd⟩
    rw [hγ'_eq n, hβ'_eq n hnN₁]
    exact π.p3_notMem n ⟨hnγ, (hcut.bd_node_iff n hnN₁).mp hxbd⟩
  p3_subset := by
    intro d hd hdbd x hx_tilde
    by_cases hxN₁ : x ∈ ι '' (cutSideNodes π F I_keep)
    · obtain ⟨n, hnN₁, rfl⟩ := hxN₁
      have hd_mem : d ∈ (fun c => ι '' c) '' I_keep := by
        by_contra hd_not
        exact (hcut.new_cell_disjoint d hd hd_not).le_bot ⟨hx_tilde, mem_image_of_mem ι hnN₁⟩
      obtain ⟨c, hc, rfl⟩ := hd_mem
      replace hx_tilde := (hcut.tilde_image c hc n hnN₁.1.2).mp hx_tilde
      rw [hβ'_eq n hnN₁]
      refine Subset.trans ?_ (hle_α' (ι '' c)).vertexSet_subset
      rw [hbase_eq c hc]
      exact π.p3_subset c (hI_keep hc) ((hcut.bd_cell_iff c hc).mp hdbd) n hx_tilde
    · rw [hβ'_empty x hxN₁]
      exact empty_subset _
  p4_disjoint := by
    intro Φ₁ hΦ₁ Φ₂ hΦ₂ hne x₁ hx₁ x₂ hx₂
    by_cases hx₁N₁ : x₁ ∈ ι '' (cutSideNodes π F I_keep)
    · by_cases hx₂N₁ : x₂ ∈ ι '' (cutSideNodes π F I_keep)
      · obtain ⟨n₁, hn₁, rfl⟩ := hx₁N₁
        obtain ⟨n₂, hn₂, rfl⟩ := hx₂N₁
        rw [hβ'_eq n₁ hn₁, hβ'_eq n₂ hn₂]
        have hx₂_not_Φ₁ : ι n₂ ∉ Φ₁ := by
          intro hmem
          have hEq : Φ₁ = Φ₂ := by
            rcases hΦ₁ with ⟨z₁, _, rfl⟩
            rcases hΦ₂ with ⟨z₂, _, rfl⟩
            exact (connectedComponentIn_eq hmem).trans (connectedComponentIn_eq hx₂.2).symm
          exact hne hEq
        obtain ⟨Θ, hΘ, hn₁Θ, hn₂_cases⟩ := hcut.cuff_sep Φ₁ hΦ₁ n₁ hn₁ hx₁.2 n₂ hn₂ hx₂_not_Φ₁
        have hΦ₂_bd : Φ₂ ⊆ bd S' := by
          rcases hΦ₂ with ⟨z₂, _, rfl⟩
          exact connectedComponentIn_subset (bd S') z₂
        have hn₂_bd : n₂ ∈ bd π.S := (hcut.bd_node_iff n₂ hn₂).mp (hΦ₂_bd hx₂.2)
        rw [disjoint_left]
        intro v hv₁ hv₂
        rcases hn₂_cases with hn₂_not_Θ | ⟨hn₂Θ, a, ha, b, hb, hord⟩
        · exact hn₂_not_Θ (hbp_same_cuff hΘ ⟨hn₁.1.1, hn₁Θ⟩ hn₂.1.1 v
            (Or.inl hv₁) (Or.inl ⟨hn₂_bd, hv₂⟩))
        · exact hbp_sep_Θ hΘ ⟨hn₁.1.1, hn₁Θ⟩ ⟨hn₂.1.1, hn₂Θ⟩ ha hb hord v
            (Or.inl hv₁) (Or.inl hv₂)
      · rw [hβ'_empty x₂ hx₂N₁]
        exact Set.disjoint_empty _
    · rw [hβ'_empty x₁ hx₁N₁]
      exact Set.empty_disjoint _
  p4_notMem := by
    rintro Φ hΦ x₁ hx₁ _ ⟨n₂, ⟨hn₂, hn₂γ⟩, rfl⟩ hx₂_not_Φ hv₁
    by_cases hx₁N₁ : x₁ ∈ ι '' (cutSideNodes π F I_keep)
    · obtain ⟨n₁, hn₁, rfl⟩ := hx₁N₁
      rw [hγ'_eq n₂, hβ'_eq n₁ hn₁] at hv₁
      obtain ⟨Θ, hΘ, hn₁Θ, hn₂_cases⟩ := hcut.cuff_sep Φ hΦ n₁ hn₁ hx₁.2 n₂ hn₂ hx₂_not_Φ
      rcases hn₂_cases with hn₂_not_Θ | ⟨hn₂Θ, a, ha, b, hb, hord⟩
      · exact hn₂_not_Θ (hbp_same_cuff hΘ ⟨hn₁.1.1, hn₁Θ⟩ hn₂.1.1 (π.nodeVertex n₂)
          (Or.inl hv₁) (Or.inr ⟨hn₂γ, rfl⟩))
      · exact hbp_sep_Θ hΘ ⟨hn₁.1.1, hn₁Θ⟩ ⟨hn₂.1.1, hn₂Θ⟩ ha hb hord (π.nodeVertex n₂)
          (Or.inl hv₁) (Or.inr ⟨hn₂γ, rfl⟩)
    · rw [hβ'_empty x₁ hx₁N₁] at hv₁
      exact hv₁
  p5 := by
    intro d hd hdbd v hv ⟨d₂, _, hd₂_ne, hv₂⟩
    have hv_not_abs : v ∉ (π.cellsUnion I_absorb).vertexSet := by
      intro hv_abs
      have hv_keep : v ∈ (π.cellsUnion I_keep).vertexSet := by
        by_cases hd_eq : d = d₀
        · have hd₂_ne_d₀ : d₂ ≠ d₀ := fun h => hd₂_ne (h.trans hd_eq.symm)
          dsimp [cutSideGraph] at hv₂
          rw [ite_eq_right hd₂_ne_d₀] at hv₂
          exact hbase_sub_keep d₂ hv₂
        · dsimp [cutSideGraph] at hv
          rw [ite_eq_right hd_eq] at hv
          exact hbase_sub_keep d hv
      exact eq_empty_iff_forall_notMem.mp hV_disj v ⟨hv_keep, hv_abs⟩
    have hv_base : v ∈ (baseGraph d).vertexSet := by
      dsimp [cutSideGraph] at hv
      split_ifs at hv with h
      · exact hv.resolve_right hv_not_abs
      · exact hv
    have hv₂_base : v ∈ (baseGraph d₂).vertexSet := by
      dsimp [cutSideGraph] at hv₂
      split_ifs at hv₂ with h
      · exact hv₂.resolve_right hv_not_abs
      · exact hv₂
    have hd_mem : d ∈ (fun c => ι '' c) '' I_keep := by
      by_contra hd_not
      rw [hbase_bot d hd_not, π.cellsUnion_empty_vertexSet] at hv_base
      exact hv_base
    have hd₂_mem : d₂ ∈ (fun c => ι '' c) '' I_keep := by
      by_contra hd₂_not
      rw [hbase_bot d₂ hd₂_not, π.cellsUnion_empty_vertexSet] at hv₂_base
      exact hv₂_base
    obtain ⟨c, hc, rfl⟩ := hd_mem
    obtain ⟨c₂, hc₂, rfl⟩ := hd₂_mem
    rw [hbase_eq c hc] at hv_base
    rw [hbase_eq c₂ hc₂] at hv₂_base
    have hc_bd : ¬ (c ∩ bd π.S).Nonempty := mt (hcut.bd_cell_iff c hc).mpr hdbd
    have hc₂_ne : c₂ ≠ c := fun h => hd₂_ne (congrArg _ h)
    obtain ⟨n, ⟨hn_tilde, hnγ⟩, rfl⟩ :=
      π.p5 c (hI_keep hc) hc_bd v hv_base ⟨c₂, hI_keep hc₂, hc₂_ne, hv₂_base⟩
    have hnF : n ∉ F := fun h => eq_empty_iff_forall_notMem.mp hFγ n ⟨h, hnγ⟩
    have hnN₁ : n ∈ cutSideNodes π F I_keep :=
      ⟨⟨π.Γ.tilde_subset_N (hI_keep hc) hn_tilde, hnF⟩, c, hc, hn_tilde⟩
    exact ⟨ι n, ⟨(hcut.tilde_image c hc n hnF).mpr hn_tilde, mem_image_of_mem ι ⟨hnN₁, hnγ⟩⟩,
      hγ'_eq n⟩
  p6 := by
    intro d hd hdbd v hv ⟨d₂, _, hd₂_ne, hv₂⟩
    have hv_not_abs : v ∉ (π.cellsUnion I_absorb).vertexSet := by
      intro hv_abs
      have hv_keep : v ∈ (π.cellsUnion I_keep).vertexSet := by
        by_cases hd_eq : d = d₀
        · have hd₂_ne_d₀ : d₂ ≠ d₀ := fun h => hd₂_ne (h.trans hd_eq.symm)
          dsimp [cutSideGraph] at hv₂
          rw [ite_eq_right hd₂_ne_d₀] at hv₂
          exact hbase_sub_keep d₂ hv₂
        · dsimp [cutSideGraph] at hv
          rw [ite_eq_right hd_eq] at hv
          exact hbase_sub_keep d hv
      exact eq_empty_iff_forall_notMem.mp hV_disj v ⟨hv_keep, hv_abs⟩
    have hv_base : v ∈ (baseGraph d).vertexSet := by
      dsimp [cutSideGraph] at hv
      split_ifs at hv with h
      · exact hv.resolve_right hv_not_abs
      · exact hv
    have hv₂_base : v ∈ (baseGraph d₂).vertexSet := by
      dsimp [cutSideGraph] at hv₂
      split_ifs at hv₂ with h
      · exact hv₂.resolve_right hv_not_abs
      · exact hv₂
    have hd_mem : d ∈ (fun c => ι '' c) '' I_keep := by
      by_contra hd_not
      rw [hbase_bot d hd_not, π.cellsUnion_empty_vertexSet] at hv_base
      exact hv_base
    have hd₂_mem : d₂ ∈ (fun c => ι '' c) '' I_keep := by
      by_contra hd₂_not
      rw [hbase_bot d₂ hd₂_not, π.cellsUnion_empty_vertexSet] at hv₂_base
      exact hv₂_base
    obtain ⟨c, hc, rfl⟩ := hd_mem
    obtain ⟨c₂, hc₂, rfl⟩ := hd₂_mem
    rw [hbase_eq c hc] at hv_base
    rw [hbase_eq c₂ hc₂] at hv₂_base
    have hc_bd : (c ∩ bd π.S).Nonempty := (hcut.bd_cell_iff c hc).mp hdbd
    have hc₂_ne : c₂ ≠ c := fun h => hd₂_ne (congrArg _ h)
    obtain ⟨n, hn_tilde, hvn⟩ :=
      π.p6 c (hI_keep hc) hc_bd v hv_base ⟨c₂, hI_keep hc₂, hc₂_ne, hv₂_base⟩
    have hn_bd : n ∈ π.Γ.N ∩ bd π.S :=
      ⟨π.Γ.tilde_subset_N (hI_keep hc) hn_tilde,
        π.Γ.border_cell_subset_bd (hI_keep hc) hc_bd hn_tilde⟩
    have hnF : n ∉ F := fun h => hbp_F n ⟨h, hn_bd⟩ v hvn
    have hnN₁ : n ∈ cutSideNodes π F I_keep := ⟨⟨hn_bd.1, hnF⟩, c, hc, hn_tilde⟩
    refine ⟨ι n, (hcut.tilde_image c hc n hnF).mpr hn_tilde, ?_⟩
    rw [hβ'_eq n hnN₁, hγ'_eq n, hcut.inj.mem_set_image]
    rcases hvn with hvn | ⟨hnγ, rfl⟩
    · exact Or.inl hvn
    · exact Or.inr ⟨⟨hnN₁, hnγ⟩, rfl⟩
  p7 := by
    intro Φ hΦ x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄ hord v hv₁ hv₃
    have hx₁N₁ : ∃ n₁ ∈ cutSideNodes π F I_keep, x₁ = ι n₁ ∧
        (v ∈ π.borderSet n₁ ∨ (n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁)) := by
      by_cases h : x₁ ∈ ι '' (cutSideNodes π F I_keep)
      · obtain ⟨n₁, hn₁, rfl⟩ := h
        rw [hβ'_eq n₁ hn₁, hγ'_eq n₁, hcut.inj.mem_set_image] at hv₁
        exact ⟨n₁, hn₁, rfl, hv₁.imp_right fun ⟨⟨_, hn₁γ⟩, hEq⟩ => ⟨hn₁γ, hEq⟩⟩
      · rw [hβ'_empty x₁ h] at hv₁
        rcases hv₁ with hv₁ | ⟨⟨n₁, ⟨hn₁, _⟩, rfl⟩, _⟩
        · exact hv₁.elim
        · exact (h ⟨n₁, hn₁, rfl⟩).elim
    have hx₃N₁ : ∃ n₃ ∈ cutSideNodes π F I_keep, x₃ = ι n₃ ∧
        (v ∈ π.borderSet n₃ ∨ (n₃ ∈ π.domγ ∧ v = π.nodeVertex n₃)) := by
      by_cases h : x₃ ∈ ι '' (cutSideNodes π F I_keep)
      · obtain ⟨n₃, hn₃, rfl⟩ := h
        rw [hβ'_eq n₃ hn₃, hγ'_eq n₃, hcut.inj.mem_set_image] at hv₃
        exact ⟨n₃, hn₃, rfl, hv₃.imp_right fun ⟨⟨_, hn₃γ⟩, hEq⟩ => ⟨hn₃γ, hEq⟩⟩
      · rw [hβ'_empty x₃ h] at hv₃
        rcases hv₃ with hv₃ | ⟨⟨n₃, ⟨hn₃, _⟩, rfl⟩, _⟩
        · exact hv₃.elim
        · exact (h ⟨n₃, hn₃, rfl⟩).elim
    obtain ⟨n₁, hn₁, hx₁_eq, hvn₁⟩ := hx₁N₁
    obtain ⟨n₃, hn₃, hx₃_eq, hvn₃⟩ := hx₃N₁
    have hΦ_bd : Φ ⊆ bd S' := by
      rcases hΦ with ⟨z₀, _, rfl⟩
      exact connectedComponentIn_subset (bd S') z₀
    have hn₁_bd : n₁ ∈ bd π.S := (hcut.bd_node_iff n₁ hn₁).mp (hx₁_eq ▸ hΦ_bd hx₁.2)
    have hn₃_bd : n₃ ∈ bd π.S := (hcut.bd_node_iff n₃ hn₃).mp (hx₃_eq ▸ hΦ_bd hx₃.2)
    obtain ⟨Θ, hΘ, hn₁Θ⟩ := exists_cuff_of_mem_bd hn₁_bd
    have hn₃Θ : n₃ ∈ Θ :=
      hbp_same_cuff hΘ ⟨hn₁.1.1, hn₁Θ⟩ hn₃.1.1 v hvn₁
        (hvn₃.imp_left fun h => ⟨hn₃_bd, h⟩)
    rcases hcut.cuff_order Φ hΦ x₁ hx₁ x₂ hx₂ x₃ hx₃ x₄ hx₄ hord
        n₁ hn₁ hx₁_eq n₃ hn₃ hx₃_eq Θ hΘ hn₁Θ hn₃Θ with
      ⟨a, ha, b, hb, hordΘ⟩ |
      ⟨n₂, ⟨hn₂N₁, hn₂Θ⟩, hx₂_eq, b, hb, hordΘ⟩ |
      ⟨n₄, ⟨hn₄N₁, hn₄Θ⟩, hx₄_eq, a, ha, hordΘ⟩
    · exact (hbp_sep_Θ hΘ ⟨hn₁.1.1, hn₁Θ⟩ ⟨hn₃.1.1, hn₃Θ⟩ ha hb hordΘ v hvn₁ hvn₃).elim
    · have hb_mem : b ∈ π.Γ.N ∩ Θ := by
        rcases hb with hbF | ⟨⟨hbN₁, hbΘ⟩, _⟩
        · exact hbF.2
        · exact ⟨hbN₁.1.1, hbΘ⟩
      rcases π.p7 Θ hΘ n₁ ⟨hn₁.1.1, hn₁Θ⟩ n₂ ⟨hn₂N₁.1.1, hn₂Θ⟩ n₃ ⟨hn₃.1.1, hn₃Θ⟩
          b hb_mem hordΘ v hvn₁ hvn₃ with hvn₂ | hvnb
      · left
        rw [hx₂_eq, hβ'_eq n₂ hn₂N₁, hγ'_eq n₂, hcut.inj.mem_set_image]
        exact hvn₂.imp_right fun ⟨hn₂γ, hEq⟩ => ⟨⟨hn₂N₁, hn₂γ⟩, hEq⟩
      · rcases hb with hbF | ⟨⟨hbN₁, _⟩, hx₄_eq⟩
        · have hΘ_bd : Θ ⊆ bd π.S := by
            rcases hΘ with ⟨z₀, _, rfl⟩
            exact connectedComponentIn_subset (bd π.S) z₀
          exact (hbp_F b ⟨hbF.1, hbF.2.1, hΘ_bd hbF.2.2⟩ v hvnb).elim
        · right
          rw [hx₄_eq, hβ'_eq b hbN₁, hγ'_eq b, hcut.inj.mem_set_image]
          exact hvnb.imp_right fun ⟨hbγ, hEq⟩ => ⟨⟨hbN₁, hbγ⟩, hEq⟩
    · have ha_mem : a ∈ π.Γ.N ∩ Θ := by
        rcases ha with haF | ⟨⟨haN₁, haΘ⟩, _⟩
        · exact haF.2
        · exact ⟨haN₁.1.1, haΘ⟩
      rcases π.p7 Θ hΘ n₁ ⟨hn₁.1.1, hn₁Θ⟩ a ha_mem n₃ ⟨hn₃.1.1, hn₃Θ⟩
          n₄ ⟨hn₄N₁.1.1, hn₄Θ⟩ hordΘ v hvn₁ hvn₃ with hvna | hvn₄
      · rcases ha with haF | ⟨⟨haN₁, _⟩, hx₂_eq⟩
        · have hΘ_bd : Θ ⊆ bd π.S := by
            rcases hΘ with ⟨z₀, _, rfl⟩
            exact connectedComponentIn_subset (bd π.S) z₀
          exact (hbp_F a ⟨haF.1, haF.2.1, hΘ_bd haF.2.2⟩ v hvna).elim
        · left
          rw [hx₂_eq, hβ'_eq a haN₁, hγ'_eq a, hcut.inj.mem_set_image]
          exact hvna.imp_right fun ⟨haγ, hEq⟩ => ⟨⟨haN₁, haγ⟩, hEq⟩
      · right
        rw [hx₄_eq, hβ'_eq n₄ hn₄N₁, hγ'_eq n₄, hcut.inj.mem_set_image]
        exact hvn₄.imp_right fun ⟨hn₄γ, hEq⟩ => ⟨⟨hn₄N₁, hn₄γ⟩, hEq⟩

private theorem cutSideCellWarp {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π π' : Portrayal G) {F : Set π.S} {I_keep I_absorb : Set (Set π.S)}
    {ι : π.S → π'.S} (hcut : IsCutSidePainting π.S π.Γ F I_keep π'.S ι π'.Γ)
    (hI_keep : I_keep ⊆ π.Γ.C) (hFγ : F ∩ π.domγ = ∅)
    (hβF : ∀ n ∈ F ∩ (π.Γ.N ∩ bd π.S), π.borderSet n = ∅)
    (hV_disj : (π.cellsUnion I_keep).vertexSet ∩ (π.cellsUnion I_absorb).vertexSet = ∅)
    (baseGraph : Set π'.S → Hypergraph α β) (d₀ : Set π'.S)
    (hbase_eq : ∀ c ∈ I_keep, baseGraph (ι '' c) = π.cellGraph c)
    (hα' : ∀ d, π'.cellGraph d = cutSideGraph π I_absorb baseGraph d₀ d)
    (hβ'_eq : ∀ n ∈ cutSideNodes π F I_keep, π'.borderSet (ι n) = π.borderSet n)
    (hβ'_empty : ∀ x ∉ ι '' cutSideNodes π F I_keep, π'.borderSet x = ∅)
    (hγ'_eq : ∀ n, π'.nodeVertex (ι n) = π.nodeVertex n)
    (hdom' : π'.domγ = ι '' (cutSideNodes π F I_keep ∩ π.domγ)) :
    ∀ d ∈ π'.Γ.C, (d ∩ bd π'.S).Nonempty → π'.cellWarp d ≤ π.warp := by
  classical
  let N₁ := cutSideNodes π F I_keep
  intro d hd hdbd
  by_cases hd_mem : d ∈ (fun c => ι '' c) '' I_keep
  · obtain ⟨c, hc, rfl⟩ := hd_mem
    have hcbd : (c ∩ bd π.S).Nonempty := (hcut.bd_cell_iff c hc).mp hdbd
    rcases hcbd with ⟨x₀, hx₀c, hx₀bd⟩
    have hcbd' : (c ∩ bd π.S).Nonempty := ⟨x₀, hx₀c, hx₀bd⟩
    obtain ⟨Θ, hΘ, hx₀Θ⟩ := exists_cuff_of_mem_bd hx₀bd
    have hcΘ : (c ∩ Θ).Nonempty := ⟨x₀, hx₀c, hx₀Θ⟩
    have hle_c : π'.cellWarp (ι '' c) ≤ π.cellWarp c := by
      rw [π'.cellWarp_le_iff hd hdbd]
      have hc_le : π.CellWarpLE c (π.cellWarp c) := π.cellWarp_spec (hI_keep hc) hcbd'
      have hβ_eq_c : ∀ n ∈ tilde c, π'.borderSet (ι n) = π.borderSet n := by
        intro n hn
        by_cases hnF : n ∈ F
        · have hn_bd : n ∈ π.Γ.N ∩ bd π.S :=
            ⟨π.Γ.tilde_subset_N (hI_keep hc) hn,
              π.Γ.border_cell_subset_bd (hI_keep hc) hcbd' hn⟩
          have hnotN₁ : ι n ∉ ι '' N₁ := by
            rintro ⟨m, hm, hEq⟩
            obtain rfl := hcut.inj hEq
            exact hm.1.2 hnF
          rw [hβ'_empty (ι n) hnotN₁, hβF n ⟨hnF, hn_bd⟩]
        · exact hβ'_eq n ⟨⟨π.Γ.tilde_subset_N (hI_keep hc) hn, hnF⟩, c, hc, hn⟩
      have hbp_eq_c : ∀ n ∈ tilde c, π'.borderPlus (ι n) = π.borderPlus n := by
        intro n hn
        ext v
        simp only [Portrayal.borderPlus, mem_ofPred_eq]
        rw [hdom', hβ_eq_c n hn, hγ'_eq n, hcut.inj.mem_set_image]
        refine or_congr Iff.rfl (and_congr_left fun _ => ⟨fun h => h.2, fun hnγ => ?_⟩)
        have hnF : n ∉ F := fun h => eq_empty_iff_forall_notMem.mp hFγ n ⟨h, hnγ⟩
        exact ⟨⟨⟨π.Γ.tilde_subset_N (hI_keep hc) hn, hnF⟩, c, hc, hn⟩, hnγ⟩
      have hmem_N₁ : ∀ x, (π'.borderPlus x).ncard = π.cellWarp c + 1 → x ∈ ι '' N₁ := by
        intro x hx
        by_contra hxN
        have hemp : π'.borderPlus x = ∅ := by
          ext v
          simp only [Portrayal.borderPlus, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or]
          refine ⟨?_, ?_⟩
          · rw [hβ'_empty x hxN]
            exact notMem_empty v
          · rw [hdom']
            rintro ⟨⟨n, ⟨hnN₁, _⟩, rfl⟩, _⟩
            exact hxN (mem_image_of_mem ι hnN₁)
        rw [hemp, ncard_empty] at hx
        omega
      have hsize : ∀ x ∈ tilde (ι '' c), (π'.borderSet x).ncard ≤ π.cellWarp c := by
        intro x hx
        by_cases hxN : x ∈ ι '' N₁
        · obtain ⟨n, hnN₁, rfl⟩ := hxN
          have hn := (hcut.tilde_image c hc n hnN₁.1.2).mp hx
          obtain ⟨u, v, huv, htilde, -, -, -, -⟩ := π.Γ.border_cell_exists_ends (hI_keep hc) hcbd'
          obtain ⟨m, hm, hmn⟩ : ∃ m ∈ tilde c, n ≠ m := by
            rw [htilde] at hn ⊢
            rcases hn with rfl | rfl
            · exact ⟨v, Or.inr rfl, huv⟩
            · exact ⟨u, Or.inl rfl, huv.symm⟩
          rw [hβ_eq_c n hn]
          exact (hc_le n hn m hm hmn).1
        · rw [hβ'_empty x hxN, ncard_empty]
          exact Nat.zero_le _
      intro x₁ hx₁ x₂ hx₂ hne
      change (π'.borderSet x₁).ncard ≤ π.cellWarp c ∧ (π'.borderSet x₂).ncard ≤ π.cellWarp c ∧
        ((π'.borderPlus x₁).ncard = π.cellWarp c + 1 →
         (π'.borderPlus x₂).ncard = π.cellWarp c + 1 →
          Portrayal.LinkagePairs (π'.cellGraph (ι '' c)).skeleton (π'.borderPlus x₁)
            (π'.borderPlus x₂)
            (π.cellWarp c + 1) (π'.nodeVertex x₁) (π'.nodeVertex x₂))
      refine ⟨hsize x₁ hx₁, hsize x₂ hx₂, fun hbpx₁ hbpx₂ => ?_⟩
      obtain ⟨n₁, hn₁N, rfl⟩ := hmem_N₁ x₁ hbpx₁
      obtain ⟨n₂, hn₂N, rfl⟩ := hmem_N₁ x₂ hbpx₂
      have hn₁ := (hcut.tilde_image c hc n₁ hn₁N.1.2).mp hx₁
      have hn₂ := (hcut.tilde_image c hc n₂ hn₂N.1.2).mp hx₂
      have hne_n : n₁ ≠ n₂ := fun h => hne (congrArg ι h)
      obtain ⟨h1, h2, hlink⟩ := hc_le n₁ hn₁ n₂ hn₂ hne_n
      rw [hbp_eq_c n₁ hn₁] at hbpx₁
      rw [hbp_eq_c n₂ hn₂] at hbpx₂
      rw [hbp_eq_c n₁ hn₁, hbp_eq_c n₂ hn₂]
      rw [hγ'_eq n₁, hγ'_eq n₂]
      have hlink₀ := hlink hbpx₁ hbpx₂
      rw [hα']
      dsimp [cutSideGraph]
      split_ifs
      · rw [hbase_eq c hc]
        have hdisj_c : (π.cellGraph c).vertexSet ∩ (π.cellsUnion I_absorb).vertexSet = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro v ⟨hvc, hv_abs⟩
          exact eq_empty_iff_forall_notMem.mp hV_disj v
            ⟨(π.cellGraph_le_cellsUnion hc (hI_keep hc)).vertexSet_subset hvc, hv_abs⟩
        have hbp₁_sub : π.borderPlus n₁ ⊆ (π.cellGraph c).vertexSet := by
          rintro v (hvβ | ⟨hn₁γ, rfl⟩)
          · exact π.p3_subset c (hI_keep hc) hcbd' n₁ hn₁ hvβ
          · exact π.p2 c (hI_keep hc) n₁ ⟨hn₁, hn₁γ⟩
        exact linkagePairs_sup_of_disjoint (π.cellGraph_le c (hI_keep hc))
          (π.cellsUnion_le I_absorb) hdisj_c hbp₁_sub hlink₀
      · rwa [hbase_eq c hc]
    exact le_trans hle_c
      (le_trans (π.cellWarp_le_warpAt (hI_keep hc) hcΘ) (π.warpAt_le_warp hΘ))
  · have h0 : π'.cellWarp d = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [π'.cellWarp_le_iff hd hdbd]
      intro x₁ hx₁ x₂ hx₂ _
      have hx₁_not : x₁ ∉ ι '' N₁ :=
        disjoint_left.mp (hcut.new_cell_disjoint d hd hd_mem) hx₁
      have hx₂_not : x₂ ∉ ι '' N₁ :=
        disjoint_left.mp (hcut.new_cell_disjoint d hd hd_mem) hx₂
      have hbp₁_empty : π'.borderPlus x₁ = ∅ := by
        ext v
        simp only [Portrayal.borderPlus, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or]
        refine ⟨?_, ?_⟩
        · rw [hβ'_empty x₁ hx₁_not]
          exact notMem_empty v
        · rw [hdom']
          rintro ⟨⟨n, ⟨hnN₁, _⟩, rfl⟩, _⟩
          exact hx₁_not (mem_image_of_mem ι hnN₁)
      change (π'.borderSet x₁).ncard ≤ 0 ∧ (π'.borderSet x₂).ncard ≤ 0 ∧ _
      rw [hβ'_empty x₁ hx₁_not, hβ'_empty x₂ hx₂_not, hbp₁_empty, ncard_empty]
      exact ⟨le_rfl, le_rfl, fun h => by omega⟩
    rw [h0]
    exact Nat.zero_le _

private theorem warp_le_of_cellWarp_le {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π π' : Portrayal G)
    (hcell : ∀ d ∈ π'.Γ.C, (d ∩ bd π'.S).Nonempty → π'.cellWarp d ≤ π.warp) :
    π'.warp ≤ π.warp := by
  by_cases hne' : (cuffs π'.S).Nonempty
  · have hSup_bdd : ∀ Φ ∈ cuffs π'.S, π'.warpAt Φ ≤ π.warp := by
      intro Φ hΦ
      have hΦ_bd : Φ ⊆ bd π'.S := by
        rcases hΦ with ⟨z₀, _, rfl⟩
        exact connectedComponentIn_subset (bd π'.S) z₀
      unfold Portrayal.warpAt
      by_cases hset_ne : {p | ∃ d ∈ π'.Γ.C, (d ∩ Φ).Nonempty ∧ p = π'.cellWarp d}.Nonempty
      · refine csSup_le hset_ne ?_
        rintro p ⟨d, hd, hdΦ, rfl⟩
        exact hcell d hd (hdΦ.mono (inter_subset_inter_right d hΦ_bd))
      · rw [not_nonempty_iff_eq_empty.mp hset_ne, csSup_empty]
        exact Nat.zero_le _
    unfold Portrayal.warp
    rw [ite_eq_left hne']
    obtain ⟨Φ₀, hΦ₀⟩ := hne'
    refine max_le π.one_le_warp (csSup_le ⟨π'.warpAt Φ₀, Φ₀, hΦ₀, rfl⟩ ?_)
    rintro p ⟨Φ, hΦ, rfl⟩
    exact hSup_bdd Φ hΦ
  · unfold Portrayal.warp
    rw [ite_eq_right hne']
    exact π.one_le_warp

/-- Unified portrayal construction for the proofs of (5.3) and (5.4) (pages 172–173):
given a $\mathcal{T}$-central portrayal $\pi$ of $G$, a normal cut along $F$ with
$F \cap \operatorname{dom}(\gamma) = \emptyset$ and $\beta = \emptyset$ on
$F \cap N(\Gamma) \cap \operatorname{bd}(\Sigma)$ partitioning $C(\Gamma)$ into $I_{\text{keep}}$
and $I_{\text{absorb}} = C(\Gamma) \setminus I_{\text{keep}}$ such that $\alpha(I_{\text{absorb}})$
is small relative to $\mathcal{T}$, if the cut side $I_{\text{keep}}$ yields a simpler surface
$S'$ with a painting $\Gamma'$ satisfying `IsCutSidePainting`, then there is a $\mathcal{T}$-central
portrayal $\pi'$ of $G$ on $S'$ that is simpler than $\pi$. -/
theorem Portrayal.exists_simpler_of_isCutSidePainting
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hTangle : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (π : Portrayal G) (hT : π.IsCentral 𝒯)
    {F : Set π.S} (hFγ : F ∩ π.domγ = ∅)
    (hβF : ∀ n ∈ F ∩ (π.Γ.N ∩ bd π.S), π.borderSet n = ∅)
    {I_keep I_absorb : Set (Set π.S)}
    (hI_keep : I_keep ⊆ π.Γ.C) (hI_absorb : I_absorb = π.Γ.C \ I_keep)
    (hsep : ∀ c₁ ∈ I_keep, ∀ c₂ ∈ I_absorb, tilde c₁ ∩ tilde c₂ ⊆ F)
    (hsmall : IsSmallWrt 𝒯 (π.cellsUnion I_absorb))
    {S' : Type} [tS' : TopologicalSpace S'] [connS' : ConnectedSpace
      S']
    (hsS' : IsSurface S') (hsimpS' : IsSimplerThan S' π.S)
    {ι : π.S → S'} {Γ' : Painting S'}
    (hcut : IsCutSidePainting π.S π.Γ F I_keep S' ι Γ') :
    ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.IsSimpler π := by
  classical
  have : ConnectedSpace π.S := π.connected
  have hI_absorb_sub : I_absorb ⊆ π.Γ.C := hI_absorb ▸ sdiff_subset
  have ⟨hsep_G, hV_disj⟩ :=
    π.isSeparation_order_zero_of_normal_cut hFγ hβF hI_keep hI_absorb hsep
  let N₁ := cutSideNodes π F I_keep
  have hcell_eq : ∀ {c₁ c₂ : Set π.S}, ι '' c₁ = ι '' c₂ → c₁ = c₂ :=
    fun h => hcut.inj.image_injective h
  let d₀ : Set S' := hcut.cells_nonempty.some
  have hd₀_mem : d₀ ∈ Γ'.C := hcut.cells_nonempty.some_mem
  let baseGraph : Set S' → Hypergraph α β := fun d =>
    if h : ∃ c ∈ I_keep, d = ι '' c then π.cellGraph h.choose else π.cellsUnion ∅
  have hbase_eq : ∀ c ∈ I_keep, baseGraph (ι '' c) = π.cellGraph c := by
    intro c hc
    have hex : ∃ c₀ ∈ I_keep, ι '' c = ι '' c₀ := ⟨c, hc, rfl⟩
    dsimp [baseGraph]
    rw [dite_eq_left hex]
    exact congrArg π.cellGraph (hcell_eq hex.choose_spec.2).symm
  have hbase_bot : ∀ d, d ∉ (fun c => ι '' c) '' I_keep → baseGraph d = π.cellsUnion ∅ := by
    intro d hd
    have hnot : ¬ ∃ c ∈ I_keep, d = ι '' c := fun ⟨c, hc, hEq⟩ => hd ⟨c, hc, hEq.symm⟩
    dsimp [baseGraph]
    rw [dite_eq_right hnot]
  have hbase_le : ∀ d, baseGraph d ≤ G := by
    intro d
    by_cases hd : ∃ c ∈ I_keep, d = ι '' c
    · obtain ⟨c, hc, rfl⟩ := hd
      rw [hbase_eq c hc]
      exact π.cellGraph_le c (hI_keep hc)
    · rw [hbase_bot d (fun ⟨c, hc, hEq⟩ => hd ⟨c, hc, hEq.symm⟩)]
      exact π.cellsUnion_le ∅
  have hbase_sub_keep : ∀ d, (baseGraph d).vertexSet ⊆ (π.cellsUnion I_keep).vertexSet := by
    intro d v hv
    by_cases hd : ∃ c ∈ I_keep, d = ι '' c
    · obtain ⟨c, hc, rfl⟩ := hd
      rw [hbase_eq c hc] at hv
      exact (π.cellGraph_le_cellsUnion hc (hI_keep hc)).vertexSet_subset hv
    · rw [hbase_bot d (fun ⟨c, hc, hEq⟩ => hd ⟨c, hc, hEq.symm⟩),
        π.cellsUnion_empty_vertexSet] at hv
      exact hv.elim
  let α' : Set S' → Hypergraph α β := fun d =>
    if d = d₀ then baseGraph d ∪ π.cellsUnion I_absorb else baseGraph d
  have hle_α' : ∀ d, baseGraph d ≤ α' d := by
    intro d
    dsimp [α']
    split_ifs
    · exact le_union_left (hbase_le d) (π.cellsUnion_le I_absorb)
    · exact le_rfl
  let β' : S' → Set α := fun x =>
    if h : ∃ n ∈ N₁, x = ι n then π.borderSet h.choose else ∅
  have hβ'_eq : ∀ n ∈ N₁, β' (ι n) = π.borderSet n := by
    intro n hn
    have hex : ∃ m ∈ N₁, ι n = ι m := ⟨n, hn, rfl⟩
    dsimp [β']
    rw [dite_eq_left hex]
    exact congrArg π.borderSet (hcut.inj hex.choose_spec.2).symm
  have hβ'_empty : ∀ x ∉ ι '' N₁, β' x = ∅ := by
    intro x hx
    have hnot : ¬ ∃ n ∈ N₁, x = ι n := fun ⟨n, hn, hEq⟩ => hx ⟨n, hn, hEq.symm⟩
    dsimp [β']
    rw [dite_eq_right hnot]
  let γ' : S' → α := fun x =>
    if h : ∃ n, x = ι n then π.nodeVertex h.choose
    else π.nodeVertex (Classical.arbitrary π.S)
  have hγ'_eq : ∀ n : π.S, γ' (ι n) = π.nodeVertex n := by
    intro n
    have hex : ∃ m, ι n = ι m := ⟨n, rfl⟩
    dsimp [γ']
    rw [dite_eq_left hex]
    exact congrArg π.nodeVertex (hcut.inj hex.choose_spec).symm
  have hbp_F : ∀ n ∈ F ∩ (π.Γ.N ∩ bd π.S),
      ∀ v, ¬ (v ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n)) := by
    rintro n ⟨hnF, hnN, hnbd⟩ v (hvn | ⟨hnγ, _⟩)
    · rw [hβF n ⟨hnF, hnN, hnbd⟩] at hvn
      exact hvn
    · exact eq_empty_iff_forall_notMem.mp hFγ n ⟨hnF, hnγ⟩
  have hbp_sep_Θ : ∀ {Θ : Set π.S}, Θ ∈ cuffs π.S →
      ∀ {n₁ n₂ a b : π.S}, n₁ ∈ π.Γ.N ∩ Θ → n₂ ∈ π.Γ.N ∩ Θ →
      a ∈ F ∩ (π.Γ.N ∩ Θ) → b ∈ F ∩ (π.Γ.N ∩ Θ) →
      GM19.InOrderOn Θ n₁ a n₂ b →
      ∀ v, (v ∈ π.borderSet n₁ ∨ (n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁)) →
        (v ∈ π.borderSet n₂ ∨ (n₂ ∈ π.domγ ∧ v = π.nodeVertex n₂)) → False := by
    intro Θ hΘ n₁ n₂ a b hn₁ hn₂ ha hb hord v hv₁ hv₂
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    rcases π.p7 Θ hΘ n₁ hn₁ a ha.2 n₂ hn₂ b hb.2 hord v hv₁ hv₂ with hva | hvb
    · exact hbp_F a ⟨ha.1, ha.2.1, hΘ_bd ha.2.2⟩ v hva
    · exact hbp_F b ⟨hb.1, hb.2.1, hΘ_bd hb.2.2⟩ v hvb
  have hbp_same_cuff : ∀ {n₁ n₂ : π.S} {Θ : Set π.S}, Θ ∈ cuffs π.S →
      n₁ ∈ π.Γ.N ∩ Θ → n₂ ∈ π.Γ.N →
      ∀ v, (v ∈ π.borderSet n₁ ∨ (n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁)) →
        ((n₂ ∈ bd π.S ∧ v ∈ π.borderSet n₂) ∨ (n₂ ∈ π.domγ ∧ v = π.nodeVertex n₂)) →
        n₂ ∈ Θ := by
    intro n₁ n₂ Θ hΘ hn₁ hn₂N v hv₁ hv₂
    by_contra hn₂Θ
    rcases hv₁ with hv₁β | ⟨hn₁γ, rfl⟩
    · rcases hv₂ with ⟨hn₂bd, hv₂β⟩ | ⟨hn₂γ, rfl⟩
      · obtain ⟨Θ₂, hΘ₂, hn₂Θ₂⟩ := exists_cuff_of_mem_bd hn₂bd
        have hne : Θ ≠ Θ₂ := fun hEq => hn₂Θ (hEq ▸ hn₂Θ₂)
        exact (π.p4_disjoint Θ hΘ Θ₂ hΘ₂ hne n₁ hn₁ n₂ ⟨hn₂N, hn₂Θ₂⟩).le_bot ⟨hv₁β, hv₂β⟩
      · exact π.p4_notMem Θ hΘ n₁ hn₁ n₂ hn₂γ hn₂Θ hv₁β
    · rcases hv₂ with ⟨hn₂bd, hv₂β⟩ | ⟨hn₂γ, hEq⟩
      · obtain ⟨Θ₂, hΘ₂, hn₂Θ₂⟩ := exists_cuff_of_mem_bd hn₂bd
        have hn₁_not_Θ₂ : n₁ ∉ Θ₂ := by
          intro hn₁Θ₂
          have hEqΘ : Θ = Θ₂ := by
            rcases hΘ with ⟨x₁, _, rfl⟩
            rcases hΘ₂ with ⟨x₂, _, rfl⟩
            exact (connectedComponentIn_eq hn₁.2).trans (connectedComponentIn_eq hn₁Θ₂).symm
          exact hn₂Θ (hEqΘ ▸ hn₂Θ₂)
        exact π.p4_notMem Θ₂ hΘ₂ n₂ ⟨hn₂N, hn₂Θ₂⟩ n₁ hn₁γ hn₁_not_Θ₂ hv₂β
      · rw [← π.nodeVertex_injOn hn₁γ hn₂γ hEq] at hn₂Θ
        exact hn₂Θ hn₁.2
  let π' : Portrayal G :=
    assembleCutSidePortrayal π hsS' hcut hI_keep hI_absorb hV_disj hFγ baseGraph d₀ hd₀_mem
      hbase_eq hbase_bot hbase_le hbase_sub_keep hle_α' β' γ' hβ'_eq hβ'_empty hγ'_eq
      hbp_F hbp_sep_Θ hbp_same_cuff
  have hπ'_central : π'.IsCentral 𝒯 := by
    change ∀ d ∈ Γ'.C, IsSmallWrt 𝒯 (α' d)
    intro d _
    have hbase_small : IsSmallWrt 𝒯 (baseGraph d) := by
      dsimp [baseGraph]
      split_ifs with hd
      · exact hT hd.choose (hI_keep hd.choose_spec.1)
      · exact π.isSmallWrt_cellsUnion_empty hTangle hθ
    dsimp [α']
    by_cases hd₀_eq : d = d₀
    · rw [ite_eq_left hd₀_eq]
      have hatt_abs_empty : attachments G (π.cellsUnion I_absorb) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        have hsub := attachments_subset_inter_of_isSeparation hsep_G.symm hv
        rw [inter_vertexSet, Set.inter_comm, hV_disj] at hsub
        exact hsub
      have hatt_lt : (attachments G (baseGraph d ∪ π.cellsUnion I_absorb)).ncard < θ := by
        have hsub : attachments G (baseGraph d ∪ π.cellsUnion I_absorb) ⊆
            attachments G (baseGraph d) := by
          refine Subset.trans attachments_union_subset ?_
          rw [hatt_abs_empty, union_empty]
        exact (ncard_le_ncard hsub attachments_finite).trans_lt
          (hbase_small.ncard_attachments_lt hTangle)
      exact hbase_small.union hTangle hsmall hatt_lt
    · rw [ite_eq_right hd₀_eq]
      exact hbase_small
  have hcellWarp_le : ∀ d ∈ Γ'.C, (d ∩ bd S').Nonempty → π'.cellWarp d ≤ π.warp :=
    cutSideCellWarp π π' hcut hI_keep hFγ hβF hV_disj baseGraph d₀ hbase_eq
      (fun _ => rfl) hβ'_eq hβ'_empty hγ'_eq rfl
  exact ⟨π', hπ'_central, Or.inl ⟨hsimpS', warp_le_of_cellWarp_le π π' hcellWarp_le⟩⟩

/-- Pure surface-and-painting topological cutting statement for (5.3) (page 172):
given a connected compact surface $\Sigma$, a painting $\Gamma$ in $\Sigma$, and a $\Gamma$-normal
$I$-arc $F \subseteq \Sigma$ with ends $n_1, n_2$ such that $F \cap \operatorname{bd}(\Sigma) =
\{n_1, n_2\}$ and $\tilde{c} \cap F = \emptyset$ for every internal cell $c \in C(\Gamma)$, cutting
$\Sigma$ along $F$ either:
(1) produces a connected simpler surface $\Sigma_0$ carrying a cut-side painting for the full cell
set $C(\Gamma)$ with at least one cuff, or
(2) partitions $C(\Gamma)$ into $I_1$ and $I_2 = C(\Gamma) \setminus I_1$ (separated by $F$) such
that for each side $(I_{\text{keep}}, I_{\text{absorb}}) \in \{(I_1, I_2), (I_2, I_1)\}$, either
$I_{\text{absorb}}$ is the set of cells in a closed disc $\Delta \subseteq \Sigma$ with
$F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$, or the surface
$\Sigma'$ of side $I_{\text{keep}}$ is simpler than $\Sigma$, has at least one cuff, and carries a
cut-side painting for $I_{\text{keep}}$. -/
@[expose] def CutNormalIArcPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [CompactSpace S] [T2Space S] [ConnectedSpace S],
    IsSurface S → ∀ (Γ : Painting S) (F : Set S) (n₁ n₂ : S),
    Γ.IsNormal F → IsLineWithEnds F n₁ n₂ → F ∩ bd S = {n₁, n₂} →
    (∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F) →
    (∃ (S₀ : Type) (_ : TopologicalSpace S₀) (_ : CompactSpace S₀) (_ : T2Space S₀)
        (_ : ConnectedSpace S₀) (ι₀ : S → S₀) (Γ₀ : Painting S₀),
      IsSurface S₀ ∧ IsSimplerThan S₀ S ∧ (cuffs S₀).Nonempty ∧
      IsCutSidePainting S Γ F Γ.C S₀ ι₀ Γ₀) ∨
    (∃ I₁ I₂ : Set (Set S),
      I₁ ⊆ Γ.C ∧ I₂ = Γ.C \ I₁ ∧
      (∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ ⊆ F) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
          {c ∈ Γ.C | c ⊆ Δ} = I₁) ∨
       (∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧ (cuffs S').Nonempty ∧
          IsCutSidePainting S Γ F I₂ S' ι Γ')) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
          {c ∈ Γ.C | c ⊆ Δ} = I₂) ∨
       (∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧ (cuffs S').Nonempty ∧
          IsCutSidePainting S Γ F I₁ S' ι Γ')))

/-- Pure surface-and-painting topological cutting statement for (5.4) (page 173):
given a connected compact surface $\Sigma$, a painting $\Gamma$ in $\Sigma$, and a $\Gamma$-normal
$O$-arc $F \subseteq \Sigma$ such that $\tilde{c} \cap F = \emptyset$ for every internal cell
$c \in C(\Gamma)$, diverting $F$ around $F \cap \operatorname{bd}(\Sigma)$ and cutting $\Sigma$
along $F$ (pasting discs onto the resulting new cuffs) either:
(1) produces a connected simpler surface $\hat{\Sigma}_0$ carrying a cut-side painting for the full
cell set $C(\Gamma)$ (whenever $C(\Gamma)$ is nonempty), or
(2) partitions $C(\Gamma)$ into $I_1$ and $I_2 = C(\Gamma) \setminus I_1$ (separated by
$F \cap \operatorname{bd}(\Sigma) = \emptyset$ after diverting) such that for each side
$(I_{\text{keep}}, I_{\text{absorb}}) \in \{(I_1, I_2), (I_2, I_1)\}$ with $I_{\text{keep}}$
nonempty, either $I_{\text{absorb}}$ is the set of cells in a closed disc $\Delta \subseteq \Sigma$
with $\operatorname{bd}(\Delta) = F$, or the capped surface $\hat{\Sigma}'$ of side
$I_{\text{keep}}$
is simpler than $\Sigma$ and carries a cut-side painting for $I_{\text{keep}}$. -/
@[expose] def CutNormalOArcPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [CompactSpace S] [T2Space S] [ConnectedSpace S],
    IsSurface S → ∀ (Γ : Painting S) (F : Set S),
    Γ.IsNormal F → IsOArc F →
    (∀ c ∈ Γ.C, Γ.IsInternalCell c → Disjoint (tilde c) F) →
    (Γ.C.Nonempty ∧
      ∃ (S₀ : Type) (_ : TopologicalSpace S₀) (_ : CompactSpace S₀) (_ : T2Space S₀)
        (_ : ConnectedSpace S₀) (ι₀ : S → S₀) (Γ₀ : Painting S₀),
      IsSurface S₀ ∧ IsSimplerThan S₀ S ∧
      IsCutSidePainting S Γ ∅ Γ.C S₀ ι₀ Γ₀) ∨
    (∃ I₁ I₂ : Set (Set S),
      I₁ ⊆ Γ.C ∧ I₂ = Γ.C \ I₁ ∧
      (∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ = ∅) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ {c ∈ Γ.C | c ⊆ Δ} = I₁) ∨
       (I₂.Nonempty →
         ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧
          IsCutSidePainting S Γ ∅ I₂ S' ι Γ')) ∧
      ((∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ {c ∈ Γ.C | c ⊆ Δ} = I₂) ∨
       (I₁.Nonempty →
         ∃ (S' : Type) (_ : TopologicalSpace S') (_ : CompactSpace S') (_ : T2Space S')
            (_ : ConnectedSpace S') (ι : S → S') (Γ' : Painting S'),
          IsSurface S' ∧ IsSimplerThan S' S ∧
          IsCutSidePainting S Γ ∅ I₁ S' ι Γ')))

end GraphMinor.GM17

end
