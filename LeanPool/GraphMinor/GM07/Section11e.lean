/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Graph Minors VII, (11.3): Pushing a Closed Curve Out of the Interior of a Closed Disc

This file proves (11.3) of Robertson and Seymour, *Graph Minors VII. Disjoint paths on a surface*
(pages 249–251):

- `disc_interior_curve_homotopy` / `theorem_11_3`: Let `S` be a surface, `Δ ⊆ S` be a closed disc,
  and `Y ⊆ S` be such that `Y ∩ discBd Δ` is arc-connected. Any continuous map
  `φ : C(Circle, S)` with `range φ ⊆ Y ∪ (Δ \ discBd Δ)` (with `(Y ∩ discBd Δ).Nonempty` in the
  degenerate case `range φ ⊆ Δ \ discBd Δ`) is homotopic in `S` to a map `ψ : C(Circle, S)` with
  `range ψ ⊆ Y` and `range ψ ⊆ range φ ∪ discBd Δ`. In particular, if `Y` is flat then so is
  `Y ∪ (Δ \ discBd Δ)` (`isFlat_union_disc_diff_discBd`).
-/

public section

namespace GraphMinor.GM07

open Set Function Topology Metric Filter GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Homotopy in a Closed Disc to a Constant Curve -/

private lemma isPreconnected_of_isArcConnected {Z : Set S} (hZ : IsArcConnected Z) :
    IsPreconnected Z := by
  rcases Z.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact isPreconnected_empty
  · have hpc : IsPathConnected Z := by
      refine ⟨x₀, hx₀, fun {y} hy => ?_⟩
      rcases eq_or_ne x₀ y with rfl | hne
      · exact JoinedIn.refl hx₀
      · obtain ⟨L, hLZ, f, hf0, hf1⟩ := hZ x₀ hx₀ y hy hne
        let p : Path x₀ y :=
          { toContinuousMap := ⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩
            source' := hf0
            target' := hf1 }
        exact ⟨p, fun t => hLZ (f t).2⟩
    exact hpc.isConnected.isPreconnected

/-- Any closed curve `φ : C(Circle, S)` whose range is contained in a closed disc `Δ ⊆ S` is
homotopic in `Δ` (and hence in `univ`) to the constant curve at any point `y₀ ∈ Δ`. -/
private lemma closedCurvesHomotopicIn_const_of_range_subset_disc
    {Δ : Set S} (hΔ : IsClosedDisc Δ) {y₀ : S} (hy₀ : y₀ ∈ Δ)
    (φ : C(Circle, S)) (hφ : range φ ⊆ Δ) :
    ClosedCurvesHomotopicIn univ φ (ContinuousMap.const Circle y₀) := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hφΔ : ∀ z : Circle, φ z ∈ Δ := fun z => hφ (mem_range_self z)
  have hcomb_mem : ∀ p : Circle × unitInterval,
      (1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h y₀ ∈ closedBall (0 : ℂ) 1 := by
    intro p
    exact convex_closedBall (0 : ℂ) 1 (c.hm (hφΔ p.1)) (c.hm hy₀)
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let L : Circle × unitInterval → ℂ :=
    fun p => (1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h y₀
  have hL_cont : Continuous L := by
    have hhφ : Continuous (fun z : Circle => h (φ z)) :=
      c.hc.comp_continuous φ.continuous hφΔ
    have ht : Continuous (fun p : Circle × unitInterval => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub ht).smul (hhφ.comp continuous_fst)).add
      (ht.smul continuous_const)
  have hΘ_cont : Continuous (fun p : Circle × unitInterval => g (L p)) :=
    c.gc.comp_continuous hL_cont hcomb_mem
  refine ⟨⟨fun p => g (L p), hΘ_cont⟩, fun _ => mem_univ _, fun z => ?_, fun z => ?_⟩
  · change g ((1 - (0 : ℝ)) • h (φ z) + (0 : ℝ) • h y₀) = φ z
    simp [c.gh (hφΔ z)]
  · change g ((1 - (1 : ℝ)) • h (φ z) + (1 : ℝ) • h y₀) = y₀
    simp [c.gh hy₀]

/-! ## 2. Boundary Arc Family on `Circle` in a Suitable Chart of `Δ` -/

/-- For a closed disc `Δ ⊆ S` and `Y ⊆ S` such that `Y ∩ discBd Δ` is arc-connected, there exist a
chart `IsChart Δ h g` and a family of arcs `arcBetween : Circle → Circle → unitInterval → Circle`
such that:
1. For all `w₁, w₂ : Circle`, `arcBetween w₁ w₂` is continuous from `w₁` to `w₂`.
2. Whenever `g w₁, g w₂ ∈ Y ∩ discBd Δ`, the entire arc `arcBetween w₁ w₂` maps under `g` into
   `Y ∩ discBd Δ`.
3. For every `w₀` with `g w₀ ∈ Y ∩ discBd Δ` and every neighborhood `V ∈ 𝓝 w₀`, there is a
   neighborhood `W ∈ 𝓝 w₀` such that `arcBetween w₁ w₂ τ ∈ V` for all `w₁, w₂ ∈ W` and all
   `τ : unitInterval`. -/
private lemma exists_chart_and_arcBetween
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ)) :
    ∃ (h : S → ℂ) (g : ℂ → S) (_c : IsChart Δ h g)
      (arcBetween : Circle → Circle → unitInterval → Circle),
      (∀ w₁ w₂ : Circle, Continuous (arcBetween w₁ w₂)) ∧
      (∀ w₁ w₂ : Circle, arcBetween w₁ w₂ 0 = w₁ ∧ arcBetween w₁ w₂ 1 = w₂) ∧
      (∀ w₁ w₂ : Circle, g (w₁ : ℂ) ∈ Y ∩ discBd Δ → g (w₂ : ℂ) ∈ Y ∩ discBd Δ →
        ∀ τ : unitInterval, g ((arcBetween w₁ w₂ τ : Circle) : ℂ) ∈ Y ∩ discBd Δ) ∧
      (∀ w₀ : Circle, g (w₀ : ℂ) ∈ Y ∩ discBd Δ → ∀ V ∈ 𝓝 w₀,
        ∃ W ∈ 𝓝 w₀, ∀ w₁ ∈ W, ∀ w₂ ∈ W, ∀ τ : unitInterval, arcBetween w₁ w₂ τ ∈ V) := by
  have : T2Space S := hS.2.1
  by_cases hbd_sub : discBd Δ ⊆ Y
  · obtain ⟨h, g, c⟩ := hΔ.exists_isChart
    let arcBetween : Circle → Circle → unitInterval → Circle :=
      fun w₁ w₂ τ => w₁ * Circle.exp ((τ : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ))
    refine ⟨h, g, c, arcBetween, ?_, ?_, ?_, ?_⟩
    · intro w₁ w₂
      dsimp [arcBetween]
      fun_prop
    · intro w₁ w₂
      constructor
      · change w₁ * Circle.exp ((0 : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ)) = w₁
        simp
      · change w₁ * Circle.exp ((1 : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ)) = w₂
        rw [one_mul, Circle.exp_arg, mul_comm w₁, inv_mul_cancel_right]
    · intro w₁ w₂ _ _ τ
      have hbd_mem : g ((arcBetween w₁ w₂ τ : Circle) : ℂ) ∈ discBd Δ := by
        rw [← c.g_sphere]
        exact mem_image_of_mem g (arcBetween w₁ w₂ τ).2
      exact ⟨hbd_sub hbd_mem, hbd_mem⟩
    · intro w₀ _ V hV
      have hmul_cont : ContinuousAt (fun p : Circle × Circle => p.1 * p.2) (w₀, 1) :=
        continuous_mul.continuousAt
      have hmul_eq : w₀ * (1 : Circle) = w₀ := mul_one w₀
      obtain ⟨U₁, hU₁, U₂, hU₂, hU_sub⟩ :=
        mem_nhds_prod_iff.mp (hmul_cont (hmul_eq.symm ▸ hV))
      have hexp_cont : ContinuousAt Circle.exp (0 : ℝ) := Circle.exp.continuous.continuousAt
      have hexp_zero : Circle.exp 0 = 1 := Circle.exp_zero
      obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
        Metric.mem_nhds_iff.mp (hexp_cont (hexp_zero.symm ▸ hU₂))
      have h1_slit : ((1 : Circle) : ℂ) ∈ Complex.slitPlane := by
        simp [Complex.one_mem_slitPlane]
      have harg_cont : ContinuousAt (fun u : Circle => Complex.arg (u : ℂ)) 1 :=
        (Complex.continuousAt_arg h1_slit).comp continuous_subtype_val.continuousAt
      have harg_one : Complex.arg ((1 : Circle) : ℂ) = 0 := by simp
      have hdiv_cont : ContinuousAt (fun p : Circle × Circle => p.2 * p.1⁻¹) (w₀, w₀) :=
        (continuous_snd.mul (continuous_fst.inv)).continuousAt
      have hdiv_eq : w₀ * w₀⁻¹ = 1 := mul_inv_cancel w₀
      have harg_cont' : ContinuousAt (fun u : Circle => Complex.arg (u : ℂ)) (w₀ * w₀⁻¹) := by
        rw [hdiv_eq]
        exact harg_cont
      have hcomp_cont : ContinuousAt
          ((fun u : Circle => Complex.arg (u : ℂ)) ∘ (fun p : Circle × Circle => p.2 * p.1⁻¹))
          (w₀, w₀) :=
        ContinuousAt.comp harg_cont' hdiv_cont
      have hball_nhds : Metric.ball (0 : ℝ) δ ∈ 𝓝 (Complex.arg ((w₀ * w₀⁻¹ : Circle) : ℂ)) := by
        rw [hdiv_eq, harg_one]
        exact Metric.ball_mem_nhds 0 hδ_pos
      obtain ⟨W₁, hW₁, W₂, hW₂, hW_sub⟩ :=
        mem_nhds_prod_iff.mp (hcomp_cont hball_nhds)
      refine ⟨U₁ ∩ W₁ ∩ W₂, Filter.inter_mem (Filter.inter_mem hU₁ hW₁) hW₂,
        fun w₁ hw₁ w₂ hw₂ τ => ?_⟩
      have hw₁U₁ : w₁ ∈ U₁ := hw₁.1.1
      have hw₁W₁ : w₁ ∈ W₁ := hw₁.1.2
      have hw₂W₂ : w₂ ∈ W₂ := hw₂.2
      have hmem_W : (w₁, w₂) ∈ W₁ ×ˢ W₂ := ⟨hw₁W₁, hw₂W₂⟩
      have harg_lt : |Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ)| < δ := by
        simpa [Real.dist_eq] using hW_sub hmem_W
      have hτ_lt : |(τ : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ)| < δ := by
        rw [abs_mul, abs_of_nonneg τ.2.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) τ.2.2).trans_lt harg_lt
      have hexp_mem : Circle.exp ((τ : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ)) ∈ U₂ := by
        apply hδ_sub
        simpa [Real.dist_eq] using hτ_lt
      have hmem_U : (w₁, Circle.exp ((τ : ℝ) * Complex.arg ((w₂ * w₁⁻¹ : Circle) : ℂ))) ∈
          U₁ ×ˢ U₂ := ⟨hw₁U₁, hexp_mem⟩
      exact hU_sub hmem_U
  · obtain ⟨hw, hw_bd, hwY⟩ : ∃ w ∈ discBd Δ, w ∉ Y := not_subset.mp hbd_sub
    obtain ⟨h₀, g₀, c₀⟩ := hΔ.exists_isChart
    have hmemS : ∀ {h : S → ℂ} {g : ℂ → S}, IsChart Δ h g → ∀ {x}, x ∈ discBd Δ → ‖h x‖ = 1 :=
      fun c x hx => mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem _ hx)
    have hcis : ∀ {z : ℂ}, ‖z‖ = 1 → cis' (Complex.arg z) = z := fun {z} hz => by
      have := Complex.norm_mul_exp_arg_mul_I z
      rw [hz] at this
      simpa [cis'] using this
    have hvn : ‖h₀ hw‖ = 1 := hmemS c₀ hw_bd
    let ρ : ℝ := Complex.arg (h₀ hw) + Real.pi
    have c₁ : IsChart Δ (fun x => cis' (-ρ) * h₀ x) (fun z => g₀ (cis' ρ * z)) := c₀.rotate ρ
    let h₁ : S → ℂ := fun x => cis' (-ρ) * h₀ x
    let g₁ : ℂ → S := fun z => g₀ (cis' ρ * z)
    have hw1 : h₁ hw = -1 := by
      change cis' (-ρ) * h₀ hw = -1
      conv_lhs => rw [← hcis hvn]
      rw [cis'_mul]
      have : -ρ + Complex.arg (h₀ hw) = -Real.pi := by ring
      rw [this, cis']
      simp [Complex.exp_neg]
    have hg₁_neg1 : g₁ (-1 : ℂ) = hw := by
      rw [← hw1]
      exact c₁.gh (discBd_subset Δ hw_bd)
    let A_Y : Set Circle := {w : Circle | g₁ (w : ℂ) ∈ Y ∩ discBd Δ}
    have hneg1_notMem : (-1 : Circle) ∉ A_Y := by
      intro hmem
      change g₁ ((-1 : Circle) : ℂ) ∈ Y ∩ discBd Δ at hmem
      simp only [Circle.coe_neg, Circle.coe_one, hg₁_neg1] at hmem
      exact hwY hmem.1
    have hslit : ∀ w ∈ A_Y, (w : ℂ) ∈ Complex.slitPlane := by
      intro w hwA
      rw [Complex.mem_slitPlane_iff_arg]
      refine ⟨fun he => hneg1_notMem ?_, Circle.coe_ne_zero w⟩
      have h1 : Circle.exp (Complex.arg (w : ℂ)) = w := Circle.exp_arg w
      have hpi : Circle.exp Real.pi = -1 :=
        Circle.ext (by simp [Circle.coe_exp, Complex.exp_pi_mul_I])
      rw [he, hpi] at h1
      exact h1 ▸ hwA
    have hA_Y_pre : IsPreconnected A_Y := by
      have hpre : IsPreconnected (Y ∩ discBd Δ) := isPreconnected_of_isArcConnected hY_arc
      have hh₁_cont : ContinuousOn h₁ (Y ∩ discBd Δ) :=
        c₁.hc.mono (inter_subset_right.trans (discBd_subset Δ))
      have hh₁_pre : IsPreconnected (h₁ '' (Y ∩ discBd Δ)) := hpre.image h₁ hh₁_cont
      have hcoe_eq : Subtype.val '' A_Y = h₁ '' (Y ∩ discBd Δ) := by
        ext z
        constructor
        · rintro ⟨w, hwA, rfl⟩
          exact ⟨g₁ (w : ℂ), hwA, c₁.hg (sphere_subset_closedBall w.2)⟩
        · rintro ⟨x, hxY, rfl⟩
          have hz_sph : h₁ x ∈ sphere (0 : ℂ) 1 := by
            rw [← c₁.bd]
            exact mem_image_of_mem h₁ hxY.2
          let w : Circle := ⟨h₁ x, hz_sph⟩
          refine ⟨w, ?_, rfl⟩
          change g₁ (h₁ x) ∈ Y ∩ discBd Δ
          have hgh : g₁ (h₁ x) = x := c₁.gh (discBd_subset Δ hxY.2)
          rw [hgh]
          exact hxY
      exact (IsInducing.subtypeVal.isPreconnected_image).mp (hcoe_eq ▸ hh₁_pre)
    have harg_contOn : ContinuousOn (fun w : Circle => Complex.arg (w : ℂ)) A_Y := by
      intro w hwA
      exact ((Complex.continuousAt_arg (hslit w hwA)).comp
        continuous_subtype_val.continuousAt).continuousWithinAt
    have hJ_ord : OrdConnected ((fun w : Circle => Complex.arg (w : ℂ)) '' A_Y) :=
      (hA_Y_pre.image _ harg_contOn).ordConnected
    let arcBetween : Circle → Circle → unitInterval → Circle :=
      fun w₁ w₂ τ => Circle.exp ((1 - (τ : ℝ)) * Complex.arg (w₁ : ℂ) + (τ : ℝ) * Complex.arg
        (w₂ : ℂ))
    refine ⟨h₁, g₁, c₁, arcBetween, ?_, ?_, ?_, ?_⟩
    · intro w₁ w₂
      dsimp [arcBetween]
      fun_prop
    · intro w₁ w₂
      constructor
      · change Circle.exp ((1 - (0 : ℝ)) * Complex.arg (w₁ : ℂ) + (0 : ℝ) * Complex.arg (w₂ : ℂ))
        = w₁
        simp [Circle.exp_arg]
      · change Circle.exp ((1 - (1 : ℝ)) * Complex.arg (w₁ : ℂ) + (1 : ℝ) * Complex.arg (w₂ : ℂ))
        = w₂
        simp [Circle.exp_arg]
    · intro w₁ w₂ hw₁ hw₂ τ
      have hw₁A : w₁ ∈ A_Y := hw₁
      have hw₂A : w₂ ∈ A_Y := hw₂
      have hmem_seg : (1 - (τ : ℝ)) * Complex.arg (w₁ : ℂ) + (τ : ℝ) * Complex.arg (w₂ : ℂ) ∈
          uIcc (Complex.arg (w₁ : ℂ)) (Complex.arg (w₂ : ℂ)) :=
        segment_subset_uIcc (x := Complex.arg (w₁ : ℂ)) (y := Complex.arg (w₂ : ℂ))
          ⟨1 - (τ : ℝ), (τ : ℝ), sub_nonneg.mpr τ.2.2, τ.2.1, sub_add_cancel 1 (τ : ℝ), rfl⟩
      have hmem_J : (1 - (τ : ℝ)) * Complex.arg (w₁ : ℂ) + (τ : ℝ) * Complex.arg (w₂ : ℂ) ∈
          (fun w : Circle => Complex.arg (w : ℂ)) '' A_Y :=
        hJ_ord.uIcc_subset (mem_image_of_mem _ hw₁A) (mem_image_of_mem _ hw₂A) hmem_seg
      obtain ⟨w, hwA, hw_eq⟩ := hmem_J
      have hexp_eq : arcBetween w₁ w₂ τ = w := by
        change Circle.exp ((1 - (τ : ℝ)) * Complex.arg (w₁ : ℂ) + (τ : ℝ) * Complex.arg (w₂ : ℂ))
          = w
        rw [← hw_eq, Circle.exp_arg]
      rw [hexp_eq]
      exact hwA
    · intro w₀ hw₀ V hV
      have hexp_cont : ContinuousAt Circle.exp (Complex.arg (w₀ : ℂ)) :=
        Circle.exp.continuous.continuousAt
      have hexp_w₀ : Circle.exp (Complex.arg (w₀ : ℂ)) = w₀ := Circle.exp_arg w₀
      obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
        Metric.mem_nhds_iff.mp (hexp_cont (hexp_w₀.symm ▸ hV))
      have hw₀_slit : (w₀ : ℂ) ∈ Complex.slitPlane := hslit w₀ hw₀
      have harg_cont : ContinuousAt (fun w : Circle => Complex.arg (w : ℂ)) w₀ :=
        (Complex.continuousAt_arg hw₀_slit).comp continuous_subtype_val.continuousAt
      have hball_nhds : Metric.ball (Complex.arg (w₀ : ℂ)) δ ∈ 𝓝 (Complex.arg (w₀ : ℂ)) :=
        Metric.ball_mem_nhds _ hδ_pos
      refine ⟨(fun w : Circle => Complex.arg (w : ℂ)) ⁻¹' Metric.ball (Complex.arg (w₀ : ℂ)) δ,
        harg_cont hball_nhds, fun w₁ hw₁ w₂ hw₂ τ => ?_⟩
      apply hδ_sub
      have hconv : Convex ℝ (Metric.ball (Complex.arg (w₀ : ℂ)) δ) :=
        convex_ball (Complex.arg (w₀ : ℂ)) δ
      exact hconv hw₁ hw₂ (sub_nonneg.mpr τ.2.2) τ.2.1 (sub_add_cancel 1 (τ : ℝ))

/-! ## 3. Component Endpoints of an Open Subset of `(0, 1)` -/

/-- The left endpoint of the connected component of `U ⊆ (0, 1)` containing `t`. -/
private noncomputable def leftEnd (U : Set ℝ) (t : ℝ) : ℝ :=
  sSup (Iic t \ U)

/-- The right endpoint of the connected component of `U ⊆ (0, 1)` containing `t`. -/
private noncomputable def rightEnd (U : Set ℝ) (t : ℝ) : ℝ :=
  sInf (Ici t \ U)

private lemma leftEnd_props {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    leftEnd U t ∈ Icc 0 1 ∧ leftEnd U t ∉ U ∧ leftEnd U t < t ∧ Ioo (leftEnd U t) t ⊆ U := by
  have ht01 : t ∈ Ioo 0 1 := hU_sub ht
  have h0_notMem : (0 : ℝ) ∉ U := fun h => (hU_sub h).1.ne rfl
  have h0_mem : (0 : ℝ) ∈ Iic t \ U := ⟨ht01.1.le, h0_notMem⟩
  have hne : (Iic t \ U).Nonempty := ⟨0, h0_mem⟩
  have hbdd : BddAbove (Iic t \ U) := ⟨t, fun _ hx => hx.1⟩
  have hcl : IsClosed (Iic t \ U) := isClosed_Iic.sdiff hU_open
  have hmem : leftEnd U t ∈ Iic t \ U := hcl.csSup_mem hne hbdd
  have h0_le : 0 ≤ leftEnd U t := le_csSup hbdd h0_mem
  have hle_t : leftEnd U t ≤ t := hmem.1
  have hnot_U : leftEnd U t ∉ U := hmem.2
  have hlt_t : leftEnd U t < t := lt_of_le_of_ne hle_t fun he => hnot_U (he.symm ▸ ht)
  refine ⟨⟨h0_le, hle_t.trans ht01.2.le⟩, hnot_U, hlt_t, fun s hs => ?_⟩
  by_contra hsU
  have hs_mem : s ∈ Iic t \ U := ⟨hs.2.le, hsU⟩
  exact not_le_of_gt hs.1 (le_csSup hbdd hs_mem)

private lemma rightEnd_props {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    rightEnd U t ∈ Icc 0 1 ∧ rightEnd U t ∉ U ∧ t < rightEnd U t ∧ Ioo t (rightEnd U t) ⊆ U := by
  have ht01 : t ∈ Ioo 0 1 := hU_sub ht
  have h1_notMem : (1 : ℝ) ∉ U := fun h => (hU_sub h).2.ne rfl
  have h1_mem : (1 : ℝ) ∈ Ici t \ U := ⟨ht01.2.le, h1_notMem⟩
  have hne : (Ici t \ U).Nonempty := ⟨1, h1_mem⟩
  have hbdd : BddBelow (Ici t \ U) := ⟨t, fun _ hx => hx.1⟩
  have hcl : IsClosed (Ici t \ U) := isClosed_Ici.sdiff hU_open
  have hmem : rightEnd U t ∈ Ici t \ U := hcl.csInf_mem hne hbdd
  have hle_1 : rightEnd U t ≤ 1 := csInf_le hbdd h1_mem
  have ht_le : t ≤ rightEnd U t := hmem.1
  have hnot_U : rightEnd U t ∉ U := hmem.2
  have ht_lt : t < rightEnd U t := lt_of_le_of_ne ht_le fun he => hnot_U (he ▸ ht)
  refine ⟨⟨ht01.1.le.trans ht_le, hle_1⟩, hnot_U, ht_lt, fun s hs => ?_⟩
  by_contra hsU
  have hs_mem : s ∈ Ici t \ U := ⟨hs.1.le, hsU⟩
  exact not_le_of_gt hs.2 (csInf_le hbdd hs_mem)

private lemma Ioo_leftEnd_rightEnd_subset {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    Ioo (leftEnd U t) (rightEnd U t) ⊆ U := by
  obtain ⟨_, _, _, hleft⟩ := leftEnd_props hU_open hU_sub ht
  obtain ⟨_, _, _, hright⟩ := rightEnd_props hU_open hU_sub ht
  intro s hs
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact hleft ⟨hs.1, hlt⟩
  · exact ht
  · exact hright ⟨hgt, hs.2⟩

private lemma le_leftEnd_of_notMem {U : Set ℝ}
    {t s₀ : ℝ} (hs₀_le : s₀ ≤ t) (hs₀_not : s₀ ∉ U) :
    s₀ ≤ leftEnd U t := by
  have hbdd : BddAbove (Iic t \ U) := ⟨t, fun _ hx => hx.1⟩
  exact le_csSup hbdd ⟨hs₀_le, hs₀_not⟩

private lemma rightEnd_le_of_notMem {U : Set ℝ}
    {t s₁ : ℝ} (hs₁_ge : t ≤ s₁) (hs₁_not : s₁ ∉ U) :
    rightEnd U t ≤ s₁ := by
  have hbdd : BddBelow (Ici t \ U) := ⟨t, fun _ hx => hx.1⟩
  exact csInf_le hbdd ⟨hs₁_ge, hs₁_not⟩

private lemma leftEnd_eq_of_mem_Ioo {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t s : ℝ} (ht : t ∈ U) (hs : s ∈ Ioo (leftEnd U t) (rightEnd U t)) :
    leftEnd U s = leftEnd U t := by
  have hsU : s ∈ U := Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht hs
  obtain ⟨_, hnot_t, _, _⟩ := leftEnd_props hU_open hU_sub ht
  obtain ⟨_, hnot_s, _, _⟩ := leftEnd_props hU_open hU_sub hsU
  refine le_antisymm ?_ (le_leftEnd_of_notMem hs.1.le hnot_t)
  by_contra hgt
  have hlt : leftEnd U t < leftEnd U s := not_le.mp hgt
  obtain ⟨_, _, hls_lt, _⟩ := leftEnd_props hU_open hU_sub hsU
  have hmem_Ioo : leftEnd U s ∈ Ioo (leftEnd U t) (rightEnd U t) :=
    ⟨hlt, hls_lt.trans hs.2⟩
  exact hnot_s (Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht hmem_Ioo)

private lemma rightEnd_eq_of_mem_Ioo {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t s : ℝ} (ht : t ∈ U) (hs : s ∈ Ioo (leftEnd U t) (rightEnd U t)) :
    rightEnd U s = rightEnd U t := by
  have hsU : s ∈ U := Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht hs
  obtain ⟨_, hnot_t, _, _⟩ := rightEnd_props hU_open hU_sub ht
  obtain ⟨_, hnot_s, _, _⟩ := rightEnd_props hU_open hU_sub hsU
  refine le_antisymm (rightEnd_le_of_notMem hs.2.le hnot_t) ?_
  by_contra hlt
  have hgt : rightEnd U s < rightEnd U t := not_le.mp hlt
  obtain ⟨_, _, hrs_gt, _⟩ := rightEnd_props hU_open hU_sub hsU
  have hmem_Ioo : rightEnd U s ∈ Ioo (leftEnd U t) (rightEnd U t) :=
    ⟨hs.1.trans hrs_gt, hgt⟩
  exact hnot_s (Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht hmem_Ioo)

private lemma leftEnd_mem_closure {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    leftEnd U t ∈ closure U := by
  obtain ⟨_, _, hlt, hsub⟩ := leftEnd_props hU_open hU_sub ht
  have hmem : leftEnd U t ∈ Icc (leftEnd U t) t := left_mem_Icc.mpr hlt.le
  rw [← closure_Ioo hlt.ne] at hmem
  exact closure_mono hsub hmem

private lemma rightEnd_mem_closure {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    {t : ℝ} (ht : t ∈ U) :
    rightEnd U t ∈ closure U := by
  obtain ⟨_, _, hlt, hsub⟩ := rightEnd_props hU_open hU_sub ht
  have hmem : rightEnd U t ∈ Icc t (rightEnd U t) := right_mem_Icc.mpr hlt.le
  rw [← closure_Ioo hlt.ne] at hmem
  exact closure_mono hsub hmem

/-! ## 4. Pushing a Curve on `ℝ` Out of an Open Set `U ⊆ (0, 1)` -/

private noncomputable def toCircleOfChart {Δ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart Δ h g) (x : S) : Circle := by
  classical
  exact if hx : x ∈ discBd Δ then
    (⟨h x, by
      change h x ∈ sphere (0 : ℂ) 1
      rw [← c.bd]
      exact mem_image_of_mem h hx⟩ : Circle)
  else (1 : Circle)

private lemma coe_toCircleOfChart {Δ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart Δ h g) {x : S} (hx : x ∈ discBd Δ) :
    ((toCircleOfChart c x : Circle) : ℂ) = h x := by
  dsimp [toCircleOfChart]
  simp [hx]

private lemma g_toCircleOfChart {Δ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart Δ h g) {x : S} (hx : x ∈ discBd Δ) :
    g ((toCircleOfChart c x : Circle) : ℂ) = x := by
  rw [coe_toCircleOfChart c hx]
  exact c.gh (discBd_subset Δ hx)

private lemma nearby_boundary_arcs
    {Δ Y : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g)
    (arcBetween : Circle → Circle → unitInterval → Circle)
    (harc_nhds : ∀ w₀ : Circle, g (w₀ : ℂ) ∈ Y ∩ discBd Δ → ∀ V ∈ 𝓝 w₀,
      ∃ W ∈ 𝓝 w₀, ∀ w₁ ∈ W, ∀ w₂ ∈ W, ∀ τ : unitInterval, arcBetween w₁ w₂ τ ∈ V)
    {P : ℝ → S} (hP_cont : Continuous P) {U : Set ℝ}
    (hP_bd : ∀ t ∈ closure U \ U, P t ∈ Y ∩ discBd Δ)
    {t₀ : ℝ} (ht₀_bd : P t₀ ∈ Y ∩ discBd Δ) {N : Set S} (hN : N ∈ 𝓝 (P t₀)) :
    ∃ δ > 0,
      (∀ s : ℝ, |s - t₀| < δ → P s ∈ N) ∧
      (∀ a b : ℝ, a ∈ closure U \ U → b ∈ closure U \ U →
        |a - t₀| < δ → |b - t₀| < δ → ∀ τ : unitInterval,
          g ((arcBetween (toCircleOfChart c (P a)) (toCircleOfChart c (P b)) τ : Circle) : ℂ) ∈ N)
            := by
  let w₀ : Circle := toCircleOfChart c (P t₀)
  have hgw₀ : g (w₀ : ℂ) = P t₀ := g_toCircleOfChart c ht₀_bd.2
  have hg_circle_cont : Continuous (fun w : Circle => g (w : ℂ)) :=
    c.gc.comp_continuous continuous_subtype_val (fun w => sphere_subset_closedBall w.2)
  have hV : (fun w : Circle => g (w : ℂ)) ⁻¹' N ∈ 𝓝 w₀ :=
    hg_circle_cont.continuousAt (hgw₀.symm ▸ hN)
  obtain ⟨W, hW_nhds, hW_sub⟩ :=
    harc_nhds w₀ (hgw₀.symm ▸ ht₀_bd) _ hV
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp hW_nhds
  have hcw₀ : (w₀ : ℂ) = h (P t₀) := coe_toCircleOfChart c ht₀_bd.2
  have hh_at : ContinuousWithinAt h Δ (P t₀) :=
    c.hc (P t₀) (discBd_subset Δ ht₀_bd.2)
  have hball_nhds : Metric.ball (h (P t₀)) ε ∈ 𝓝 (h (P t₀)) :=
    Metric.ball_mem_nhds _ hε_pos
  obtain ⟨M, hM_nhds, hM_sub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hh_at hball_nhds)
  have hP_pre : P ⁻¹' (N ∩ M) ∈ 𝓝 t₀ :=
    hP_cont.continuousAt (Filter.inter_mem hN hM_nhds)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hP_pre
  refine ⟨δ, hδ_pos, fun s hs => (hδ_sub (by simpa [Real.dist_eq] using hs)).1,
    fun a b ha hb ha_lt hb_lt τ => ?_⟩
  have ha_bd : P a ∈ Y ∩ discBd Δ := hP_bd a ha
  have hb_bd : P b ∈ Y ∩ discBd Δ := hP_bd b hb
  have ha_M : P a ∈ M := (hδ_sub (by simpa [Real.dist_eq] using ha_lt)).2
  have hb_M : P b ∈ M := (hδ_sub (by simpa [Real.dist_eq] using hb_lt)).2
  have ha_ball : h (P a) ∈ Metric.ball (h (P t₀)) ε := hM_sub ⟨ha_M, discBd_subset Δ ha_bd.2⟩
  have hb_ball : h (P b) ∈ Metric.ball (h (P t₀)) ε := hM_sub ⟨hb_M, discBd_subset Δ hb_bd.2⟩
  have ha_W : toCircleOfChart c (P a) ∈ W := by
    apply hε_sub
    rw [Metric.mem_ball]
    change dist ((toCircleOfChart c (P a) : Circle) : ℂ) (w₀ : ℂ) < ε
    rw [coe_toCircleOfChart c ha_bd.2, hcw₀]
    exact Metric.mem_ball.mp ha_ball
  have hb_W : toCircleOfChart c (P b) ∈ W := by
    apply hε_sub
    rw [Metric.mem_ball]
    change dist ((toCircleOfChart c (P b) : Circle) : ℂ) (w₀ : ℂ) < ε
    rw [coe_toCircleOfChart c hb_bd.2, hcw₀]
    exact Metric.mem_ball.mp hb_ball
  exact hW_sub _ ha_W _ hb_W τ

private lemma exists_pushed_real_curve
    {Δ Y : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g)
    (arcBetween : Circle → Circle → unitInterval → Circle)
    (harc_cont : ∀ w₁ w₂ : Circle, Continuous (arcBetween w₁ w₂))
    (harc_ends : ∀ w₁ w₂ : Circle, arcBetween w₁ w₂ 0 = w₁ ∧ arcBetween w₁ w₂ 1 = w₂)
    (harc_mem : ∀ w₁ w₂ : Circle, g (w₁ : ℂ) ∈ Y ∩ discBd Δ → g (w₂ : ℂ) ∈ Y ∩ discBd Δ →
      ∀ τ : unitInterval, g ((arcBetween w₁ w₂ τ : Circle) : ℂ) ∈ Y ∩ discBd Δ)
    (harc_nhds : ∀ w₀ : Circle, g (w₀ : ℂ) ∈ Y ∩ discBd Δ → ∀ V ∈ 𝓝 w₀,
      ∃ W ∈ 𝓝 w₀, ∀ w₁ ∈ W, ∀ w₂ ∈ W, ∀ τ : unitInterval, arcBetween w₁ w₂ τ ∈ V)
    {P : ℝ → S} (hP_cont : Continuous P)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : U ⊆ Ioo 0 1)
    (hP_bd : ∀ t ∈ closure U \ U, P t ∈ Y ∩ discBd Δ) :
    ∃ Ψ : ℝ → S, Continuous Ψ ∧
      (∀ t ∉ U, Ψ t = P t) ∧
      (∀ t ∈ U, Ψ t ∈ Y ∩ discBd Δ) := by
  classical
  let segMap (a b t : ℝ) : S :=
    g ((arcBetween (toCircleOfChart c (P a)) (toCircleOfChart c (P b))
      (projIcc 0 1 zero_le_one ((t - a) / (b - a))) : Circle) : ℂ)
  have hseg_cont : ∀ a b : ℝ, Continuous (segMap a b) := by
    intro a b
    have hτ_cont : Continuous (fun t : ℝ => projIcc 0 1 zero_le_one ((t - a) / (b - a))) :=
      continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _)
    have harc_t : Continuous (fun t : ℝ =>
        ((arcBetween (toCircleOfChart c (P a)) (toCircleOfChart c (P b))
          (projIcc 0 1 zero_le_one ((t - a) / (b - a))) : Circle) : ℂ)) :=
      continuous_subtype_val.comp ((harc_cont _ _).comp hτ_cont)
    exact c.gc.comp_continuous harc_t fun t => sphere_subset_closedBall (arcBetween _ _ _).2
  let Ψ : ℝ → S := fun t => if t ∈ U then segMap (leftEnd U t) (rightEnd U t) t else P t
  have hΨ_notMem : ∀ t ∉ U, Ψ t = P t := fun t ht => by simp [Ψ, ht]
  have hΨ_mem : ∀ t ∈ U, Ψ t ∈ Y ∩ discBd Δ := by
    intro t ht
    simp only [Ψ, ht, ↓reduceIte]
    have ha_cl : leftEnd U t ∈ closure U \ U :=
      ⟨leftEnd_mem_closure hU_open hU_sub ht, (leftEnd_props hU_open hU_sub ht).2.1⟩
    have hb_cl : rightEnd U t ∈ closure U \ U :=
      ⟨rightEnd_mem_closure hU_open hU_sub ht, (rightEnd_props hU_open hU_sub ht).2.1⟩
    have ha_Y : P (leftEnd U t) ∈ Y ∩ discBd Δ := hP_bd _ ha_cl
    have hb_Y : P (rightEnd U t) ∈ Y ∩ discBd Δ := hP_bd _ hb_cl
    exact harc_mem _ _ ((g_toCircleOfChart c ha_Y.2).symm ▸ ha_Y)
      ((g_toCircleOfChart c hb_Y.2).symm ▸ hb_Y) _
  refine ⟨Ψ, continuous_iff_continuousAt.mpr fun t₀ => ?_, hΨ_notMem, hΨ_mem⟩
  by_cases ht₀U : t₀ ∈ U
  · obtain ⟨_, _, ha_lt, _⟩ := leftEnd_props hU_open hU_sub ht₀U
    obtain ⟨_, _, hb_gt, _⟩ := rightEnd_props hU_open hU_sub ht₀U
    have hIoo_nhds : Ioo (leftEnd U t₀) (rightEnd U t₀) ∈ 𝓝 t₀ :=
      Ioo_mem_nhds ha_lt hb_gt
    have heq : Ψ =ᶠ[𝓝 t₀] segMap (leftEnd U t₀) (rightEnd U t₀) := by
      filter_upwards [hIoo_nhds] with t ht
      have htU : t ∈ U := Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht₀U ht
      simp only [Ψ, htU, ↓reduceIte, leftEnd_eq_of_mem_Ioo hU_open hU_sub ht₀U ht,
        rightEnd_eq_of_mem_Ioo hU_open hU_sub ht₀U ht]
    exact (hseg_cont _ _).continuousAt.congr heq.symm
  · by_cases ht₀_cl : t₀ ∈ closure U
    · have ht₀_bd : P t₀ ∈ Y ∩ discBd Δ := hP_bd t₀ ⟨ht₀_cl, ht₀U⟩
      let w₀ : Circle := toCircleOfChart c (P t₀)
      have hgw₀ : g (w₀ : ℂ) = P t₀ := g_toCircleOfChart c ht₀_bd.2
      have hΨ_t₀ : Ψ t₀ = P t₀ := by simp [Ψ, ht₀U]
      rw [continuousAt_iff_continuous_left_right]
      constructor
      · -- Left continuity at `t₀`
        by_cases hleft_in : ∃ s₀ < t₀, Ioo s₀ t₀ ⊆ U
        · obtain ⟨s₀, hs₀_lt, hs₀_sub⟩ := hleft_in
          let t_mid : ℝ := (s₀ + t₀) / 2
          have ht_mid_mem : t_mid ∈ Ioo s₀ t₀ := by
            change (s₀ + t₀) / 2 ∈ Ioo s₀ t₀
            exact ⟨by linarith, by linarith⟩
          have ht_mid_U : t_mid ∈ U := hs₀_sub ht_mid_mem
          have hr_eq : rightEnd U t_mid = t₀ := by
            obtain ⟨_, hr_not, htm_lt_r, _⟩ := rightEnd_props hU_open hU_sub ht_mid_U
            refine le_antisymm (rightEnd_le_of_notMem ht_mid_mem.2.le ht₀U) ?_
            by_contra hlt
            have hlt' : rightEnd U t_mid < t₀ := not_le.mp hlt
            exact hr_not (hs₀_sub ⟨ht_mid_mem.1.trans htm_lt_r, hlt'⟩)
          let a₀ : ℝ := leftEnd U t_mid
          obtain ⟨_, _, ha₀_lt_tm, _⟩ := leftEnd_props hU_open hU_sub ht_mid_U
          have ha₀_lt_t₀ : a₀ < t₀ := ha₀_lt_tm.trans ht_mid_mem.2
          have hIoc_nhds : Ioc a₀ t₀ ∈ 𝓝[≤] t₀ := Ioc_mem_nhdsLE ha₀_lt_t₀
          have heq : Ψ =ᶠ[𝓝[≤] t₀] segMap a₀ t₀ := by
            filter_upwards [hIoc_nhds] with t ht
            rcases eq_or_lt_of_le ht.2 with ht_eq | ht_lt
            · rw [ht_eq]
              dsimp [segMap]
              have hdiv : (t₀ - a₀) / (t₀ - a₀) = 1 := div_self (sub_ne_zero.mpr ha₀_lt_t₀.ne')
              have hproj : projIcc 0 1 zero_le_one ((t₀ - a₀) / (t₀ - a₀)) = 1 := by
                ext
                simp [hdiv]
              rw [hΨ_t₀, hproj, (harc_ends _ _).2, hgw₀]
            · have ht_Ioo : t ∈ Ioo (leftEnd U t_mid) (rightEnd U t_mid) := by
                rw [hr_eq]
                exact ⟨ht.1, ht_lt⟩
              have htU : t ∈ U := Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht_mid_U ht_Ioo
              simp only [Ψ, htU, ↓reduceIte, leftEnd_eq_of_mem_Ioo hU_open hU_sub ht_mid_U ht_Ioo,
                rightEnd_eq_of_mem_Ioo hU_open hU_sub ht_mid_U ht_Ioo, hr_eq]
              rfl
          exact ((hseg_cont a₀ t₀).continuousAt.continuousWithinAt).congr_of_eventuallyEq
            heq (by
              dsimp [segMap]
              have hdiv : (t₀ - a₀) / (t₀ - a₀) = 1 := div_self (sub_ne_zero.mpr ha₀_lt_t₀.ne')
              have hproj : projIcc 0 1 zero_le_one ((t₀ - a₀) / (t₀ - a₀)) = 1 := by
                ext; simp [hdiv]
              rw [hΨ_t₀, hproj, (harc_ends _ _).2, hgw₀])
        · rw [ContinuousWithinAt, Filter.tendsto_def]
          intro N hN
          rw [hΨ_t₀] at hN
          obtain ⟨δ, hδ_pos, hδ_P, hδ_seg⟩ :=
            nearby_boundary_arcs c arcBetween harc_nhds hP_cont hP_bd ht₀_bd hN
          have hnot_sub : ¬ (Ioo (t₀ - δ) t₀ ⊆ U) := fun h => hleft_in ⟨t₀ - δ, by linarith, h⟩
          obtain ⟨s₀, hs₀_Ioo, hs₀_notU⟩ := not_subset.mp hnot_sub
          have hs₀_nhds : Ioc s₀ t₀ ∈ 𝓝[≤] t₀ := Ioc_mem_nhdsLE hs₀_Ioo.2
          filter_upwards [hs₀_nhds] with t ht
          change Ψ t ∈ N
          by_cases htU : t ∈ U
          · simp only [Ψ, htU, ↓reduceIte]
            have ha_cl : leftEnd U t ∈ closure U \ U :=
              ⟨leftEnd_mem_closure hU_open hU_sub htU, (leftEnd_props hU_open hU_sub htU).2.1⟩
            have hb_cl : rightEnd U t ∈ closure U \ U :=
              ⟨rightEnd_mem_closure hU_open hU_sub htU, (rightEnd_props hU_open hU_sub htU).2.1⟩
            have hs₀_le_a : s₀ ≤ leftEnd U t := le_leftEnd_of_notMem ht.1.le hs₀_notU
            have ha_lt_t : leftEnd U t < t := (leftEnd_props hU_open hU_sub htU).2.2.1
            have ht_lt_b : t < rightEnd U t := (rightEnd_props hU_open hU_sub htU).2.2.1
            have hb_le_t₀ : rightEnd U t ≤ t₀ := rightEnd_le_of_notMem ht.2 ht₀U
            have ha_dist : |leftEnd U t - t₀| < δ := by
              rw [abs_lt]
              exact ⟨by linarith [hs₀_Ioo.1], by linarith⟩
            have hb_dist : |rightEnd U t - t₀| < δ := by
              rw [abs_lt]
              exact ⟨by linarith [hs₀_Ioo.1], by linarith⟩
            exact hδ_seg _ _ ha_cl hb_cl ha_dist hb_dist _
          · simp only [Ψ, htU, ↓reduceIte]
            apply hδ_P
            rw [abs_lt]
            exact ⟨by linarith [hs₀_Ioo.1, ht.1], by linarith [ht.2]⟩
      · -- Right continuity at `t₀`
        by_cases hright_in : ∃ s₁ > t₀, Ioo t₀ s₁ ⊆ U
        · obtain ⟨s₁, hs₁_gt, hs₁_sub⟩ := hright_in
          let t_mid : ℝ := (t₀ + s₁) / 2
          have ht_mid_mem : t_mid ∈ Ioo t₀ s₁ := by
            change (t₀ + s₁) / 2 ∈ Ioo t₀ s₁
            exact ⟨by linarith, by linarith⟩
          have ht_mid_U : t_mid ∈ U := hs₁_sub ht_mid_mem
          have hl_eq : leftEnd U t_mid = t₀ := by
            obtain ⟨_, hl_not, hl_lt_tm, _⟩ := leftEnd_props hU_open hU_sub ht_mid_U
            refine le_antisymm ?_ (le_leftEnd_of_notMem ht_mid_mem.1.le ht₀U)
            by_contra hgt
            have hgt' : t₀ < leftEnd U t_mid := not_le.mp hgt
            exact hl_not (hs₁_sub ⟨hgt', hl_lt_tm.trans ht_mid_mem.2⟩)
          let b₀ : ℝ := rightEnd U t_mid
          obtain ⟨_, _, htm_lt_b₀, _⟩ := rightEnd_props hU_open hU_sub ht_mid_U
          have ht₀_lt_b₀ : t₀ < b₀ := ht_mid_mem.1.trans htm_lt_b₀
          have hIco_nhds : Ico t₀ b₀ ∈ 𝓝[≥] t₀ := Ico_mem_nhdsGE ht₀_lt_b₀
          have heq : Ψ =ᶠ[𝓝[≥] t₀] segMap t₀ b₀ := by
            filter_upwards [hIco_nhds] with t ht
            rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
            · dsimp [segMap]
              have hproj : projIcc 0 1 zero_le_one ((t₀ - t₀) / (b₀ - t₀)) = 0 := by
                ext
                simp
              rw [hΨ_t₀, hproj, (harc_ends _ _).1, hgw₀]
            · have ht_Ioo : t ∈ Ioo (leftEnd U t_mid) (rightEnd U t_mid) := by
                rw [hl_eq]
                exact ⟨ht_gt, ht.2⟩
              have htU : t ∈ U := Ioo_leftEnd_rightEnd_subset hU_open hU_sub ht_mid_U ht_Ioo
              simp only [Ψ, htU, ↓reduceIte, leftEnd_eq_of_mem_Ioo hU_open hU_sub ht_mid_U ht_Ioo,
                rightEnd_eq_of_mem_Ioo hU_open hU_sub ht_mid_U ht_Ioo, hl_eq]
              rfl
          exact ((hseg_cont t₀ b₀).continuousAt.continuousWithinAt).congr_of_eventuallyEq
            heq (by
              dsimp [segMap]
              have hproj : projIcc 0 1 zero_le_one ((t₀ - t₀) / (b₀ - t₀)) = 0 := by
                ext; simp
              rw [hΨ_t₀, hproj, (harc_ends _ _).1, hgw₀])
        · rw [ContinuousWithinAt, Filter.tendsto_def]
          intro N hN
          rw [hΨ_t₀] at hN
          obtain ⟨δ, hδ_pos, hδ_P, hδ_seg⟩ :=
            nearby_boundary_arcs c arcBetween harc_nhds hP_cont hP_bd ht₀_bd hN
          have hnot_sub : ¬ (Ioo t₀ (t₀ + δ) ⊆ U) := fun h => hright_in ⟨t₀ + δ, by linarith, h⟩
          obtain ⟨s₁, hs₁_Ioo, hs₁_notU⟩ := not_subset.mp hnot_sub
          have hs₁_nhds : Ico t₀ s₁ ∈ 𝓝[≥] t₀ := Ico_mem_nhdsGE hs₁_Ioo.1
          filter_upwards [hs₁_nhds] with t ht
          change Ψ t ∈ N
          by_cases htU : t ∈ U
          · simp only [Ψ, htU, ↓reduceIte]
            have ha_cl : leftEnd U t ∈ closure U \ U :=
              ⟨leftEnd_mem_closure hU_open hU_sub htU, (leftEnd_props hU_open hU_sub htU).2.1⟩
            have hb_cl : rightEnd U t ∈ closure U \ U :=
              ⟨rightEnd_mem_closure hU_open hU_sub htU, (rightEnd_props hU_open hU_sub htU).2.1⟩
            have ht₀_le_a : t₀ ≤ leftEnd U t := le_leftEnd_of_notMem ht.1 ht₀U
            have ha_lt_t : leftEnd U t < t := (leftEnd_props hU_open hU_sub htU).2.2.1
            have ht_lt_b : t < rightEnd U t := (rightEnd_props hU_open hU_sub htU).2.2.1
            have hb_le_s₁ : rightEnd U t ≤ s₁ := rightEnd_le_of_notMem ht.2.le hs₁_notU
            have ha_dist : |leftEnd U t - t₀| < δ := by
              rw [abs_lt]
              exact ⟨by linarith, by linarith [hs₁_Ioo.2]⟩
            have hb_dist : |rightEnd U t - t₀| < δ := by
              rw [abs_lt]
              exact ⟨by linarith, by linarith [hs₁_Ioo.2]⟩
            exact hδ_seg _ _ ha_cl hb_cl ha_dist hb_dist _
          · simp only [Ψ, htU, ↓reduceIte]
            apply hδ_P
            rw [abs_lt]
            exact ⟨by linarith [ht.1], by linarith [hs₁_Ioo.2, ht.2]⟩
    · have hcompl_open : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
      have hcompl_nhds : (closure U)ᶜ ∈ 𝓝 t₀ := hcompl_open.mem_nhds ht₀_cl
      have heq : Ψ =ᶠ[𝓝 t₀] P := by
        filter_upwards [hcompl_nhds] with t ht
        have ht_notU : t ∉ U := fun htU => ht (subset_closure htU)
        simp [Ψ, ht_notU]
      exact hP_cont.continuousAt.congr heq.symm

/-! ## 5. Proof of Graph Minors VII, (11.3) -/

private lemma homotopic_of_coincide_off_chart
    {Δ : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g)
    (hΔ_closed : IsClosed Δ) {Z : Set Circle} (hZ_open : IsOpen Z)
    (φ ψ : C(Circle, S)) (hφ_mem : ∀ z ∈ Z, φ z ∈ Δ)
    (hψ_mem : ∀ z ∈ Z, ψ z ∈ Δ) (hψ_outside : ∀ z ∉ Z, ψ z = φ z) :
    ClosedCurvesHomotopicIn univ φ ψ := by
  have hφ_clZ : ∀ z ∈ closure Z, φ z ∈ Δ := by
    have hcl_Δ : IsClosed (φ ⁻¹' Δ) := hΔ_closed.preimage φ.continuous
    exact fun z hz => hcl_Δ.closure_subset_iff.mpr hφ_mem hz
  have hψ_clZ : ∀ z ∈ closure Z, ψ z ∈ Δ := by
    intro z hz
    by_cases hzZ : z ∈ Z
    · exact hψ_mem z hzZ
    · rw [hψ_outside z hzZ]
      exact hφ_clZ z hz
  let Θ_fun : Circle × unitInterval → S := by
    classical
    exact fun p =>
      if p.1 ∈ closure Z then
        g ((1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h (ψ p.1))
      else φ p.1
  have hΘ_eq_outside : ∀ p : Circle × unitInterval, p.1 ∉ Z → Θ_fun p = φ p.1 := by
    intro p hp
    dsimp [Θ_fun]
    split_ifs with hp_cl
    · change g ((1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h (ψ p.1)) = φ p.1
      have h1 : (1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h (ψ p.1) = h (φ p.1) := by
        rw [hψ_outside p.1 hp, ← add_smul, sub_add_cancel, one_smul]
      rw [h1, c.gh (hφ_clZ p.1 hp_cl)]
    · rfl
  have hΘ_cont : Continuous Θ_fun := by
    have hcl1 : IsClosed (closure Z ×ˢ (univ : Set unitInterval)) :=
      isClosed_closure.prod isClosed_univ
    have hcl2 : IsClosed (Zᶜ ×ˢ (univ : Set unitInterval)) :=
      hZ_open.isClosed_compl.prod isClosed_univ
    have hunion : (closure Z ×ˢ (univ : Set unitInterval)) ∪
        (Zᶜ ×ˢ (univ : Set unitInterval)) = univ := by
      ext p
      simp only [mem_union, mem_prod, mem_univ, and_true, mem_compl_iff, iff_true]
      by_cases hp : p.1 ∈ Z
      · exact Or.inl (subset_closure hp)
      · exact Or.inr hp
    have hcont1 : ContinuousOn Θ_fun (closure Z ×ˢ (univ : Set unitInterval)) := by
      have hcont_g : ContinuousOn
          (fun p : Circle × unitInterval =>
            g ((1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h (ψ p.1)))
          (closure Z ×ˢ (univ : Set unitInterval)) := by
        have hhφ : ContinuousOn (fun p : Circle × unitInterval => h (φ p.1))
            (closure Z ×ˢ (univ : Set unitInterval)) :=
          c.hc.comp (φ.continuous.comp continuous_fst).continuousOn
            (fun p hp => hφ_clZ p.1 hp.1)
        have hhψ : ContinuousOn (fun p : Circle × unitInterval => h (ψ p.1))
            (closure Z ×ˢ (univ : Set unitInterval)) :=
          c.hc.comp (ψ.continuous.comp continuous_fst).continuousOn
            (fun p hp => hψ_clZ p.1 hp.1)
        have ht : ContinuousOn (fun p : Circle × unitInterval => (p.2 : ℝ))
            (closure Z ×ˢ (univ : Set unitInterval)) :=
          (continuous_subtype_val.comp continuous_snd).continuousOn
        have hL : ContinuousOn
            (fun p : Circle × unitInterval =>
              (1 - (p.2 : ℝ)) • h (φ p.1) + (p.2 : ℝ) • h (ψ p.1))
            (closure Z ×ˢ (univ : Set unitInterval)) :=
          ((continuousOn_const.sub ht).smul hhφ).add (ht.smul hhψ)
        refine c.gc.comp hL fun p hp => ?_
        exact convex_closedBall (0 : ℂ) 1
          (c.hm (hφ_clZ p.1 hp.1)) (c.hm (hψ_clZ p.1 hp.1))
          (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
      refine hcont_g.congr fun p hp => ?_
      have hp_cl : p.1 ∈ closure Z := hp.1
      simp [Θ_fun, hp_cl]
    have hcont2 : ContinuousOn Θ_fun (Zᶜ ×ˢ (univ : Set unitInterval)) := by
      refine (φ.continuous.comp continuous_fst).continuousOn.congr fun p hp => ?_
      exact hΘ_eq_outside p hp.1
    rw [← continuousOn_univ, ← hunion]
    exact hcont1.union_of_isClosed hcont2 hcl1 hcl2
  refine ⟨⟨Θ_fun, hΘ_cont⟩, fun _ => mem_univ _, fun z => ?_, fun z => ?_⟩
  · dsimp [Θ_fun]
    split_ifs with hz_cl
    · change g ((1 - (0 : ℝ)) • h (φ z) + (0 : ℝ) • h (ψ z)) = φ z
      simp [c.gh (hφ_clZ z hz_cl)]
    · rfl
  · by_cases hz : z ∈ Z
    · have hz_cl : z ∈ closure Z := subset_closure hz
      change Θ_fun (z, 1) = ψ z
      simp only [Θ_fun, hz_cl, ↓reduceIte]
      change g ((1 - (1 : ℝ)) • h (φ z) + (1 : ℝ) • h (ψ z)) = ψ z
      simp [c.gh (hψ_clZ z hz_cl)]
    · change Θ_fun (z, 1) = ψ z
      rw [hΘ_eq_outside (z, 1) hz, hψ_outside z hz]

/-- When `Z = {z : Circle | φ z ∈ Δ \ discBd Δ}` is a proper subset of `Circle` (`Z ≠ univ`), any
continuous map `φ : C(Circle, S)` with `range φ ⊆ Y ∪ (Δ \ discBd Δ)` is homotopic in `univ` to a
map `ψ : C(Circle, S)` with `range ψ ⊆ Y` and `range ψ ⊆ range φ ∪ discBd Δ`. -/
private lemma disc_interior_curve_homotopy_of_exists_notMem
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ))
    (φ : C(Circle, S)) (hφ : range φ ⊆ Y ∪ (Δ \ discBd Δ))
    {z_base : Circle} (hz_base : φ z_base ∉ Δ \ discBd Δ) :
    ∃ ψ : C(Circle, S), range ψ ⊆ Y ∧ range ψ ⊆ range φ ∪ discBd Δ ∧
      ClosedCurvesHomotopicIn univ φ ψ := by
  have : T2Space S := hS.2.1
  obtain ⟨h, g, c, arcBetween, harc_cont, harc_ends, harc_mem, harc_nhds⟩ :=
    exists_chart_and_arcBetween hS hΔ hY_arc
  have hΔ_compact : IsCompact Δ := by
    rw [← c.g_closedBall]
    exact (isCompact_closedBall 0 1).image_of_continuousOn c.gc
  have hΔ_closed : IsClosed Δ := hΔ_compact.isClosed
  have hint_eq : Δ \ discBd Δ = g '' ball 0 1 := by
    have h1 := c.g_closedBall
    have h2 := c.g_sphere
    rw [← h2, ← h1, ← c.g_sdiff Subset.rfl sphere_subset_closedBall]
    congr 1
    ext w
    simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm, mem_ball_zero_iff]
    exact ⟨fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2, fun h1 => ⟨h1.le, h1.ne⟩⟩
  have hint_open : IsOpen (Δ \ discBd Δ) := by
    rw [hint_eq]
    exact c.isOpen_image_ball hS.2.2
  let Z : Set Circle := {z : Circle | φ z ∈ Δ \ discBd Δ}
  have hZ_open : IsOpen Z := hint_open.preimage φ.continuous
  have hz_base_notZ : z_base ∉ Z := hz_base
  let E : ℝ → Circle := fun t => z_base * Circle.exp (2 * Real.pi * t)
  have hE_cont : Continuous E := by
    dsimp [E]
    fun_prop
  have hE0 : E 0 = z_base := by simp [E]
  have hE1 : E 1 = z_base := by simp [E, Circle.exp_two_pi]
  let E_Icc : C(unitInterval, Circle) := ⟨fun t => E t.1, hE_cont.comp continuous_subtype_val⟩
  have hE_Icc_surj : Surjective E_Icc := by
    intro z
    have h2pi : 0 < 2 * Real.pi := Real.two_pi_pos
    let w : Circle := z_base⁻¹ * z
    let θ : ℝ := toIcoMod h2pi 0 (Complex.arg (w : ℂ))
    have hθ_mem : θ ∈ Ico 0 (2 * Real.pi) := by
      simpa using toIcoMod_mem_Ico h2pi 0 (Complex.arg (w : ℂ))
    have hexp_θ : Circle.exp θ = w := by
      have h1 : θ = Complex.arg (w : ℂ) - toIcoDiv h2pi 0 (Complex.arg (w : ℂ)) • (2 * Real.pi)
        := rfl
      have h2 : Circle.exp θ = Circle.exp (Complex.arg (w : ℂ)) := by
        rw [h1, zsmul_eq_mul]
        exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg (w : ℂ)), by push_cast; ring⟩
      exact h2.trans (Circle.exp_arg w)
    let t : ℝ := θ / (2 * Real.pi)
    have ht_mem : t ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hθ_mem.1 h2pi.le, (div_le_one h2pi).mpr hθ_mem.2.le⟩
    refine ⟨⟨t, ht_mem⟩, ?_⟩
    change z_base * Circle.exp (2 * Real.pi * (θ / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ θ h2pi.ne', hexp_θ, mul_inv_cancel_left]
  have hE_quot : Topology.IsQuotientMap E_Icc :=
    Topology.IsQuotientMap.of_surjective_continuous hE_Icc_surj E_Icc.continuous
  let P : ℝ → S := φ ∘ E
  have hP_cont : Continuous P := φ.continuous.comp hE_cont
  let U : Set ℝ := Ioo 0 1 ∩ E ⁻¹' Z
  have hU_open : IsOpen U := isOpen_Ioo.inter (hZ_open.preimage hE_cont)
  have hU_sub : U ⊆ Ioo 0 1 := inter_subset_left
  have hU_iff_on_Icc : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ U ↔ E t ∈ Z := by
    intro t ht
    constructor
    · exact fun h => h.2
    · intro hEZ
      refine ⟨⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hEZ⟩
      · rintro rfl
        exact hz_base_notZ (hE0 ▸ hEZ)
      · rintro rfl
        exact hz_base_notZ (hE1 ▸ hEZ)
  have hP_bd : ∀ t ∈ closure U \ U, P t ∈ Y ∩ discBd Δ := by
    intro t ⟨ht_cl, ht_notU⟩
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := by
      rw [← closure_Ioo (zero_ne_one' ℝ)]
      exact closure_mono hU_sub ht_cl
    have hEt_notZ : E t ∉ Z := fun hEZ => ht_notU ((hU_iff_on_Icc t ht_Icc).mpr hEZ)
    have hPt_Y : P t ∈ Y := (hφ (mem_range_self (E t))).resolve_right hEt_notZ
    have hU_in_Δ : U ⊆ P ⁻¹' Δ := fun s hs => hs.2.1
    have hPt_Δ : P t ∈ Δ := by
      have hcl_Δ : IsClosed (P ⁻¹' Δ) := hΔ_closed.preimage hP_cont
      exact hcl_Δ.closure_subset_iff.mpr hU_in_Δ ht_cl
    have hPt_bd : P t ∈ discBd Δ := by
      by_contra hnot_bd
      exact hEt_notZ ⟨hPt_Δ, hnot_bd⟩
    exact ⟨hPt_Y, hPt_bd⟩
  obtain ⟨Ψ, hΨ_cont, hΨ_notMem, hΨ_mem⟩ :=
    exists_pushed_real_curve c arcBetween harc_cont harc_ends harc_mem harc_nhds
      hP_cont hU_open hU_sub hP_bd
  let Ψ_Icc : C(unitInterval, S) := ⟨fun t => Ψ t.1, hΨ_cont.comp continuous_subtype_val⟩
  have hΨ_factors : Function.FactorsThrough Ψ_Icc E_Icc := by
    intro s t hst
    have hexp_eq : Circle.exp (2 * Real.pi * (s : ℝ)) = Circle.exp (2 * Real.pi * (t : ℝ)) :=
      mul_left_cancel (show z_base * Circle.exp (2 * Real.pi * (s : ℝ)) =
        z_base * Circle.exp (2 * Real.pi * (t : ℝ)) from hst)
    have hinj : InjOn (fun x : ℝ => Circle.exp (2 * Real.pi * x)) (Ico 0 1) := by
      intro x hx y hy hxy
      have hx' : 2 * Real.pi * x ∈ Ico 0 (2 * Real.pi) :=
        ⟨mul_nonneg Real.two_pi_pos.le hx.1, by nlinarith [hx.2, Real.pi_pos]⟩
      have hy' : 2 * Real.pi * y ∈ Ico 0 (2 * Real.pi) :=
        ⟨mul_nonneg Real.two_pi_pos.le hy.1, by nlinarith [hy.2, Real.pi_pos]⟩
      have hmul := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith) hx' hy' hxy
      exact mul_left_cancel₀ Real.two_pi_pos.ne' hmul
    have h0_notU : (0 : ℝ) ∉ U := fun h => (hU_sub h).1.ne rfl
    have h1_notU : (1 : ℝ) ∉ U := fun h => (hU_sub h).2.ne rfl
    have hΨ01 : Ψ 0 = Ψ 1 := by
      rw [hΨ_notMem 0 h0_notU, hΨ_notMem 1 h1_notU]
      change φ (E 0) = φ (E 1)
      rw [hE0, hE1]
    rcases eq_or_lt_of_le s.2.2 with hs1 | hs_lt
    · rcases eq_or_lt_of_le t.2.2 with ht1 | ht_lt
      · have : s = t := Subtype.ext (hs1.trans ht1.symm)
        rw [this]
      · have ht0 : (t : ℝ) = 0 := by
          apply hinj ⟨t.2.1, ht_lt⟩ ⟨le_rfl, zero_lt_one⟩
          change Circle.exp (2 * Real.pi * (t : ℝ)) = Circle.exp (2 * Real.pi * 0)
          rw [mul_zero, Circle.exp_zero, ← hexp_eq, hs1, mul_one, Circle.exp_two_pi]
        change Ψ s.1 = Ψ t.1
        rw [hs1, ht0, hΨ01]
    · rcases eq_or_lt_of_le t.2.2 with ht1 | ht_lt
      · have hs0 : (s : ℝ) = 0 := by
          apply hinj ⟨s.2.1, hs_lt⟩ ⟨le_rfl, zero_lt_one⟩
          change Circle.exp (2 * Real.pi * (s : ℝ)) = Circle.exp (2 * Real.pi * 0)
          rw [mul_zero, Circle.exp_zero, hexp_eq, ht1, mul_one, Circle.exp_two_pi]
        change Ψ s.1 = Ψ t.1
        rw [hs0, ht1, hΨ01]
      · have hst_eq : (s : ℝ) = (t : ℝ) := hinj ⟨s.2.1, hs_lt⟩ ⟨t.2.1, ht_lt⟩ hexp_eq
        change Ψ s.1 = Ψ t.1
        rw [hst_eq]
  let ψ : C(Circle, S) := hE_quot.lift Ψ_Icc hΨ_factors
  have hψ_comp : ∀ t : unitInterval, ψ (E_Icc t) = Ψ t.1 := by
    intro t
    exact ContinuousMap.congr_fun (hE_quot.lift_comp Ψ_Icc hΨ_factors) t
  have hψ_outside : ∀ z : Circle, z ∉ Z → ψ z = φ z := by
    intro z hz
    obtain ⟨t, rfl⟩ := hE_Icc_surj z
    rw [hψ_comp t]
    have ht_notU : t.1 ∉ U := fun htU => hz ((hU_iff_on_Icc t.1 t.2).mp htU)
    exact hΨ_notMem t.1 ht_notU
  have hψ_inside : ∀ z : Circle, z ∈ Z → ψ z ∈ Y ∩ discBd Δ := by
    intro z hz
    obtain ⟨t, rfl⟩ := hE_Icc_surj z
    rw [hψ_comp t]
    have htU : t.1 ∈ U := (hU_iff_on_Icc t.1 t.2).mpr hz
    exact hΨ_mem t.1 htU
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Z
    · exact (hψ_inside z hz).1
    · rw [hψ_outside z hz]
      exact (hφ (mem_range_self z)).resolve_right hz
  · rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Z
    · exact Or.inr (hψ_inside z hz).2
    · rw [hψ_outside z hz]
      exact Or.inl (mem_range_self z)
  · exact homotopic_of_coincide_off_chart c hΔ_closed hZ_open φ ψ
      (fun z hz => hz.1) (fun z hz => discBd_subset Δ (hψ_inside z hz).2) hψ_outside

/-- Graph Minors VII, (11.3), first statement (page 249):
"Let $\Sigma$ be a connected surface, let $\Delta \subseteq \Sigma$ be a closed disc, and let
$Y \subseteq \Sigma$ be such that $Y \cap bd(\Delta)$ is arc-connected. Then any continuous map
$\phi \colon S^1 \to Y \cup (\Delta - bd(\Delta))$ is homotopic to a map $\psi \colon S^1 \to Y$
with $|\psi| \subseteq |\phi| \cup bd(\Delta)$."
Note: in the degenerate case `range φ ⊆ Δ \ discBd Δ` (`Z = S¹` on page 250, line 982), the
existence of `ψ : Circle → Y` with `range ψ ⊆ range φ ∪ discBd Δ` requires `Y ∩ (range φ ∪ discBd
Δ)`
(for instance `Y ∩ discBd Δ`) to be nonempty. -/
theorem disc_interior_curve_homotopy
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ))
    (φ : C(Circle, S)) (hφ : range φ ⊆ Y ∪ (Δ \ discBd Δ))
    (hne : (∃ z : Circle, φ z ∉ Δ \ discBd Δ) ∨ (Y ∩ discBd Δ).Nonempty) :
    ∃ ψ : C(Circle, S), range ψ ⊆ Y ∧ range ψ ⊆ range φ ∪ discBd Δ ∧
      ClosedCurvesHomotopicIn univ φ ψ := by
  by_cases hex : ∃ z : Circle, φ z ∉ Δ \ discBd Δ
  · obtain ⟨z_base, hz_base⟩ := hex
    exact disc_interior_curve_homotopy_of_exists_notMem hS hΔ hY_arc φ hφ hz_base
  · obtain ⟨y₀, hy₀Y, hy₀_bd⟩ := hne.resolve_left hex
    push Not at hex
    have hφ_Δ : range φ ⊆ Δ := by
      rintro _ ⟨z, rfl⟩
      exact (hex z).1
    refine ⟨ContinuousMap.const Circle y₀, ?_, ?_,
      closedCurvesHomotopicIn_const_of_range_subset_disc hΔ (discBd_subset Δ hy₀_bd) φ hφ_Δ⟩
    · rintro _ ⟨_, rfl⟩
      exact hy₀Y
    · rintro _ ⟨_, rfl⟩
      exact Or.inr hy₀_bd

/-- Graph Minors VII, (11.3), second statement (page 249):
"In particular, if $Y$ is flat then so is $Y \cup (\Delta - bd(\Delta))$." -/
theorem isFlat_union_disc_diff_discBd
    (hS : IsSurface S) {Δ Y : Set S} (hΔ : IsClosedDisc Δ)
    (hY_arc : IsArcConnected (Y ∩ discBd Δ)) (hY_flat : IsFlat Y) :
    IsFlat (Y ∪ (Δ \ discBd Δ)) := by
  intro φ hφ
  by_cases hex : ∃ z : Circle, φ z ∉ Δ \ discBd Δ
  · obtain ⟨ψ, hψY, _, ⟨Θ₁, _, hΘ₁0, hΘ₁1⟩⟩ :=
      disc_interior_curve_homotopy hS hΔ hY_arc φ hφ (Or.inl hex)
    obtain ⟨c₀, _, ⟨Θ₂, _, hΘ₂0, hΘ₂1⟩⟩ := hY_flat ψ hψY
    let t₁ : Circle × unitInterval → Circle × unitInterval :=
      fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))
    let t₂ : Circle × unitInterval → Circle × unitInterval :=
      fun p => (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
    have ht₁_cont : Continuous t₁ :=
      continuous_fst.prodMk (continuous_projIcc.comp (continuous_const.mul
        (continuous_subtype_val.comp continuous_snd)))
    have ht₂_cont : Continuous t₂ :=
      continuous_fst.prodMk (continuous_projIcc.comp
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
    let f₁ : Circle × unitInterval → S := Θ₁ ∘ t₁
    let f₂ : Circle × unitInterval → S := Θ₂ ∘ t₂
    have hf₁_cont : Continuous f₁ := Θ₁.continuous.comp ht₁_cont
    have hf₂_cont : Continuous f₂ := Θ₂.continuous.comp ht₂_cont
    let Ψ_fun : Circle × unitInterval → S :=
      fun p => if (p.2 : ℝ) ≤ 1 / 2 then f₁ p else f₂ p
    have hΨ_cont : Continuous Ψ_fun := by
      refine Continuous.if_le hf₁_cont hf₂_cont
        (continuous_subtype_val.comp continuous_snd) continuous_const ?_
      intro p hp
      have hp1 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)) = 1 := by
        rw [hp]; ext; simp
      have hp0 : projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1) = 0 := by
        rw [hp]; ext; simp
      change Θ₁ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) =
        Θ₂ (p.1, projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      rw [hp1, hp0, hΘ₁1 p.1, hΘ₂0 p.1]
    refine ⟨c₀, mem_univ c₀, ⟨Ψ_fun, hΨ_cont⟩, fun _ => mem_univ _, fun z => ?_, fun z => ?_⟩
    · have hle : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
      have hp0 : projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ)) = 0 := by
        ext; change max (0 : ℝ) (min 1 (2 * 0)) = 0; norm_num
      change (if ((0 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (z, 0) else f₂ (z, 0)) = φ z
      simp only [hle, ↓reduceIte]
      change Θ₁ (z, projIcc 0 1 zero_le_one (2 * ((0 : unitInterval) : ℝ))) = φ z
      rw [hp0, hΘ₁0 z]
    · have hnot : ¬ (((1 : unitInterval) : ℝ) ≤ 1 / 2) := by norm_num
      have hp1 : projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by
        ext; change max (0 : ℝ) (min 1 (2 * 1 - 1)) = 1; norm_num
      change (if ((1 : unitInterval) : ℝ) ≤ 1 / 2 then f₁ (z, 1) else f₂ (z, 1)) = c₀
      simp only [hnot, ↓reduceIte]
      change Θ₂ (z, projIcc 0 1 zero_le_one (2 * ((1 : unitInterval) : ℝ) - 1)) = c₀
      rw [hp1, hΘ₂1 z]
      rfl
  · push Not at hex
    have hφ_Δ : range φ ⊆ Δ := by
      rintro _ ⟨z, rfl⟩
      exact (hex z).1
    have hy₀ : φ 1 ∈ Δ := (hex 1).1
    exact ⟨φ 1, mem_univ _, closedCurvesHomotopicIn_const_of_range_subset_disc hΔ hy₀ φ hφ_Δ⟩

end GraphMinor.GM07
