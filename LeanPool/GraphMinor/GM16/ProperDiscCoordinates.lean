/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Boundary coordinates for arrangement discs

The disc transport in XV (7.7), pages 139–140, first matches the cyclic orders on the two boundary
circles. We construct an increasing interpolation of the marked angles and the resulting circle
homeomorphism.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

theorem isInteriorPoint_euclideanPlane (x : EuclideanPlane) : IsInteriorPoint x := by
  let U : Set EuclideanPlane := (fun y : EuclideanPlane => y + x) '' OpenUnitDisc
  have hHomeo := (Homeomorph.addRight x).image OpenUnitDisc
  have hOpen_ball : IsOpen OpenUnitDisc := Metric.isOpen_ball
  have hOpen_U : IsOpen U := (Homeomorph.addRight x).isOpenMap OpenUnitDisc hOpen_ball
  have hxU : x ∈ U := ⟨0, by simp [OpenUnitDisc], by simp⟩
  exact ⟨U, hOpen_U, hxU, ⟨hHomeo.symm⟩⟩

/-- For any closed disc `D` in `EuclideanPlane`, `frontier D = discBd D`. -/
theorem isClosedDisc_frontier_eq_discBd_euclideanPlane {D : Set EuclideanPlane}
    (hD : IsClosedDisc D) : frontier D = discBd D := by
  have hman : ∀ x : EuclideanPlane, IsManifoldPoint x :=
    fun x => (isInteriorPoint_euclideanPlane x).isManifoldPoint
  have hcl : IsClosed D := hD.isCompact.isClosed
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨u1, -⟩ := c.union_ball
  have hO := c.isOpen_image_ball hman
  have hsub : g '' Metric.ball 0 1 ⊆ D := fun x hx => u1 ▸ Or.inl hx
  apply subset_antisymm
  · intro x hx
    have hxD : x ∈ D := hcl.frontier_subset hx
    rw [← u1] at hxD
    rcases hxD with h' | h'
    · exact absurd (interior_maximal hsub hO h') hx.2
    · exact h'
  · intro x hx
    have hxD : x ∈ D := Surface.discBd_subset _ hx
    refine ⟨subset_closure hxD, fun hint => ?_⟩
    obtain ⟨U, hU, hxU, ⟨f⟩⟩ := isInteriorPoint_euclideanPlane x
    classical
    let G : ℂ → EuclideanPlane := fun w =>
      if hw : complexPlane w ∈ OpenUnitDisc then (f.symm ⟨_, hw⟩).1 else x
    let M : Set ℂ := complexPlane ⁻¹' OpenUnitDisc
    have hMo : IsOpen M := Metric.isOpen_ball.preimage complexPlane.continuous
    have hG : ∀ w (hw : w ∈ M), G w = (f.symm ⟨_, hw⟩).1 := fun w hw => by
      have hw' : complexPlane w ∈ OpenUnitDisc := hw
      simp only [G, hw', dite_true]
    have hGc : ContinuousOn G M := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : M.domRestrict G = fun w : M => (f.symm ⟨complexPlane w.1, w.2⟩).1 :=
        funext fun w => hG w.1 w.2
      rw [this]
      refine continuous_subtype_val.comp (f.symm.continuous.comp ?_)
      exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) _
    have hGi : InjOn G M := by
      intro a ha b hb hab
      rw [hG a ha, hG b hb] at hab
      have h₁ := f.symm.injective (Subtype.ext hab)
      exact complexPlane.injective (congrArg Subtype.val h₁)
    let B : Set ℂ := M ∩ G ⁻¹' interior D
    have hBo : IsOpen B := hGc.isOpen_inter_preimage hMo isOpen_interior
    have hBD : MapsTo G B D := fun w hw => interior_subset hw.2
    have hHc : ContinuousOn (h ∘ G) B := c.hc.comp (hGc.mono inter_subset_left) hBD
    have hHi : InjOn (h ∘ G) B := by
      intro a ha b hb hab
      apply hGi ha.1 hb.1
      have := congrArg g hab
      simpa [c.gh (hBD ha), c.gh (hBD hb)] using this
    have hOpen := isOpen_image_of_injOn hBo hHc hHi
    set w₀ : ℂ := complexPlane.symm (f ⟨x, hxU⟩).1 with hw₀
    have hw₀M : w₀ ∈ M := by
      change complexPlane w₀ ∈ OpenUnitDisc
      rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      exact (f ⟨x, hxU⟩).2
    have hGw : G w₀ = x := by
      rw [hG w₀ hw₀M]
      have : (⟨complexPlane w₀, hw₀M⟩ : OpenUnitDisc) = f ⟨x, hxU⟩ := by
        apply Subtype.ext
        change complexPlane w₀ = _
        rw [hw₀, LinearIsometryEquiv.apply_symm_apply]
      rw [this, f.symm_apply_apply]
    have hw₀B : w₀ ∈ B := ⟨hw₀M, show G w₀ ∈ interior D from hGw ▸ hint⟩
    have hball : h x ∈ interior (Metric.closedBall (0 : ℂ) 1) := by
      refine mem_interior.mpr ⟨_, ?_, hOpen, ⟨w₀, hw₀B, by simp [hGw]⟩⟩
      rintro _ ⟨w, hw, rfl⟩
      exact c.hm (hBD hw)
    rw [interior_closedBall _ one_ne_zero] at hball
    have hsph : h x ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    rw [Metric.mem_ball, Metric.mem_sphere.mp hsph] at hball
    exact lt_irrefl _ hball

/-- For any closed disc `D` in `EuclideanPlane`, `subBd D = discBd D`. -/
theorem isClosedDisc_subBd_eq_discBd_euclideanPlane {D : Set EuclideanPlane}
    (hD : IsClosedDisc D) : subBd D = discBd D := by
  rw [GM11.subBd_eq_frontier, isClosedDisc_frontier_eq_discBd_euclideanPlane hD]

/-- Piecewise-linear strictly increasing interpolation between `a 0 < a 1 < ... < a (n + 1)` and
`b 0 < b 1 < ... < b (n + 1)`. -/
theorem exists_strictMonoOn_interp (n : ℕ) (a b : ℕ → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) :
    ∃ τ : ℝ → ℝ,
      ContinuousOn τ (Icc (a 0) (a (n + 1))) ∧
      StrictMonoOn τ (Icc (a 0) (a (n + 1))) ∧
      ∀ i ≤ n + 1, τ (a i) = b i := by
  induction n with
  | zero =>
    have ha01 : a 0 < a 1 := ha Nat.zero_lt_one
    have hb01 : b 0 < b 1 := hb Nat.zero_lt_one
    have hslope : 0 < (b 1 - b 0) / (a 1 - a 0) := div_pos (by linarith) (by linarith)
    let τ : ℝ → ℝ := fun x => b 0 + (b 1 - b 0) / (a 1 - a 0) * (x - a 0)
    refine ⟨τ, by fun_prop, ?_, ?_⟩
    · intro x _ y _ hxy
      dsimp only [τ]
      nlinarith
    · intro i hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · simp [τ]
      · dsimp only [τ]
        have hne : a 1 - a 0 ≠ 0 := by linarith
        rw [div_mul_cancel₀ _ hne]
        ring
  | succ n ih =>
    obtain ⟨τ₀, hcont₀, hmono₀, hval₀⟩ := ih
    have ha_step : a (n + 1) < a (n + 2) := ha (Nat.lt_succ_self (n + 1))
    have hb_step : b (n + 1) < b (n + 2) := hb (Nat.lt_succ_self (n + 1))
    have ha0_le : a 0 ≤ a (n + 1) := ha.monotone (Nat.zero_le (n + 1))
    have hslope : 0 < (b (n + 2) - b (n + 1)) / (a (n + 2) - a (n + 1)) :=
      div_pos (by linarith) (by linarith)
    let τ₁ : ℝ → ℝ := fun x =>
      b (n + 1) + (b (n + 2) - b (n + 1)) / (a (n + 2) - a (n + 1)) * (x - a (n + 1))
    let τ : ℝ → ℝ := fun x => if x ≤ a (n + 1) then τ₀ x else τ₁ x
    have hτ_left : ∀ x ≤ a (n + 1), τ x = τ₀ x := fun x hx => by simp [τ, hx]
    have hτ_right : ∀ x, a (n + 1) ≤ x → τ x = τ₁ x := by
      intro x hx
      rcases eq_or_lt_of_le hx with rfl | hlt
      · simp [τ, τ₁, hval₀ (n + 1) le_rfl]
      · have hnot : ¬ x ≤ a (n + 1) := not_le.mpr hlt
        simp [τ, hnot]
    have hcont₁ : ContinuousOn τ (Icc (a (n + 1)) (a (n + 2))) := by
      refine (by fun_prop : ContinuousOn τ₁ (Icc (a (n + 1)) (a (n + 2)))).congr ?_
      intro x hx
      exact hτ_right x hx.1
    have hcont₀' : ContinuousOn τ (Icc (a 0) (a (n + 1))) := by
      refine hcont₀.congr ?_
      intro x hx
      exact hτ_left x hx.2
    have hIcc_union : Icc (a 0) (a (n + 1)) ∪ Icc (a (n + 1)) (a (n + 2)) = Icc (a 0) (a (n + 2)) :=
      Icc_union_Icc_eq_Icc ha0_le ha_step.le
    refine ⟨τ, ?_, ?_, ?_⟩
    · rw [← hIcc_union]
      exact hcont₀'.union_of_isClosed hcont₁ isClosed_Icc isClosed_Icc
    · intro x hx y hy hxy
      by_cases hy_le : y ≤ a (n + 1)
      · have hx_le : x ≤ a (n + 1) := hxy.le.trans hy_le
        rw [hτ_left x hx_le, hτ_left y hy_le]
        exact hmono₀ ⟨hx.1, hx_le⟩ ⟨hy.1, hy_le⟩ hxy
      · have hy_gt : a (n + 1) < y := not_le.mp hy_le
        by_cases hx_le : x ≤ a (n + 1)
        · have h1 : τ x ≤ b (n + 1) := by
            rw [hτ_left x hx_le, ← hval₀ (n + 1) le_rfl]
            exact hmono₀.monotoneOn ⟨hx.1, hx_le⟩ ⟨ha0_le, le_rfl⟩ hx_le
          have h2 : b (n + 1) < τ y := by
            rw [hτ_right y hy_gt.le]
            dsimp only [τ₁]
            nlinarith
          exact h1.trans_lt h2
        · have hx_gt : a (n + 1) < x := not_le.mp hx_le
          rw [hτ_right x hx_gt.le, hτ_right y hy_gt.le]
          dsimp only [τ₁]
          nlinarith
    · intro i hi
      rcases Nat.of_le_succ hi with hi_le | rfl
      · rw [hτ_left (a i) (ha.monotone hi_le)]
        exact hval₀ i hi_le
      · rw [hτ_right (a (n + 2)) ha_step.le]
        dsimp only [τ₁]
        have hne : a (n + 2) - a (n + 1) ≠ 0 := by linarith
        rw [div_mul_cancel₀ _ hne]
        ring

/-- Given `m ≥ 1` and strictly increasing sequences `t₁, t₂ : ℕ → ℝ` with
`t₁ i < t₁ 0 + 2π` and `t₂ i < t₂ 0 + 2π` for `i < m`, there is a homeomorphism
`h_circ : Circle ≃ₜ Circle` mapping `Circle.exp (t₁ i)` to `Circle.exp (t₂ i)` for all `i < m`. -/
theorem exists_circle_homeo_matching_angles (m : ℕ) (hm : 1 ≤ m)
    (t₁ t₂ : ℕ → ℝ) (ht₁ : StrictMono t₁) (ht₂ : StrictMono t₂)
    (hbd₁ : ∀ i < m, t₁ i < t₁ 0 + 2 * Real.pi)
    (hbd₂ : ∀ i < m, t₂ i < t₂ 0 + 2 * Real.pi) :
    ∃ h_circ : Circle ≃ₜ Circle,
      ∀ i < m, h_circ (Circle.exp (t₁ i)) = Circle.exp (t₂ i) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let a : ℕ → ℝ := fun i =>
    if i < m then (t₁ i - t₁ 0) / (2 * Real.pi) else 1 + (i - m : ℕ)
  let b : ℕ → ℝ := fun i =>
    if i < m then (t₂ i - t₂ 0) / (2 * Real.pi) else 1 + (i - m : ℕ)
  have ha_mono : StrictMono a := by
    intro i j hij
    dsimp only [a]
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      simp only [hi, hj, ↓reduceIte]
      exact div_lt_div_of_pos_right (by linarith [ht₁ hij]) hpi
    · by_cases hi : i < m
      · simp only [hi, hj, ↓reduceIte]
        have hlt : (t₁ i - t₁ 0) / (2 * Real.pi) < 1 := by
          rw [div_lt_one hpi]
          linarith [hbd₁ i hi]
        have hge : (0 : ℝ) ≤ (j - m : ℕ) := Nat.cast_nonneg _
        linarith
      · simp only [hi, hj, ↓reduceIte]
        have hsub : i - m < j - m := by omega
        have hcast : ((i - m : ℕ) : ℝ) < ((j - m : ℕ) : ℝ) := Nat.cast_lt.mpr hsub
        linarith
  have hb_mono : StrictMono b := by
    intro i j hij
    dsimp only [b]
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      simp only [hi, hj, ↓reduceIte]
      exact div_lt_div_of_pos_right (by linarith [ht₂ hij]) hpi
    · by_cases hi : i < m
      · simp only [hi, hj, ↓reduceIte]
        have hlt : (t₂ i - t₂ 0) / (2 * Real.pi) < 1 := by
          rw [div_lt_one hpi]
          linarith [hbd₂ i hi]
        have hge : (0 : ℝ) ≤ (j - m : ℕ) := Nat.cast_nonneg _
        linarith
      · simp only [hi, hj, ↓reduceIte]
        have hsub : i - m < j - m := by omega
        have hcast : ((i - m : ℕ) : ℝ) < ((j - m : ℕ) : ℝ) := Nat.cast_lt.mpr hsub
        linarith
  have hm0 : 0 < m := hm
  have ha0 : a 0 = 0 := by simp [a, hm0]
  have hb0 : b 0 = 0 := by simp [b, hm0]
  have ham : a m = 1 := by simp [a]
  have hbm : b m = 1 := by simp [b]
  have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  obtain ⟨τ, hcont, hmono, hval⟩ := exists_strictMonoOn_interp (m - 1) a b ha_mono hb_mono
  rw [← hm_eq, ha0, ham] at hcont hmono
  rw [← hm_eq] at hval
  have hτ0 : τ 0 = 0 := by
    have h := hval 0 (Nat.zero_le m)
    rwa [ha0, hb0] at h
  have hτ1 : τ 1 = τ 0 + 1 := by
    have h := hval m le_rfl
    rw [ham, hbm] at h
    rw [hτ0, zero_add, h]
  obtain ⟨h₀, _, hh₀⟩ := exists_circle_homeo hcont hmono hτ1
  let rot₁ : Circle ≃ₜ Circle := Homeomorph.mulRight (Circle.exp (-t₁ 0))
  let rot₂ : Circle ≃ₜ Circle := Homeomorph.mulRight (Circle.exp (t₂ 0))
  refine ⟨(rot₁.trans h₀).trans rot₂, fun i hi => ?_⟩
  have hai_mem : a i ∈ Icc (0 : ℝ) 1 := by
    rw [← ha0, ← ham]
    exact ⟨ha_mono.monotone (Nat.zero_le i), ha_mono.monotone (le_of_lt hi)⟩
  have hai_ee : ee (a i) = rot₁ (Circle.exp (t₁ i)) := by
    change Circle.exp (2 * Real.pi * a i) = Circle.exp (t₁ i) * Circle.exp (-t₁ 0)
    dsimp only [a]
    simp only [hi, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hpi), ← Circle.exp_add, sub_eq_add_neg]
  have hbi_ee : ee (b i) = Circle.exp (t₂ i - t₂ 0) := by
    dsimp only [ee, b]
    simp only [hi, ↓reduceIte]
    rw [mul_div_cancel₀ _ (ne_of_gt hpi)]
  simp only [Homeomorph.trans_apply]
  rw [← hai_ee, hh₀ (a i) hai_mem, hval i (le_of_lt hi), hbi_ee]
  change Circle.exp (t₂ i - t₂ 0) * Circle.exp (t₂ 0) = Circle.exp (t₂ i)
  rw [← Circle.exp_add, sub_add_cancel]


end GraphMinor.GM16
