/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Homeomorphisms matching marked disc boundaries

Increasing real interpolation matches two cyclically ordered lists on a circle. A boundary
homeomorphism then extends over the entire disc. The planar frontier criteria identify the
boundary of the disc in Euclidean coordinates.
-/

public section

namespace GraphMinor.GM14

open Set Topology Surface GM09

/-- Every point of the Euclidean plane is a surface interior point. -/
theorem isInteriorPoint_euclideanPlane (x : EuclideanPlane) : IsInteriorPoint x :=
  Surface.isInteriorPoint_euclideanPlane x

/-- The frontier of a closed disc in the plane is its disc boundary. -/
theorem isClosedDisc_frontier_eq_discBd_euclideanPlane {D : Set EuclideanPlane}
    (hD : IsClosedDisc D) : frontier D = discBd D :=
  Surface.plane_disc_frontier hD

/-- The surface and disc boundaries agree for a closed disc in the plane. -/
theorem isClosedDisc_subBd_eq_discBd_euclideanPlane {D : Set EuclideanPlane}
    (hD : IsClosedDisc D) : subBd D = discBd D :=
  Surface.subBd_eq_discBd_euclideanPlane hD

/-- Two strictly ordered finite lists of real points admit strictly monotone interpolation. -/
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

/-- Match two cyclically ordered lists on the unit circle by a homeomorphism. -/
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

/-- A homeomorphism between disc boundaries extends over both discs. -/
theorem exists_disc_extension_of_bd_homeo
    {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂]
    {D₁ : Set S₁} {D₂ : Set S₂} (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (e_bd : discBd D₁ ≃ₜ discBd D₂) :
    ∃ (f : S₁ → S₂) (f' : S₂ → S₁),
      MapsTo f D₁ D₂ ∧ MapsTo f' D₂ D₁ ∧
      ContinuousOn f D₁ ∧ ContinuousOn f' D₂ ∧
      LeftInvOn f' f D₁ ∧ LeftInvOn f f' D₂ ∧
      ∀ x : discBd D₁, f x.1 = (e_bd x).1 := by
  obtain ⟨h₁, g₁, c₁⟩ := hD₁.exists_isChart
  obtain ⟨h₂, g₂, c₂⟩ := hD₂.exists_isChart
  have hsub₁ := Surface.discBd_subset D₁
  have hsub₂ := Surface.discBd_subset D₂
  have hs_sub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1
    := Metric.sphere_subset_closedBall
  obtain ⟨e₁', he₁'⟩ := exists_homeomorph_image (c₁.hc.mono hsub₁)
    (by rw [c₁.bd]; exact c₁.gc.mono hs_sub) (c₁.gh.mono hsub₁)
  let e₁ : discBd D₁ ≃ₜ Metric.sphere (0 : ℂ) 1 := e₁'.trans (Homeomorph.setCongr c₁.bd)
  have he₁ : ∀ x : discBd D₁, (e₁ x).1 = h₁ x.1 := fun x => he₁' x
  obtain ⟨e₂', he₂'⟩ := exists_homeomorph_image (c₂.hc.mono hsub₂)
    (by rw [c₂.bd]; exact c₂.gc.mono hs_sub) (c₂.gh.mono hsub₂)
  let e₂ : discBd D₂ ≃ₜ Metric.sphere (0 : ℂ) 1 := e₂'.trans (Homeomorph.setCongr c₂.bd)
  have he₂ : ∀ x : discBd D₂, (e₂ x).1 = h₂ x.1 := fun x => he₂' x
  let e_sph : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1 := (e₁.symm.trans e_bd).trans e₂
  obtain ⟨h₀, k₀, m, hh₀⟩ := exists_bdMatch e_sph
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner oArc_sphere oArc_sphere m
  rw [closedInner_sphere] at m'
  obtain ⟨m_maps₁, m_maps₂, m_left, m_right, m_cont₁, m_cont₂⟩ := m'
  let f : S₁ → S₂ := g₂ ∘ ψ ∘ h₁
  let f' : S₂ → S₁ := g₁ ∘ χ ∘ h₂
  refine ⟨f, f', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact c₂.gm (m_maps₁ (c₁.hm hx))
  · intro y hy
    exact c₁.gm (m_maps₂ (c₂.hm hy))
  · exact c₂.gc.comp (m_cont₁.comp c₁.hc c₁.hm) (m_maps₁.comp c₁.hm)
  · exact c₁.gc.comp (m_cont₂.comp c₂.hc c₂.hm) (m_maps₂.comp c₂.hm)
  · intro x hx
    dsimp only [f, f', Function.comp_apply]
    rw [c₂.hg (m_maps₁ (c₁.hm hx)), m_left (c₁.hm hx), c₁.gh hx]
  · intro y hy
    dsimp only [f, f', Function.comp_apply]
    rw [c₁.hg (m_maps₂ (c₂.hm hy)), m_right (c₂.hm hy), c₂.gh hy]
  · intro x
    dsimp only [f, Function.comp_apply]
    have hx_sph : h₁ x.1 ∈ Metric.sphere (0 : ℂ) 1 := c₁.bd ▸ mem_image_of_mem h₁ x.2
    have he₁_x : (⟨h₁ x.1, hx_sph⟩ : Metric.sphere (0 : ℂ) 1) = e₁ x := Subtype.ext (he₁ x).symm
    rw [hψ hx_sph, hh₀ ⟨h₁ x.1, hx_sph⟩, he₁_x]
    simp only [e_sph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [he₂ (e_bd x), c₂.gh (hsub₂ (e_bd x).2)]

/-- Represent a nonempty clockwise sequence by increasing angles over one turn. -/
theorem exists_angles_of_isClockwiseSeq
    {S : Type*} [TopologicalSpace S] {α : Type*}
    {ν : α → S} {Ω : CyclicPerm α} {C : Set S} {φ : Circle ≃ₜ C} {L : List α}
    (hA : AgreesWithOArcHomeo ν Ω C φ) (hinj : InjOn ν Ω.bar)
    (hcw : Ω.IsClockwiseSeq L) (hlen : 1 ≤ L.length) :
    ∃ t : ℕ → ℝ,
      StrictMono t ∧
      (∀ i < L.length, t i < t 0 + 2 * Real.pi) ∧
      ∀ (i : ℕ) (hi : i < L.length), (φ (Circle.exp (t i))).1 = ν (L[i]'hi) := by
  classical
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  let pt : ℝ → S := fun t => (φ (Circle.exp t)).1
  have hpt_eq_iff : ∀ t₁ t₂ : ℝ, pt t₁ = pt t₂ ↔ ∃ m : ℤ, t₁ = t₂ + m * (2 * Real.pi) := by
    intro t₁ t₂
    constructor
    · intro h
      have h1 : φ (Circle.exp t₁) = φ (Circle.exp t₂) := Subtype.ext h
      exact Circle.exp_eq_exp.mp (φ.injective h1)
    · rintro ⟨m, rfl⟩
      have h2 : Circle.exp (t₂ + m * (2 * Real.pi)) = Circle.exp t₂ :=
        Circle.exp_eq_exp.mpr ⟨m, rfl⟩
      simp [pt, h2]
  have hpt_inj : ∀ t₀ : ℝ, InjOn pt (Ico t₀ (t₀ + 2 * Real.pi)) := by
    intro t₀ t₁ ht₁ t₂ ht₂ h
    obtain ⟨m, rfl⟩ := (hpt_eq_iff t₁ t₂).mp h
    have hm0 : m = 0 := by
      by_contra hm
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_le hpi.le
        linarith [ht₁.1, ht₂.2]
      · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        have : 1 * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm_ge hpi.le
        linarith [ht₁.2, ht₂.1]
    simp [hm0]
  by_cases hlen3 : 3 ≤ L.length
  · have h012 : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) :=
      (Ω.mem_interval_of_lt hcw (by omega) (by omega) hlen3).2
    obtain ⟨t₀, t₁, t₂, ht01, ht12, ht20, hpt0, hpt1, hpt2⟩ :=
      hA.2 (L[0]'(by omega)) (L[1]'(by omega)) (L[2]'(by omega)) h012
    have hshift3 : ∀ v₁ v₂ : α, Ω.IsClockwise3 (L[0]'(by omega)) v₁ v₂ →
        ∃ u₁ u₂ : ℝ, t₀ < u₁ ∧ u₁ < u₂ ∧ u₂ < t₀ + 2 * Real.pi ∧
          pt u₁ = ν v₁ ∧ pt u₂ = ν v₂ := by
      intro v₁ v₂ hcw3
      obtain ⟨s₀, s₁, s₂, hs01, hs12, hs20, hs₀, hs₁, hs₂⟩ := hA.2 (L[0]'(by omega)) v₁ v₂ hcw3
      obtain ⟨m, hm⟩ := (hpt_eq_iff t₀ s₀).mp (hpt0.trans hs₀.symm)
      refine ⟨s₁ + m * (2 * Real.pi), s₂ + m * (2 * Real.pi), by linarith, by linarith, by linarith,
        ?_, ?_⟩
      · exact ((hpt_eq_iff _ s₁).mpr ⟨m, rfl⟩).trans hs₁
      · exact ((hpt_eq_iff _ s₂).mpr ⟨m, rfl⟩).trans hs₂
    have hex : ∀ (i : ℕ) (hi : i < L.length),
        ∃ u ∈ Ico t₀ (t₀ + 2 * Real.pi), pt u = ν (L[i]'hi) ∧ (0 < i → t₀ < u) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi_pos
      · exact ⟨t₀, ⟨le_rfl, by linarith⟩, hpt0, fun h => (Nat.lt_irrefl 0 h).elim⟩
      · by_cases hi1 : i = 1
        · subst hi1
          exact ⟨t₁, ⟨le_of_lt ht01, by linarith⟩, hpt1, fun _ => ht01⟩
        · have hcw_i : Ω.IsClockwise3 (L[0]'(by omega)) (L[1]'(by omega)) (L[i]'hi) :=
            (Ω.mem_interval_of_lt hcw (by omega) (by omega) hi).2
          obtain ⟨u₁, u₂, hu01, hu12, hu20, _, hu₂⟩ := hshift3 (L[1]'(by omega)) (L[i]'hi) hcw_i
          exact ⟨u₂, ⟨le_of_lt (hu01.trans hu12), hu20⟩, hu₂, fun _ => hu01.trans hu12⟩
    let t : ℕ → ℝ := fun i =>
      if hi : i < L.length then Classical.choose (hex i hi) else t₀ + 2 * Real.pi + i
    have ht_spec : ∀ (i : ℕ) (hi : i < L.length),
        t i ∈ Ico t₀ (t₀ + 2 * Real.pi) ∧ pt (t i) = ν (L[i]'hi) ∧ (0 < i → t₀ < t i) := by
      intro i hi
      have h_eq : t i = Classical.choose (hex i hi) := by
        dsimp only [t]; split_ifs; rfl
      rw [h_eq]
      exact Classical.choose_spec (hex i hi)
    have ht0_eq : t 0 = t₀ := by
      obtain ⟨ht0_mem, ht0_pt, _⟩ := ht_spec 0 (by omega)
      exact hpt_inj t₀ ht0_mem ⟨le_rfl, by linarith⟩ (ht0_pt.trans hpt0.symm)
    refine ⟨t, ?_, ?_, ?_⟩
    · intro i j hij
      by_cases hj : j < L.length
      · have hi : i < L.length := hij.trans hj
        rcases Nat.eq_zero_or_pos i with rfl | hi_pos
        · rw [ht0_eq]
          exact (ht_spec j hj).2.2 hij
        · have hcw_ij : Ω.IsClockwise3 (L[0]'(by omega)) (L[i]'hi) (L[j]'hj) :=
            (Ω.mem_interval_of_lt hcw hi_pos hij hj).2
          obtain ⟨u₁, u₂, hu01, hu12, hu20, hu₁, hu₂⟩ := hshift3 (L[i]'hi) (L[j]'hj) hcw_ij
          have hti : t i = u₁ :=
            hpt_inj t₀ (ht_spec i hi).1 ⟨le_of_lt hu01, hu12.trans hu20⟩
              ((ht_spec i hi).2.1.trans hu₁.symm)
          have htj : t j = u₂ :=
            hpt_inj t₀ (ht_spec j hj).1 ⟨le_of_lt (hu01.trans hu12), hu20⟩
              ((ht_spec j hj).2.1.trans hu₂.symm)
          linarith
      · by_cases hi : i < L.length
        · have hti := (ht_spec i hi).1.2
          have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
          have hj_nonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith
        · have hti : t i = t₀ + 2 * Real.pi + i := by dsimp only [t]; split_ifs; rfl
          have htj : t j = t₀ + 2 * Real.pi + j := by dsimp only [t]; split_ifs; rfl
          have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
          linarith
    · intro i hi
      rw [ht0_eq]
      exact (ht_spec i hi).1.2
    · intro i hi
      simpa [pt] using (ht_spec i hi).2.1
  · have hmem0 : L[0]'hlen ∈ Ω.bar := hcw.2.1 _ (List.getElem_mem hlen)
    obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective (φ.symm ⟨ν (L[0]'hlen), hA.1 _ hmem0⟩)
    have hpt0 : (φ (Circle.exp θ₀)).1 = ν (L[0]'hlen) := by
      rw [hθ₀, φ.apply_symm_apply]
    rcases ( by omega : L.length = 1 ∨ L.length = 2 ) with hlen1 | hlen2
    · refine ⟨fun i => θ₀ + i, ?_, ?_, ?_⟩
      · intro i j hij
        have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
        linarith
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [hpi]
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using hpt0
    · have h1_lt : 1 < L.length := by omega
      have hmem1 : L[1]'h1_lt ∈ Ω.bar := hcw.2.1 _ (List.getElem_mem h1_lt)
      obtain ⟨θ₁', hθ₁'⟩ := Circle.exp_surjective (φ.symm ⟨ν (L[1]'h1_lt), hA.1 _ hmem1⟩)
      obtain ⟨θ₁, hθ₁_mem, hθ₁_exp⟩ := Circle.periodic_exp.exists_mem_Ico hpi θ₁' θ₀
      have hpt1 : (φ (Circle.exp θ₁)).1 = ν (L[1]'h1_lt) := by
        rw [← hθ₁_exp, hθ₁', φ.apply_symm_apply]
      have hne01 : L[0]'hlen ≠ L[1]'h1_lt := by
        intro heq
        have := (List.Nodup.getElem_inj_iff hcw.1).mp heq
        omega
      have hθ0_lt_θ1 : θ₀ < θ₁ := by
        rcases eq_or_lt_of_le hθ₁_mem.1 with rfl | hlt
        · exfalso
          exact hne01 (hinj hmem0 hmem1 (hpt0.symm.trans hpt1))
        · exact hlt
      let t : ℕ → ℝ := fun i =>
        if i = 0 then θ₀ else if i = 1 then θ₁ else θ₀ + 2 * Real.pi + i
      refine ⟨t, ?_, ?_, ?_⟩
      · intro i j hij
        dsimp only [t]
        by_cases hj : j < 2
        · have hi0 : i = 0 := by omega
          have hj1 : j = 1 := by omega
          subst hi0; subst hj1
          simpa using hθ0_lt_θ1
        · by_cases hi : i < 2
          · have hj_nonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
            · simp only [↓reduceIte, show j ≠ 0 by omega, show j ≠ 1 by omega]
              linarith
            · simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, show j ≠ 0 by omega,
                show j ≠ 1 by omega]
              linarith [hθ₁_mem.2]
          · simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, show j ≠ 0 by omega,
              show j ≠ 1 by omega, ↓reduceIte]
            have hij_cast : (i : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hij
            linarith
      · intro i hi
        dsimp only [t]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · simp [hpi]
        · simpa using hθ₁_mem.2
      · intro i hi
        dsimp only [t]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · simpa using hpt0
        · simpa using hpt1

/-- Match the marked points of two circle parametrizations with the same cyclic order. -/
theorem exists_bd_homeo_of_agreesWithOArcHomeo
    {S₁ : Type*} {S₂ : Type*} [TopologicalSpace S₁] [TopologicalSpace S₂] {α : Type*}
    {ν₁ : α → S₁} {ν₂ : α → S₂} {Ω : CyclicPerm α} {C₁ : Set S₁} {C₂ : Set S₂}
    {φ₁ : Circle ≃ₜ C₁} {φ₂ : Circle ≃ₜ C₂}
    (hA₁ : AgreesWithOArcHomeo ν₁ Ω C₁ φ₁) (hA₂ : AgreesWithOArcHomeo ν₂ Ω C₂ φ₂)
    (hinj₁ : InjOn ν₁ Ω.bar) (hinj₂ : InjOn ν₂ Ω.bar) :
    ∃ e_bd : C₁ ≃ₜ C₂, ∀ v (hv : v ∈ Ω.bar), (e_bd ⟨ν₁ v, hA₁.1 v hv⟩).1 = ν₂ v := by
  rcases Ω.bar.eq_empty_or_nonempty with hemp | ⟨w₀, hw₀⟩
  · refine ⟨φ₁.symm.trans φ₂, fun v hv => ?_⟩
    rw [hemp] at hv
    exact hv.elim
  · obtain ⟨L, hL_len, hL_set, _, hcw⟩ := Ω.exists_isClockwiseSeq_of_subset_bar Subset.rfl hw₀
    have hlen_pos : 1 ≤ L.length := by
      have hw₀L : w₀ ∈ L := by
        have : w₀ ∈ {v | v ∈ L} := hL_set.symm ▸ hw₀
        exact this
      exact List.length_pos_of_mem hw₀L
    obtain ⟨t₁, ht₁_mono, ht₁_bd, ht₁_pt⟩ := exists_angles_of_isClockwiseSeq hA₁ hinj₁ hcw hlen_pos
    obtain ⟨t₂, ht₂_mono, ht₂_bd, ht₂_pt⟩ := exists_angles_of_isClockwiseSeq hA₂ hinj₂ hcw hlen_pos
    obtain ⟨h_circ, hh_circ⟩ :=
      exists_circle_homeo_matching_angles L.length hlen_pos t₁ t₂ ht₁_mono ht₂_mono ht₁_bd ht₂_bd
    refine ⟨φ₁.symm.trans (h_circ.trans φ₂), fun v hv => ?_⟩
    have hvL : v ∈ L := by
      have : v ∈ {x | x ∈ L} := hL_set.symm ▸ hv
      exact this
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvL
    have hφ₁_eq : (⟨ν₁ (L[i]'hi), hA₁.1 _ hv⟩ : C₁) = φ₁ (Circle.exp (t₁ i)) :=
      Subtype.ext (ht₁_pt i hi).symm
    simp only [Homeomorph.trans_apply]
    rw [hφ₁_eq, φ₁.symm_apply_apply, hh_circ i hi, ht₂_pt i hi]

end GraphMinor.GM14
