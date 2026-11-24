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
public import LeanPool.GraphMinor.GM16.ProperDiscCoordinates
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Extending the boundary map across a disc

For the disc transport in XV (7.7), pages 139–140, we extend a boundary homeomorphism radially
across the unit disc. We also extract increasing angle coordinates from the cyclic order.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

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

/-- Given `AgreesWithOArcHomeo ν Ω C φ`, `InjOn ν Ω.bar`, and a nonempty `Ω`-clockwise list `L`,
there is a strictly increasing sequence `t : ℕ → ℝ` with `t i < t 0 + 2π` and
`(φ (Circle.exp (t i))).1 = ν (L[i])` for all `i < L.length`. -/
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


end GraphMinor.GM16
