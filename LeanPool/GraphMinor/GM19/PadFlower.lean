/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Flower
public import LeanPool.GraphMinor.GM19.CircleOrder
public import LeanPool.GraphMinor.GM19.MarkedMatch

/-!
# A flower in a pad

For step (3) of the proof of Graph Minors XIX, (15.2), page 382, we work in a closed disc `C`, which
we call a pad, with a chart onto the closed unit disc. The ends `Y` of a disc `Δ` of `Σ̂` lie around
`bd(Δ)`, and each end `y` has a vertex `φ y` on `bd(C)`. If the two orders agree, then
`exists_pad_flower` gives a flower in the chart with one peak for each end, near `φ y`, and a
homeomorphism `τ` of the
circle that carries the peaks to the ends.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- The order data of a pad. `A y` and `U y` are the places of the end `y` and of its vertex `φ y`,
read along a cut circle. The vertices come in the order of the ends. The cyclic order of the ends
around
the parametrization `q` of `bd(Δ)` is the order of the places `A`. -/
structure PadOrder (q : Circle → T) (g : ℂ → T) (Y : Set T) (φ : T → T) (A U : T → ℝ) : Prop where
  finite : Y.Finite
  sub : Y ⊆ range q
  A_mem : ∀ y ∈ Y, A y ∈ Icc (0 : ℝ) 1
  U_mem : ∀ y ∈ Y, U y ∈ Icc (0 : ℝ) 1
  g_U : ∀ y ∈ Y, g (ee (U y)) = φ y
  mono : ∀ x ∈ Y, ∀ y ∈ Y, A x < A y → U x ≤ U y
  inj : InjOn A Y
  cyc : ∀ a b c : Circle, q a ∈ Y → q b ∈ Y → q c ∈ Y → a ≠ b → b ≠ c → a ≠ c →
    (CircleCyclic a b c ↔ CycOrder (A (q a)) (A (q b)) (A (q c)))

theorem exists_ee (u : Circle) : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ u = ee s := by
  by_cases h : u = 1
  · exact ⟨0, le_rfl, one_pos, by simp [ee, h]⟩
  · obtain ⟨s, hs0, hs1, hs⟩ := exists_angle h
    have hpi := Real.pi_pos
    refine ⟨s / (2 * Real.pi), by positivity, by rw [div_lt_one (by positivity)]; exact hs1, ?_⟩
    rw [ee, mul_div_cancel₀ _ (by positivity), ← hs]

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Circle.exp_add]
  congr 1
  ring

theorem ee_one_add (x : ℝ) : ee (x - 1) = ee x := by
  have : ee 1 = 1 := by simp [ee]
  have h := ee_add (x - 1) 1
  rw [sub_add_cancel, this, mul_one] at h
  exact h.symm

theorem ee_ne_of_window {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 1) : ee x ≠ ee y := by
  have hpi := Real.pi_pos
  refine circle_exp_ne (fun he => hne (mul_left_cancel₀ (by positivity) he)) ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  nlinarith

theorem continuous_ee_coe : Continuous fun x : ℝ => (ee x : ℂ) := continuous_induced_dom.comp
  continuous_ee

/-- Directions close to `ee (w y)`, for finitely many separated `w y`, have angles in the same
order. -/
theorem exists_near {Y : Type} [Finite Y] (w : Y → ℝ) (_hw : Function.Injective w)
  (h0 : ∀ y, 0 < w y) (h1 : ∀ y, w y < 1) :
    ∃ δ > 0, ∀ u : Y → Circle, (∀ y, ‖(u y : ℂ) - ee (w y)‖ < δ) → ∃ b : Y → ℝ, (∀ y, ee (b y)
      = u y) ∧ (∀ y, 0 < b y ∧ b y < 1) ∧ ∀ x y, w x < w y → b x < b y := by
  obtain ⟨θ, hθ0, hθ1, hθ, hθs⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ (∀ y, θ < w y ∧ w y < 1 - θ)
    ∧ ∀ x y, w x < w y → w x + 2 * θ < w y := by
    have e : ∀ᶠ θ : ℝ in 𝓝[>] 0, (∀ y, θ < w y ∧ w y < 1 - θ) ∧ ∀ x y, w x < w y
      → w x + 2 * θ < w y := by
      refine Eventually.and (eventually_all.mpr fun y => Eventually.and ?_ ?_)
        (eventually_all.mpr fun x => eventually_all.mpr fun y => ?_)
      · exact ((continuous_id.tendsto 0).eventually (gt_mem_nhds (h0 y))).filter_mono
          nhdsWithin_le_nhds
      · have hc : Continuous fun θ : ℝ => 1 - θ := by fun_prop
        exact ((hc.tendsto 0).eventually (lt_mem_nhds (by simpa using h1 y))).filter_mono
          nhdsWithin_le_nhds
      · by_cases hxy : w x < w y
        · have hc : Continuous fun θ : ℝ => w x + 2 * θ := by fun_prop
          have := (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hxy))
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun θ h _ => h
        · exact Eventually.of_forall fun θ h => absurd h hxy
    obtain ⟨θ, h2, h3⟩ := (e.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
    exact ⟨θ, h3.1, h3.2, h2.1, h2.2⟩
  have hne : (Icc θ (1 - θ)).Nonempty := ⟨θ, le_rfl, by linarith⟩
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := θ) (b := 1 - θ)).exists_isMinOn hne (f := fun s
    => ‖(ee s : ℂ) - 1‖) ((continuous_ee_coe.sub continuous_const).norm.continuousOn)
  have hμ : 0 < ‖(ee m : ℂ) - 1‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => ?_)
    have h1' : ee m = ee 0 := Circle.ext (by rw [h]; simp [ee])
    exact ee_ne_of_window (by linarith [hm.1] : m ≠ 0) (by rw [sub_zero, abs_lt]; constructor
      <;> linarith [hm.1, hm.2]) h1'
  refine ⟨_, hμ, fun u hu => ?_⟩
  have hb : ∀ y, ∃ b : ℝ, |b - w y| < θ ∧ ee (b) = u y := fun y => by
    obtain ⟨s, hs0, hs1, hs⟩ := exists_ee ((ee (w y))⁻¹ * u y)
    have hu' : u y = ee (w y + s) := by rw [ee_add, ← hs, mul_inv_cancel_left]
    have hsn : ‖(ee s : ℂ) - 1‖ = ‖(u y : ℂ) - ee (w y)‖ := by
      have : (u y : ℂ) - ee (w y) = ee (w y) * ((ee s : ℂ) - 1) := by
        rw [hu', ee_add]
        push_cast
        ring
      rw [this, norm_mul, Circle.norm_coe, one_mul]
    have hlt := hu y
    rw [← hsn] at hlt
    by_cases hs2 : s < θ
    · exact ⟨w y + s, by rw [add_sub_cancel_left, abs_of_nonneg hs0]; exact hs2, hu'.symm⟩
    · by_cases hs3 : 1 - θ < s
      · refine ⟨w y + s - 1, by rw [abs_lt]; constructor <;> linarith, ?_⟩
        rw [ee_one_add, hu']
      · exact absurd (hmin (⟨not_lt.mp hs2, not_lt.mp hs3⟩ : s ∈ Icc θ (1 - θ))) (not_le.mpr hlt)
  choose b hb1 hb2 using hb
  refine ⟨b, hb2, fun y => ?_, fun x y hxy => ?_⟩
  · have := abs_lt.mp (hb1 y)
    have h' := hθ y
    constructor <;> linarith [this.1, this.2, h'.1, h'.2]
  · have h1' := abs_lt.mp (hb1 x)
    have h2' := abs_lt.mp (hb1 y)
    have := hθs x y hxy
    linarith [h1'.2, h2'.1]

theorem cycOrder_congr {x y z x' y' z' : ℝ} (h1 : x < y ↔ x' < y') (h2 : y < z ↔ y' < z')
  (h3 : z < x ↔ z' < x') : CycOrder x y z ↔ CycOrder x' y' z' := by
  simp only [CycOrder, h1, h2, h3]

omit [T2Space T] in
/-- **A flower in a pad.** Here `X` is the union of the discs around the vertices. It holds the part
of the pad near each vertex `φ y`, and the part of `X` in the pad stays away from the centre. The
flower
in the chart meets the chart image of `X` in exactly its peaks `u y`. Each peak is near the place of
`φ y`, and `τ` carries it to the end `y`. -/
theorem exists_pad_flower {C : Set T} {c : T → ℂ} {g : ℂ → T} (hC : IsCompact C)
  (hch : IsChart C c g) {q : Circle → T} {Y : Set T} {φ : T → T} {A U : T → ℝ}
    (hO : PadOrder q g Y φ A U) {X : Set T}
    (hX : IsClosed X) (hfar : ∀ x ∈ C ∩ X, 1 / 2 < ‖c x‖) (hnear : ∀ y ∈ Y, ∀ᶠ z in 𝓝 (ee
      (U y) : ℂ), z ∈ closedBall (0 : ℂ) 1 → g z ∈ X) {s : ℝ} (hs : 0 < s) :
    ∃ ρ : Circle → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x ∧ ρ x < 1) ∧ ∃ u : {y // y ∈ Y} → Circle,
      (∀ y, ‖(u y : ℂ) - ee (U y.1)‖ < s) ∧ (∀ y, (ρ (u y) : ℂ) * u y ∈ c '' (C ∩ X)) ∧
      (∀ z (hz : z ≠ 0), z ∈ c '' (C ∩ X) → ‖z‖ ≤ ρ (unitOf z hz) → ∃ y, z = (ρ (u y) : ℂ) * u y)
        ∧ ∃ τ : Circle ≃ₜ Circle, PreservesCircleOrientation τ ∧ ∀ y, q (τ (u y)) = y.1 := by
  classical
  let Y' := {y // y ∈ Y}
  have : Finite Y' := hO.finite.to_subtype
  let F : Set ℂ := c '' (C ∩ X)
  have hF : IsCompact F := (hC.inter_right hX).image_of_continuousOn (hch.hc.mono inter_subset_left)
  let wf : ℝ → Y' → ℝ := fun ε y => (1 - 3 * ε) * U y.1 + ε * A y.1 + ε
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ y : Y', ‖(ee (wf ε y) : ℂ) - ee (U y.1)‖ < s / 2
    ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (t : ℂ) * ee (wf ε y) ∈ F := by
    refine eventually_all.mpr fun y => ?_
    obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.mp (hnear y.1 y.2)
    let η₁ := min (min η s) 1 / 2
    have hη₁ : 0 < η₁ := by simp only [η₁]; positivity
    have hη₂ : η₁ ≤ η / 2 := by
      have : min (min η s) 1 ≤ η := (min_le_left _ _).trans (min_le_left _ _)
      simp only [η₁]
      linarith
    have hη₃ : η₁ ≤ s / 2 := by
      have : min (min η s) 1 ≤ s := (min_le_left _ _).trans (min_le_right _ _)
      simp only [η₁]
      linarith
    have hη₄ : η₁ ≤ 1 / 2 := by
      have : min (min η s) 1 ≤ 1 := min_le_right _ _
      simp only [η₁]
      linarith
    have hc : Continuous fun ε : ℝ => (ee ((1 - 3 * ε) * U y.1 + ε * A y.1 + ε) : ℂ)
      := continuous_ee_coe.comp (by fun_prop)
    have ht : Tendsto (fun ε : ℝ => (ee ((1 - 3 * ε) * U y.1 + ε * A y.1 + ε) : ℂ)) (𝓝 0) (𝓝 (ee
      (U y.1) : ℂ)) := by
      have := hc.tendsto 0
      simpa using this
    have hev := (Metric.tendsto_nhds.mp ht η₁ hη₁).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
    refine hev.mono fun ε hε => ?_
    rw [dist_eq_norm] at hε
    refine ⟨hε.trans_le hη₃, 1 - η₁, by linarith, by linarith, ?_⟩
    have ht1 : (1 - η₁ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hn : ‖((1 - η₁ : ℝ) : ℂ) * ee (wf ε y)‖ = 1 - η₁ := by
      rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg ht1.1]
    have hmem : ((1 - η₁ : ℝ) : ℂ) * ee (wf ε y) ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, hn]
      linarith
    have hd : dist (((1 - η₁ : ℝ) : ℂ) * ee (wf ε y)) (ee (U y.1)) < η := by
      rw [dist_eq_norm]
      have : ((1 - η₁ : ℝ) : ℂ) * ee (wf ε y) - ee (U y.1) = ((ee (wf ε y) : ℂ) - ee (U y.1)) -
        ((η₁ : ℝ) : ℂ) * ee (wf ε y) := by
        push_cast
        ring
      rw [this]
      refine (norm_sub_le _ _).trans_lt ?_
      rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hη₁.le]
      have := hε
      simp only [wf]
      linarith
    exact ⟨_, ⟨hch.gm hmem, hb hd hmem⟩, hch.hg hmem⟩
  obtain ⟨ε, hev', hε0, hε1⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  let w : Y' → ℝ := wf ε
  have hA := fun y : Y' => hO.A_mem y.1 y.2
  have hU := fun y : Y' => hO.U_mem y.1 y.2
  have hp : 0 < 1 - 3 * ε := by linarith
  have hw0 : ∀ y, 0 < w y := fun y => by
    have h1 := mul_nonneg hp.le (hU y).1
    have h2 := mul_nonneg hε0.le (hA y).1
    simp only [w, wf]
    linarith
  have hw1 : ∀ y, w y < 1 := fun y => by
    have h1 := mul_le_mul_of_nonneg_left (hU y).2 hp.le
    have h2 := mul_le_mul_of_nonneg_left (hA y).2 hε0.le
    simp only [w, wf]
    linarith
  have hlt : ∀ x y : Y', A x.1 < A y.1 → w x < w y := fun x y hxy => by
    have h1 := mul_le_mul_of_nonneg_left (hO.mono x.1 x.2 y.1 y.2 hxy) hp.le
    have h2 := mul_lt_mul_of_pos_left hxy hε0
    simp only [w, wf]
    linarith
  have hAne : ∀ x y : Y', x ≠ y → A x.1 ≠ A y.1 := fun x y hne h => hne (Subtype.ext
    (hO.inj x.2 y.2 h))
  have hwi : Function.Injective w := fun x y he => by
    by_contra hne
    rcases lt_or_gt_of_ne (hAne x y hne) with h | h
    · exact (hlt x y h).ne he
    · exact (hlt y x h).ne he.symm
  have heei : Function.Injective fun y => ee (w y) := fun x y he => by
    by_contra hne
    refine ee_ne_of_window (fun h => hne (hwi h)) ?_ he
    rw [abs_lt]
    constructor <;> linarith [hw0 x, hw0 y, hw1 x, hw1 y]
  obtain ⟨δ, hδ, hnear'⟩ := exists_near w hwi hw0 hw1
  obtain ⟨ρ, hρc, hρ, u, hu, hud, hupk, hF'⟩ := exists_flower hF (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) (fun z ⟨x, hx, hz⟩ => hz ▸ hfar x hx) heei (fun y => (hev' y).2)
    (lt_min hδ (half_pos hs))
  refine ⟨ρ, hρc, hρ, u, fun y => ?_, hupk, hF', ?_⟩
  · have h1 : ‖(u y : ℂ) - ee (w y)‖ < s / 2 := (hud y).trans_le (min_le_right _ _)
    have h2 := (hev' y).1
    have : (u y : ℂ) - ee (U y.1) = ((u y : ℂ) - ee (w y)) + ((ee (w y) : ℂ) - ee (U y.1)) := by
      ring
    rw [this]
    refine (norm_add_le _ _).trans_lt ?_
    have h2' : ‖(ee (w y) : ℂ) - ee (U y.1)‖ < s / 2 := h2
    linarith
  obtain ⟨b, hbe, hb01, hbl⟩ := hnear' u fun y => (hud y).trans_le (min_le_left _ _)
  have hbi : Function.Injective b := fun x y he => hu (by rw [← hbe, ← hbe, he])
  have hto : ∀ y : Y', ∃ t, q t = y.1 := fun y => hO.sub y.2
  choose t ht using hto
  have hti : Function.Injective t := fun x y he => Subtype.ext (by rw [← ht, ← ht, he])
  have hord : ∀ x y : Y', A x.1 < A y.1 ↔ b x < b y := fun x y => by
    refine ⟨fun h => hbl x y (hlt x y h), fun h => ?_⟩
    by_contra hn
    rcases (not_lt.mp hn).lt_or_eq with h' | h'
    · exact absurd h (hbl y x (hlt y x h')).not_gt
    · have := Subtype.ext (hO.inj y.2 x.2 h')
      rw [this] at h
      exact lt_irrefl _ h
  obtain ⟨τ, hτ, hτe⟩ := exists_circle_interp b hbi (fun x y => by linarith [(hb01 x).2,
    (hb01 y).1]) t hti (fun x y z hxy hyz hxz => by
    have hc := hO.cyc (t x) (t y) (t z) (by rw [ht]; exact x.2) (by rw [ht]; exact y.2)
      (by rw [ht]; exact z.2) (fun h => hxy (hti h)) (fun h => hyz (hti h)) (fun h => hxz (hti h))
    rw [hc, ht, ht, ht]
    exact cycOrder_congr (hord x y) (hord y z) (hord z x))
  refine ⟨τ, hτ, fun y => ?_⟩
  rw [← hbe, hτe, ht]

end GraphMinor.GM19
