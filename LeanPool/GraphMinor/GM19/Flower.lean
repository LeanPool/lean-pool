/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PlaneOrientation
public import LeanPool.GraphMinor.Surface.DiscTwist

/-!
# Flowers in the plane

Step (3) of the proof of Graph Minors XIX, (15.2), page 382 joins each end of an edge to a vertex by
a tree. We use small discs around the vertices in place of trees, and so we need a closed disc that
meets a given compact set `F` in exactly one point near each of some given directions. A set `{z |
‖z‖ ≤ ρ(z / ‖z‖)}` with `ρ` continuous is a closed disc (`starHomeo`), and we call the point
`ρ(w) * w` the peak in direction `w`. For each direction `w` we take the point `z` of `F` that
minimizes `‖z‖ + L * ‖z / ‖z‖ - w‖`, and `ρ` falls away from this point just fast enough to miss
the rest of `F` (`exists_flower`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Metric Topology Filter GraphMinor.Surface

open Classical in
/-- Stretch each ray of the plane by the factor `ρ`. -/
noncomputable def starMap (ρ : Circle → ℝ) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0 else (ρ (unitOf z hz) : ℂ) * z

theorem starMap_coe (ρ : Circle → ℝ) (w : Circle) : starMap ρ w = (ρ w : ℂ) * w := by
  have hw : (w : ℂ) ≠ 0 := Circle.coe_ne_zero w
  have hu : unitOf w hw = w := by
    have := unitOf_mul 1 one_pos w (by simp [hw])
    simpa using this
  simp only [starMap, dite_eq_right hw, hu]

theorem continuous_starMap {ρ : Circle → ℝ} (hρ : Continuous ρ) : Continuous (starMap ρ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    obtain ⟨B, hB⟩ := (isCompact_range (hρ.norm)).bddAbove
    have hB' : ∀ w, ‖ρ w‖ ≤ B := fun w => hB (mem_range_self w)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 1)
    have h0 : starMap ρ 0 = 0 := by simp [starMap]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ w, ‖starMap ρ w‖ ≤ B * ‖w‖ := fun w => by
      by_cases hw : w = 0
      · simp [starMap, hw]
      · simp only [starMap, dite_eq_right hw, norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_right (hB' _) (norm_nonneg _)
    have ht : Tendsto (fun w : ℂ => B * ‖w‖) (𝓝 0) (𝓝 0) := by
      have h : Continuous fun w : ℂ => B * ‖w‖ := continuous_const.mul continuous_norm
      simpa using h.tendsto (0 : ℂ)
    exact squeeze_zero (fun _ => norm_nonneg _) hle ht
  · have hmem : {z : ℂ | z ≠ 0} ∈ 𝓝 z := isOpen_ne.mem_nhds hz
    refine ContinuousOn.continuousAt ?_ hmem
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({z : ℂ | z ≠ 0}).domRestrict (starMap ρ) = fun x : {z : ℂ // z ≠ 0} => (ρ
      (unitOf x.1 x.2) : ℂ) * x.1 := by
      funext x
      change starMap ρ x.1 = _
      simp only [starMap, dite_eq_right x.2]
    rw [heq]
    exact (Complex.continuous_ofReal.comp (hρ.comp continuous_unitOf)).mul continuous_subtype_val

theorem starMap_form (ρ : Circle → ℝ) {z : ℂ} (hz : z ≠ 0) : starMap ρ z = ((ρ
  (unitOf z hz) * ‖z‖ : ℝ) : ℂ) * unitOf z hz := by
  simp only [starMap, dite_eq_right hz]
  rw [Complex.ofReal_mul, mul_assoc, norm_mul_unitOf]

theorem starMap_ne {ρ : Circle → ℝ} (hρ : ∀ w, 0 < ρ w) {z : ℂ} (hz : z ≠ 0) : starMap ρ z ≠ 0 := by
  simp only [starMap, dite_eq_right hz]
  exact mul_ne_zero (by exact_mod_cast (hρ _).ne') hz

theorem unitOf_starMap {ρ : Circle → ℝ} (hρ : ∀ w, 0 < ρ w) {z : ℂ} (hz : z ≠ 0) : unitOf
  (starMap ρ z) (starMap_ne hρ hz) = unitOf z hz := by
  have hpos : 0 < ρ (unitOf z hz) * ‖z‖ := mul_pos (hρ _) (norm_pos_iff.mpr hz)
  have hne : ((ρ (unitOf z hz) * ‖z‖ : ℝ) : ℂ) * unitOf z hz ≠ 0 := by
    rw [← starMap_form ρ hz]
    exact starMap_ne hρ hz
  have := unitOf_mul _ hpos (unitOf z hz) hne
  simp only [starMap_form ρ hz]
  exact this

theorem starMap_inv {ρ : Circle → ℝ} (hρ : ∀ w, 0 < ρ w) (z : ℂ) : starMap (fun w => (ρ w)⁻¹)
  (starMap ρ z) = z := by
  by_cases hz : z = 0
  · simp [starMap, hz]
  · have hn := starMap_ne hρ hz
    have hu := unitOf_starMap hρ hz
    rw [starMap, dite_eq_right hn, hu]
    simp only [starMap, dite_eq_right hz]
    have hr : (ρ (unitOf z hz) : ℂ) ≠ 0 := by exact_mod_cast (hρ _).ne'
    rw [Complex.ofReal_inv, inv_mul_cancel_left₀ hr]

/-- The stretching of rays is a homeomorphism of the plane. -/
noncomputable def starHomeo {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) : ℂ ≃ₜ ℂ where
  toFun := starMap ρ
  invFun := starMap fun w => (ρ w)⁻¹
  left_inv := starMap_inv hρ
  right_inv := fun z => by
    have := starMap_inv (ρ := fun w => (ρ w)⁻¹) (fun w => inv_pos.mpr (hρ w)) z
    simpa using this
  continuous_toFun := continuous_starMap hc
  continuous_invFun := continuous_starMap (hc.inv₀ fun w => (hρ w).ne')

/-- The closed disc under the graph of `ρ`. -/
noncomputable def starDisc {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) : Set ℂ :=
  starHomeo hc hρ '' closedBall 0 1

theorem starHomeo_apply {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w)
  (z : ℂ) : starHomeo hc hρ z = starMap ρ z := rfl

theorem starHomeo_zero {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) : starHomeo hc hρ 0
  = 0 := by
  simp [starHomeo_apply, starMap]

theorem mem_starDisc {ρ : Circle → ℝ} {hc : Continuous ρ} {hρ : ∀ w, 0 < ρ w} {z : ℂ}
  (hz : z ≠ 0) : z ∈ starDisc hc hρ ↔ ‖z‖ ≤ ρ (unitOf z hz) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hz (by rw [h, starHomeo_zero])
    have hu := unitOf_starMap hρ hx0
    have hk : unitOf (starHomeo hc hρ x) hz = unitOf x hx0 := hu
    rw [hk, starHomeo_apply, starMap_form ρ hx0, norm_mul, Complex.norm_real, Circle.norm_coe,
      mul_one, Real.norm_of_nonneg (mul_pos (hρ _) (norm_pos_iff.mpr hx0)).le]
    have := mem_closedBall_zero_iff.mp hx
    nlinarith [hρ (unitOf x hx0), norm_nonneg x]
  · intro h
    refine ⟨(starHomeo hc hρ).symm z, ?_, Homeomorph.apply_symm_apply _ _⟩
    change starMap (fun w => (ρ w)⁻¹) z ∈ _
    rw [mem_closedBall_zero_iff, starMap_form _ hz, norm_mul, Complex.norm_real, Circle.norm_coe,
      mul_one, Real.norm_of_nonneg (mul_pos (inv_pos.mpr (hρ _)) (norm_pos_iff.mpr hz)).le]
    have hp := hρ (unitOf z hz)
    rw [inv_mul_le_iff₀ hp]
    simpa using h

theorem zero_mem_starDisc {ρ : Circle → ℝ} {hc : Continuous ρ} {hρ : ∀ w, 0 < ρ w} :
  (0 : ℂ) ∈ starDisc hc hρ :=
  ⟨0, by simp, starHomeo_zero hc hρ⟩

theorem starDisc_subset_ball {ρ : Circle → ℝ} {hc : Continuous ρ} {hρ : ∀ w, 0 < ρ w}
  (hlt : ∀ w, ρ w < 1) : starDisc hc hρ ⊆ ball 0 1 := by
  intro z hz
  rw [mem_ball_zero_iff]
  by_cases h0 : z = 0
  · simp [h0]
  · exact ((mem_starDisc h0).mp hz).trans_lt (hlt _)

theorem isClosedDisc_starDisc {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) :
  IsClosedDisc (starDisc hc hρ) :=
  (isClosedDisc_image_injOn isClosedDisc_closedBall.1 (starHomeo hc hρ).continuous.continuousOn
    (starHomeo hc hρ).injective.injOn).1

theorem discBd_starDisc {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) : discBd
  (starDisc hc hρ) = starHomeo hc hρ '' sphere 0 1 := by
  have := (isClosedDisc_image_injOn isClosedDisc_closedBall.1 (starHomeo hc
    hρ).continuous.continuousOn (starHomeo hc hρ).injective.injOn).2
  rwa [isClosedDisc_closedBall.2] at this

/-- The boundary of a star disc is parametrized by its peaks, in the positive direction. -/
theorem isPosParam_star {ρ : Circle → ℝ} (hc : Continuous ρ) (hρ : ∀ w, 0 < ρ w) : IsPosParam
  (starDisc hc hρ) fun w => (ρ w : ℂ) * w := by
  have hG : ∀ w : Circle, starHomeo hc hρ w = (fun w : Circle => (ρ w : ℂ) * w) w := fun w
    => starMap_coe ρ w
  have hφc : Continuous fun w : Circle => (ρ w : ℂ) * w := (Complex.continuous_ofReal.comp hc).mul
    continuous_induced_dom
  have himg := image_sphere_of_extension (starHomeo hc hρ) hG
  have hr : range (fun w : Circle => (ρ w : ℂ) * w) = discBd (starDisc hc hρ) := by
    rw [discBd_starDisc, himg]
  refine ⟨hφc, fun a b h => ?_, hr, fun z hz => ?_⟩
  · have h' : starHomeo hc hρ a = starHomeo hc hρ b := by rw [hG, hG]; exact h
    exact Circle.ext ((starHomeo hc hρ).injective h')
  · rw [discInt_eq_of_extension (starHomeo hc hρ) hG hr rfl] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [wind_eq_of_ball (starHomeo hc hρ) hφc hG ha (mem_ball_self one_pos), starHomeo_zero]
    have h0 : ∀ t : ℝ, (ρ (Circle.exp t) : ℂ) * (Circle.exp t) - 0 ≠ 0 := fun t => by
      rw [sub_zero]
      exact mul_ne_zero (by exact_mod_cast (hρ _).ne') (Circle.coe_ne_zero _)
    have hang : IsAngle (fun t : ℝ => (ρ (Circle.exp t) : ℂ) * (Circle.exp t) - 0) fun t => t := by
      refine ⟨continuous_id, fun t => ?_⟩
      simp only [sub_zero, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
        Real.norm_of_nonneg (hρ _).le]
      rw [Circle.coe_exp]
    rw [wind, hang.turn_eq h0]
    have := Real.pi_pos
    linarith

/-- **Flowers.** Let `F` be a compact set off the ball of radius `ρ₀`, and let `w` be finitely many
directions, each with a point of `F` strictly inside the unit circle. Then some star disc inside
the open unit ball meets `F` in exactly its peaks in directions `u`, with `u y` as near to `w y` as
we like. -/
theorem exists_flower {Y : Type} [Finite Y] {F : Set ℂ} (hF : IsCompact F) {ρ₀ : ℝ} (h0 : 0 < ρ₀)
  (h1 : ρ₀ < 1) (hρ₀ : ∀ z ∈ F, ρ₀ < ‖z‖) {w : Y → Circle} (hw : Function.Injective w)
    (ht : ∀ y, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (t : ℂ) * w y ∈ F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : Circle → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x ∧ ρ x < 1) ∧ ∃ u : Y
      → Circle, Function.Injective u ∧ (∀ y, ‖(u y : ℂ) - w y‖ < δ) ∧ (∀ y, (ρ
        (u y) : ℂ) * u y ∈ F) ∧
      ∀ z (hz : z ≠ 0), z ∈ F → ‖z‖ ≤ ρ (unitOf z hz) → ∃ y, z = (ρ (u y) : ℂ) * u y := by
  classical
  have := Fintype.ofFinite Y
  have hne0 : ∀ z ∈ F, z ≠ 0 := fun z hz h => by
    have := hρ₀ z hz
    rw [h, norm_zero] at this
    linarith
  obtain ⟨L, hL0, hLδ, hLw⟩ : ∃ L : ℝ, 0 < L ∧ 1 / L < δ ∧ ∀ x y, x ≠ y → 2 / L < ‖(w x : ℂ) - w y‖
    := by
    have hlim : ∀ c : ℝ, Tendsto (fun L : ℝ => c / L) atTop (𝓝 0) := fun c
      => tendsto_const_nhds.div_atTop tendsto_id
    have e1 : ∀ᶠ L : ℝ in atTop, 1 / L < δ := (hlim 1).eventually (gt_mem_nhds hδ)
    have e2 : ∀ᶠ L : ℝ in atTop, ∀ x y, x ≠ y → 2 / L < ‖(w x : ℂ) - w y‖ := by
      refine eventually_all.mpr fun x => eventually_all.mpr fun y => ?_
      by_cases hxy : x = y
      · exact Eventually.of_forall fun L h => absurd hxy h
      · have hp : 0 < ‖(w x : ℂ) - w y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hxy (hw
        (Circle.ext h)))
        exact ((hlim 2).eventually (gt_mem_nhds hp)).mono fun L hL _ => hL
    obtain ⟨L, h1', h2', h3'⟩ := (e1.and (e2.and (eventually_gt_atTop 0))).exists
    exact ⟨L, h3', h1', h2'⟩
  let dir : ℂ → ℂ := fun z => ((‖z‖ : ℝ) : ℂ)⁻¹ * z
  have hdir : ∀ z (hz : z ≠ 0), dir z = unitOf z hz := fun z hz => (coe_unitOf z hz).symm
  have hdc : ContinuousOn dir F := fun z hz => by
    refine ContinuousAt.continuousWithinAt ?_
    have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hne0 z hz)
    exact ((Complex.continuous_ofReal.comp continuous_norm).continuousAt.inv₀ hn).mul
      continuousAt_id
  let Q : Y → ℂ → ℝ := fun y z => ‖z‖ + L * ‖dir z - w y‖
  have hQc : ∀ y, ContinuousOn (Q y) F := fun y =>
    continuous_norm.continuousOn.add (continuousOn_const.mul (hdc.sub continuousOn_const).norm)
  have hmin : ∀ y, ∃ z ∈ F, IsMinOn (Q y) F z := fun y => by
    obtain ⟨t, _, _, ht'⟩ := ht y
    exact hF.exists_isMinOn ⟨_, ht'⟩ (hQc y)
  choose z hzF hzmin using hmin
  have hzne : ∀ y, z y ≠ 0 := fun y => hne0 _ (hzF y)
  let u : Y → Circle := fun y => unitOf (z y) (hzne y)
  have hdu : ∀ y, dir (z y) = u y := fun y => hdir _ _
  have hQ1 : ∀ y, Q y (z y) < 1 := fun y => by
    obtain ⟨t, ht0, ht1, ht'⟩ := ht y
    refine (hzmin y ht').trans_lt ?_
    have hne : (t : ℂ) * w y ≠ 0 := hne0 _ ht'
    have h1 : dir ((t : ℂ) * w y) = w y := by rw [hdir _ hne, unitOf_mul t ht0 (w y) hne]
    have h2 : ‖(t : ℂ) * w y‖ = t := by
      rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg ht0.le]
    change ‖(t : ℂ) * w y‖ + L * ‖dir ((t : ℂ) * w y) - w y‖ < 1
    rw [h1, h2, sub_self, norm_zero, mul_zero, add_zero]
    exact ht1
  have hzn : ∀ y, ρ₀ < ‖z y‖ := fun y => hρ₀ _ (hzF y)
  have hclose : ∀ y, L * ‖(u y : ℂ) - w y‖ < 1 := fun y => by
    have := hQ1 y
    have h2 : Q y (z y) = ‖z y‖ + L * ‖(u y : ℂ) - w y‖ := by simp only [Q, hdu]
    rw [h2] at this
    linarith [hzn y]
  have hclose' : ∀ y, ‖(u y : ℂ) - w y‖ < 1 / L := fun y => by
    rw [lt_div_iff₀ hL0]
    linarith [hclose y]
  let b : Option Y → Circle → ℝ := fun a x => match a with
    | none => ρ₀
    | some y => Q y (z y) - L * ‖(x : ℂ) - w y‖ - ‖(x : ℂ) - u y‖
  let ρ : Circle → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty fun a => b a x
  have hbc : ∀ a, Continuous (b a) := by
    rintro (_ | y)
    · exact continuous_const
    · change Continuous fun x : Circle => Q y (z y) - L * ‖(x : ℂ) - w y‖ - ‖(x : ℂ) - u y‖
      have hcoe : Continuous fun x : Circle => (x : ℂ) := continuous_induced_dom
      exact (continuous_const.sub (continuous_const.mul (hcoe.sub continuous_const).norm)).sub
        (hcoe.sub continuous_const).norm
  have hρc : Continuous ρ := Continuous.finset_sup'_apply Finset.univ_nonempty fun a _ => hbc a
  have hle : ∀ a x, b a x ≤ ρ x := fun a x => Finset.le_sup' (fun a => b a x) (Finset.mem_univ a)
  have hb1 : ∀ a x, b a x < 1 := by
    rintro (_ | y) x
    · exact h1
    · change Q y (z y) - L * ‖(x : ℂ) - w y‖ - ‖(x : ℂ) - u y‖ < 1
      have := mul_nonneg hL0.le (norm_nonneg ((x : ℂ) - w y))
      linarith [hQ1 y, norm_nonneg ((x : ℂ) - u y)]
  have hρ0 : ∀ x, ρ₀ ≤ ρ x := fun x => hle none x
  have hρ1 : ∀ x, ρ x < 1 := fun x => (Finset.sup'_lt_iff _).mpr fun a _ => hb1 a x
  have hpeak : ∀ y, ρ (u y) = ‖z y‖ := fun y => by
    refine le_antisymm (Finset.sup'_le _ _ ?_) ?_
    · rintro (_ | x) -
      · exact (hzn y).le
      · change Q x (z x) - L * ‖(u y : ℂ) - w x‖ - ‖(u y : ℂ) - u x‖ ≤ ‖z y‖
        by_cases hxy : x = y
        · subst hxy
          simp only [Q, hdu, sub_self, norm_zero]
          linarith
        · have h2 := hLw x y hxy
          rw [div_lt_iff₀ hL0] at h2
          have htri : ‖(w x : ℂ) - w y‖ ≤ ‖(u y : ℂ) - w x‖ + ‖(u y : ℂ) - w y‖ := by
            have : (w x : ℂ) - w y = ((u y : ℂ) - w y) - ((u y : ℂ) - w x) := by ring
            rw [this]
            exact (norm_sub_le _ _).trans (by rw [add_comm])
          have h3 := mul_le_mul_of_nonneg_right htri hL0.le
          have h4 := hclose y
          have h5 := hQ1 x
          have h6 := norm_nonneg ((u y : ℂ) - u x)
          nlinarith [hzn y]
    · have := hle (some y) (u y)
      refine le_trans (le_of_eq ?_) this
      change ‖z y‖ = Q y (z y) - L * ‖(u y : ℂ) - w y‖ - ‖(u y : ℂ) - u y‖
      simp only [Q, hdu, sub_self, norm_zero]
      ring
  have hpk : ∀ y, (ρ (u y) : ℂ) * u y = z y := fun y => by
    rw [hpeak]
    exact norm_mul_unitOf _ _
  refine ⟨ρ, hρc, fun x => ⟨h0.trans_le (hρ0 x), hρ1 x⟩, u, fun x y he => ?_, fun y =>
    (hclose' y).trans hLδ, fun y => by rw [hpk]; exact hzF y, fun v hv hvF hvle => ?_⟩
  · by_contra hxy
    have h2 := hLw x y hxy
    have htri : ‖(w x : ℂ) - w y‖ ≤ ‖(u x : ℂ) - w x‖ + ‖(u y : ℂ) - w y‖ := by
      have : (w x : ℂ) - w y = ((u y : ℂ) - w y) - ((u x : ℂ) - w x) := by rw [he]; ring
      rw [this]
      exact (norm_sub_le _ _).trans (by rw [add_comm])
    have h3 := hclose' x
    have h4 := hclose' y
    have : (2 : ℝ) / L = 1 / L + 1 / L := by ring
    linarith
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun a => b a (unitOf v hv)
    have ha' : ρ (unitOf v hv) = b a (unitOf v hv) := ha
    rcases a with _ | y
    · have : ρ (unitOf v hv) = ρ₀ := ha'
      linarith [hρ₀ v hvF]
    · refine ⟨y, ?_⟩
      have hb' : ρ (unitOf v hv) = Q y (z y) - L * ‖(unitOf v hv : ℂ) - w y‖ - ‖(unitOf v hv : ℂ) -
        u y‖ := ha'
      have hm : Q y (z y) ≤ Q y v := hzmin y hvF
      have hQv : Q y v = ‖v‖ + L * ‖(unitOf v hv : ℂ) - w y‖ := by simp only [Q, hdir v hv]
      have hzero : ‖(unitOf v hv : ℂ) - u y‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
      have hequ : unitOf v hv = u y := Circle.ext (sub_eq_zero.mp (norm_eq_zero.mp hzero))
      have hQz : Q y (z y) = ‖z y‖ + L * ‖(u y : ℂ) - w y‖ := by simp only [Q, hdu]
      rw [hpk, ← norm_mul_unitOf v hv, hequ]
      have hnorm : ‖v‖ = ‖z y‖ := by
        rw [hequ] at hQv hvle
        rw [hpeak] at hvle
        linarith
      rw [hnorm]
      exact norm_mul_unitOf _ _

end GraphMinor.GM19
