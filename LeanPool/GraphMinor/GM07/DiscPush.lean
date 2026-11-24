/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CapMap

/-!
# Pushing a set out of a closed disc

Let `Δ` be a closed disc and `p` a point of its inside. Radial projection from `p` moves all of `Δ -
p` to the boundary. Given a
point `v` of the boundary and an open set `N` around `v`, we can choose `p` so that only points of
`N` go to `v` (`exists_disc_push`).
Möbius maps of the unit disc give a chart with `p` at the centre.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface Complex

universe u

local notation "𝕀" => unitInterval

/-- The Möbius map of the unit disc that takes `c` to `0`. -/
noncomputable def mobius (c z : ℂ) : ℂ := (z - c) / (1 - (starRingEnd ℂ) c * z)

theorem mobius_denom_ne {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) : 1 - (starRingEnd ℂ) c * z ≠ 0
  := by
  intro h
  have h1 : (starRingEnd ℂ) c * z = 1 := by
    linear_combination -h
  have h2 : ‖(starRingEnd ℂ) c * z‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_conj] at h2
  nlinarith [norm_nonneg c, norm_nonneg z]

/-- `|1 - cBar z|² - |z - c|² = (1 - |z|²)(1 - |c|²)`. -/
theorem mobius_identity (c z : ℂ) :
    ‖1 - (starRingEnd ℂ) c * z‖ ^ 2 - ‖z - c‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖c‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem norm_mobius_le {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) : ‖mobius c z‖ ≤ 1 := by
  have hd := mobius_denom_ne hc hz
  have hp : 0 < ‖1 - (starRingEnd ℂ) c * z‖ := norm_pos_iff.mpr hd
  rw [mobius, norm_div, div_le_one hp]
  have h1 := mobius_identity c z
  have h2 : 0 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖c‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg z]) (by nlinarith [norm_nonneg c])
  have h3 : ‖z - c‖ ^ 2 ≤ ‖1 - (starRingEnd ℂ) c * z‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hp.le two_ne_zero).mp h3

theorem norm_mobius_eq_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ = 1) : ‖mobius c z‖ = 1 := by
  have hd := mobius_denom_ne hc hz.le
  have hp : 0 < ‖1 - (starRingEnd ℂ) c * z‖ := norm_pos_iff.mpr hd
  rw [mobius, norm_div, div_eq_one_iff_eq hp.ne']
  have h1 := mobius_identity c z
  rw [hz] at h1
  have h3 : ‖z - c‖ ^ 2 = ‖1 - (starRingEnd ℂ) c * z‖ ^ 2 := by nlinarith
  exact (pow_left_inj₀ (norm_nonneg _) hp.le two_ne_zero).mp h3

theorem mobius_neg_mobius {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) : mobius (-c) (mobius c z) = z
  := by
  have hd := mobius_denom_ne hc hz
  have hw : mobius c z * (1 - (starRingEnd ℂ) c * z) = z - c := by
    rw [mobius]
    exact div_mul_cancel₀ _ hd
  have key : mobius c z + c = z * (1 + (starRingEnd ℂ) c * mobius c z) := by
    apply mul_right_cancel₀ hd
    linear_combination (1 - z * (starRingEnd ℂ) c) * hw
  have hdenom : 1 - (starRingEnd ℂ) (-c) * mobius c z = 1 + (starRingEnd ℂ) c * mobius c z := by
    simp
  have hne : 1 + (starRingEnd ℂ) c * mobius c z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at key
    have h1 : mobius c z = -c := by linear_combination key
    rw [h1] at h0
    have h2 := mobius_denom_ne (c := c) (z := c) hc hc.le
    apply h2
    linear_combination h0
  change (mobius c z - -c) / (1 - (starRingEnd ℂ) (-c) * mobius c z) = z
  rw [sub_neg_eq_add, hdenom, div_eq_iff hne, key]

theorem mobius_mobius_neg {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) : mobius c (mobius (-c) z) = z
  := by
  have h := mobius_neg_mobius (c := -c) (by simpa using hc) hz
  rwa [neg_neg] at h

theorem continuousOn_mobius {c : ℂ} (hc : ‖c‖ < 1) : ContinuousOn (mobius c) (closedBall 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  exact mobius_denom_ne hc (mem_closedBall_zero_iff.mp hz)

/-- A chart of a closed disc with a given point at the centre. -/
theorem IsChart.recenter {S : Type u} [TopologicalSpace S] {D : Set S} {h : S → ℂ} {g : ℂ → S}
  (cc : IsChart D h g)
    {c : ℂ} (hc : ‖c‖ < 1) : IsChart D (fun x => mobius c (h x)) (fun z => g (mobius (-c) z)) := by
  have hc' : ‖-c‖ < 1 := by simpa using hc
  have hb : ∀ {c : ℂ}, ‖c‖ < 1 → MapsTo (mobius c) (closedBall 0 1) (closedBall 0 1) := fun hc z hz
    =>
    mem_closedBall_zero_iff.mpr (norm_mobius_le hc (mem_closedBall_zero_iff.mp hz))
  refine ⟨(continuousOn_mobius hc).comp cc.hc cc.hm, cc.gc.comp (continuousOn_mobius hc')
    (hb hc'), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => hb hc (cc.hm hx)
  · exact fun z hz => cc.gm (hb hc' hz)
  · intro x hx
    change g (mobius (-c) (mobius c (h x))) = x
    rw [mobius_neg_mobius hc (mem_closedBall_zero_iff.mp (cc.hm hx)), cc.gh hx]
  · intro z hz
    change mobius c (h (g (mobius (-c) z))) = z
    rw [cc.hg (hb hc' hz), mobius_mobius_neg hc (mem_closedBall_zero_iff.mp hz)]
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : h x ∈ sphere (0 : ℂ) 1 := cc.bd ▸ mem_image_of_mem h hx
      exact mem_sphere_zero_iff_norm.mpr (norm_mobius_eq_one hc (mem_sphere_zero_iff_norm.mp h1))
    · intro hw
      have hw1 := mem_sphere_zero_iff_norm.mp hw
      have h1 : mobius (-c) w ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr
        (norm_mobius_eq_one hc' hw1)
      rw [← cc.bd] at h1
      obtain ⟨x, hx, he⟩ := h1
      exact ⟨x, hx, by
        change mobius c (h x) = w
        rw [he, mobius_mobius_neg hc hw1.le]⟩

variable {S : Type u} [TopologicalSpace S]

/-- Radial projection in a chart: for a compact set that misses the centre, a homotopy into the
complement of the inside of the
disc, fixing what lies off the inside. -/
theorem exists_radial_push [T2Space S] {D : Set S} {h : S → ℂ} {g : ℂ → S} (cc : IsChart D h g)
  (hD : IsClosedDisc D)
    {K : Set S} (hK : IsClosed K) (h0 : g 0 ∉ K) (hdisc : IsClosed (discInt D)ᶜ) :
    ∃ R : 𝕀 × S → S, ContinuousOn R (univ ×ˢ K) ∧ (∀ y, R (0, y) = y) ∧ (∀ t y, y ∉ discInt D → R
      (t, y) = y) ∧
      (∀ y ∈ K, y ∈ D → ‖h y‖ ≠ 0 ∧ R (1, y) = g (h y / (‖h y‖ : ℂ))) ∧ (∀ t, ∀ y ∈ K, y ∈ D → R
        (t, y) ∈ D) := by
  classical
  have hsphere : ∀ y ∈ D, y ∉ discInt D → ‖h y‖ = 1 := fun y hy hn => by
    have h1 : y ∈ discBd D := by
      by_contra h2
      exact hn ⟨hy, h2⟩
    exact mem_sphere_zero_iff_norm.mp (cc.bd ▸ mem_image_of_mem h h1)
  have hne : ∀ y ∈ K, y ∈ D → ‖h y‖ ≠ 0 := fun y hy hyD hn => by
    have h1 : h y = 0 := norm_eq_zero.mp hn
    apply h0
    rw [← h1, cc.gh hyD]
    exact hy
  let B : 𝕀 → ℂ → ℂ := fun t z => (((1 - t.1 : ℝ) : ℂ) + (t.1 : ℂ) / (‖z‖ : ℂ)) * z
  have hBb : ∀ t, ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 0 → ‖B t z‖ ≤ 1 := fun t z hz h0' => by
    have h1 : B t z = ((1 - t.1 : ℝ) : ℂ) * z + (t.1 : ℂ) * (z / (‖z‖ : ℂ)) := by
      simp only [B]
      ring
    have ht0 := t.2.1
    have ht1 := t.2.2
    have h2 : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      have : ‖z‖ ≠ 0 := by simpa using h0'
      simp [this]
    calc ‖B t z‖ ≤ ‖((1 - t.1 : ℝ) : ℂ) * z‖ + ‖(t.1 : ℂ) * (z / (‖z‖ : ℂ))‖ := by
          rw [h1]
          exact norm_add_le _ _
      _ = (1 - t.1) * ‖z‖ + t.1 := by
        rw [norm_mul, norm_mul, h2, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg ht0, mul_one]
      _ ≤ 1 := by nlinarith
  let R : 𝕀 × S → S := fun q => if q.2 ∈ discInt D then g (B q.1 (h q.2)) else q.2
  have hBone : ∀ t, ∀ z : ℂ, ‖z‖ = 1 → B t z = z := fun t z hz => by
    simp [B, hz]
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · have hA : IsClosed (univ ×ˢ (K ∩ D) : Set (𝕀 × S)) := isClosed_univ.prod
      (hK.inter hD.isCompact.isClosed)
    have hB : IsClosed (univ ×ˢ (K ∩ (discInt D)ᶜ) : Set (𝕀 × S)) := isClosed_univ.prod
      (hK.inter hdisc)
    have hcov : (univ ×ˢ K : Set (𝕀 × S)) = (univ ×ˢ (K ∩ D)) ∪ (univ ×ˢ (K ∩ (discInt D)ᶜ)) := by
      ext ⟨t, y⟩
      simp only [mem_prod, mem_univ, true_and, mem_union, mem_inter_iff, mem_compl_iff]
      constructor
      · intro hy
        by_cases hi : y ∈ discInt D
        · exact .inl ⟨hy, hi.1⟩
        · exact .inr ⟨hy, hi⟩
      · rintro (hy | hy) <;> exact hy.1
    have h1 : ContinuousOn R (univ ×ˢ (K ∩ D)) := by
      have he : EqOn (fun q : 𝕀 × S => g (B q.1 (h q.2))) R (univ ×ˢ (K ∩ D)) := by
        rintro ⟨t, y⟩ ⟨-, hy, hyD⟩
        simp only [R]
        split_ifs with hi
        · rfl
        · rw [hBone t _ (hsphere y hyD hi), cc.gh hyD]
      refine ContinuousOn.congr ?_ he.symm
      have hhc : ContinuousOn (fun q : 𝕀 × S => h q.2) (univ ×ˢ (K ∩ D)) :=
        cc.hc.comp continuousOn_snd fun q hq => hq.2.2
      have hnorm : ContinuousOn (fun q : 𝕀 × S => ((‖h q.2‖ : ℝ) : ℂ)) (univ ×ˢ (K ∩ D)) :=
        Complex.continuous_ofReal.comp_continuousOn hhc.norm
      have ht : Continuous fun q : 𝕀 × S => ((q.1.1 : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      have ht' : Continuous fun q : 𝕀 × S => ((1 - q.1.1 : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.comp
          continuous_fst))
      have hb : ContinuousOn (fun q : 𝕀 × S => B q.1 (h q.2)) (univ ×ˢ (K ∩ D)) :=
        (ht'.continuousOn.add (ht.continuousOn.div hnorm fun q hq => by
          have := hne q.2 hq.2.1 hq.2.2
          simpa using this)).mul hhc
      refine cc.gc.comp hb fun q hq => ?_
      refine mem_closedBall_zero_iff.mpr (hBb q.1 _ (mem_closedBall_zero_iff.mp (cc.hm hq.2.2)) ?_)
      exact norm_ne_zero_iff.mp (hne q.2 hq.2.1 hq.2.2)
    have h2 : ContinuousOn R (univ ×ˢ (K ∩ (discInt D)ᶜ)) := by
      refine continuous_snd.continuousOn.congr ?_
      rintro ⟨t, y⟩ ⟨-, -, hi⟩
      simp only [R]
      rw [ite_eq_right hi]
    rw [hcov]
    exact h1.union_of_isClosed h2 hA hB
  · intro y
    simp only [R]
    split_ifs with hy
    · simp [B, cc.gh hy.1]
    · rfl
  · intro t y hy
    simp [R, hy]
  · intro y hy hyD
    refine ⟨hne y hy hyD, ?_⟩
    by_cases hi : y ∈ discInt D
    · have h1 : (((1 - (1 : 𝕀).1 : ℝ) : ℂ) + ((1 : 𝕀).1 : ℂ) / (‖h y‖ : ℂ)) * h y = h y /
        (‖h y‖ : ℂ) := by
        simp
        ring
      simp only [R, ite_eq_left hi, B, h1]
    · have h1 := hsphere y hyD hi
      simp only [R, ite_eq_right hi, h1]
      simp [cc.gh hyD]
  · intro t y hy hyD
    simp only [R]
    split_ifs with hi
    · refine cc.gm (mem_closedBall_zero_iff.mpr (hBb t _ (mem_closedBall_zero_iff.mp
        (cc.hm hyD)) ?_))
      exact norm_ne_zero_iff.mp (hne y hy hyD)
    · exact hyD

/-- The point at the centre can be chosen so that the radial projection takes only points near `v`
to `v`. -/
theorem exists_centre_near {D : Set S} {h : S → ℂ} {g : ℂ → S}
  (cc : IsChart D h g) {v : S} (hv : v ∈ discBd D)
    {N : Set S} (hN : IsOpen N) (hvN : v ∈ N) :
    ∃ c : ℂ, ‖c‖ < 1 ∧ g c ∈ N ∧ ∀ y ∈ D, h y ≠ c → mobius c (h y) / (‖mobius c (h y)‖ : ℂ)
      = mobius c (h v) → y ∈ N := by
  have hu : ‖h v‖ = 1 := mem_sphere_zero_iff_norm.mp (cc.bd ▸ mem_image_of_mem h hv)
  have hvD : v ∈ D := Surface.discBd_subset _ hv
  set u := h v with hudef
  have hcont : ContinuousOn (fun s : ℝ => g ((s : ℂ) * u)) (Icc 0 1) := by
    refine cc.gc.comp (by fun_prop) fun s hs => ?_
    rw [mem_closedBall_zero_iff, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact hs.2
  have hg1 : g ((1 : ℝ) * u) = v := by
    simp only [ofReal_one, one_mul]
    exact cc.gh hvD
  have hnh : (fun s : ℝ => g ((s : ℂ) * u)) ⁻¹' N ∈ 𝓝[Icc 0 1] (1 : ℝ) :=
    (hcont 1 ⟨zero_le_one, le_rfl⟩) (hN.mem_nhds (by
      change g (((1 : ℝ) : ℂ) * u) ∈ N
      rw [hg1]
      exact hvN))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnh
  set a : ℝ := max (1 / 2) (1 - ε / 2) with ha
  have ha1 : a < 1 := max_lt (by norm_num) (by linarith)
  have ha0 : 1 / 2 ≤ a := le_max_left _ _
  have hIcc : ∀ s ∈ Icc a 1, g ((s : ℂ) * u) ∈ N := fun s hs => by
    refine hball ⟨?_, ?_⟩
    · rw [mem_ball, Real.dist_eq, abs_lt]
      have := le_max_right (1 / 2 : ℝ) (1 - ε / 2)
      constructor <;> linarith [hs.1, hs.2]
    · exact ⟨by linarith [hs.1], hs.2⟩
  have hc : ‖(a : ℂ) * u‖ < 1 := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact ha1
  refine ⟨(a : ℂ) * u, hc, hIcc a ⟨le_rfl, ha1.le⟩, fun y hy hne he => ?_⟩
  have huu : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  have hzn : ‖h y‖ ≤ 1 := mem_closedBall_zero_iff.mp (cc.hm hy)
  have hmu : mobius ((a : ℂ) * u) u = u := by
    have hd : (1 : ℂ) - (a : ℂ) ≠ 0 := by
      have : ((1 - a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (show 1 - a ≠ 0 by linarith)
      simpa using this
    rw [mobius, map_mul, Complex.conj_ofReal, mul_assoc, huu, mul_one]
    field_simp
  rw [hmu] at he
  set w := mobius ((a : ℂ) * u) (h y) with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : h y - (a : ℂ) * u = 0 := by
      have h2 := mobius_denom_ne hc hzn
      have h3 := div_eq_zero_iff.mp (show (h y - (a : ℂ) * u) / (1 - (starRingEnd ℂ)
        ((a : ℂ) * u) * h y) = 0 from h0)
      exact h3.resolve_right h2
    exact hne (sub_eq_zero.mp h1)
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hwu : w = ((‖w‖ : ℝ) : ℂ) * u := by
    have hc0 : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwn
    rw [← he, mul_div_cancel₀ _ hc0]
  set τ := ‖w‖ with hτ
  have hτ0 : 0 < τ := lt_of_le_of_ne (norm_nonneg _) hwn.symm
  have hτ1 : τ ≤ 1 := norm_mobius_le hc hzn
  have hback := mobius_neg_mobius hc hzn
  rw [← hw, hwu] at hback
  have hden : (0 : ℝ) < 1 + a * τ := by nlinarith
  have hs : h y = (((τ + a) / (1 + a * τ) : ℝ) : ℂ) * u := by
    rw [← hback, mobius, map_neg, map_mul, Complex.conj_ofReal, neg_mul, sub_neg_eq_add]
    have h1 : (a : ℂ) * (starRingEnd ℂ) u * ((τ : ℂ) * u) = (a : ℂ) * τ := by
      linear_combination (a : ℂ) * τ * huu
    rw [h1]
    have hd : (1 : ℂ) + (a : ℂ) * τ ≠ 0 := by
      have : ((1 + a * τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden.ne'
      simpa using this
    push_cast
    field_simp
    ring
  have hmem : (τ + a) / (1 + a * τ) ∈ Icc a 1 := by
    constructor
    · rw [le_div_iff₀ hden]
      have h5 : a * a ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h5 hτ0.le]
    · rw [div_le_one hden]
      nlinarith
  have := hIcc _ hmem
  rwa [← hs, cc.gh hy] at this

/-- Project a compact set off the inside of a closed disc, from a point of the inside that it
misses. The second conclusion is about
the map at time one. The last one controls what goes to a point `v` of the boundary. -/
theorem exists_disc_push [T2Space S] {D K : Set S} (hD : IsClosedDisc D) (hint : IsOpen
  (discInt D)) (hK : IsClosed K)
    {h : S → ℂ} {g : ℂ → S} (cc : IsChart D h g) {c : ℂ} (hc : ‖c‖ < 1) (hcK : g c ∉ K) :
    ∃ R : 𝕀 × S → S, ContinuousOn R (univ ×ˢ K) ∧ (∀ y, R (0, y) = y) ∧
      (∀ y ∈ K, y ∉ discInt D → R (1, y) = y) ∧ (∀ y ∈ K, y ∈ discInt D → R (1, y) ∈ discBd D) ∧
      ∀ y ∈ K, y ∈ D → R (1, y) = g (mobius (-c) (mobius c (h y) / (‖mobius c (h y)‖ : ℂ))) := by
  have cc' := IsChart.recenter cc hc
  have hg0 : mobius (-c) 0 = c := by simp [mobius]
  have h0 : g (mobius (-c) 0) ∉ K := by rwa [hg0]
  obtain ⟨R, h1, h2, h3, h4, -⟩ := exists_radial_push cc' hD hK h0 hint.isClosed_compl
  refine ⟨R, h1, h2, fun y _ hy => h3 1 y hy, fun y hy hi => ?_, fun y hy hyD => (h4 y hy hyD).2⟩
  obtain ⟨hne, he⟩ := h4 y hy hi.1
  rw [he]
  set w := mobius c (h y) with hw
  have hb : w / (‖w‖ : ℂ) ∈ sphere (0 : ℂ) 1 := by
    have hwn : (‖w‖ : ℝ) ≠ 0 := hne
    simp [hwn]
  rw [← cc'.bd] at hb
  obtain ⟨x, hx, hxe⟩ := hb
  have := cc'.gh (Surface.discBd_subset _ hx)
  change g (mobius (-c) (mobius c (h x))) = x at this
  change mobius c (h x) = _ at hxe
  rw [← hxe, this]
  exact hx

end GraphMinor.GM07
