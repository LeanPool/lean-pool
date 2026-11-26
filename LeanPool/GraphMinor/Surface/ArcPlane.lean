/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Schoenflies
public import LeanPool.GraphMinor.Surface.ArcInPath
public import LeanPool.GraphMinor.Surface.PlaneLog
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween

/-!
# An arc in the plane lies on an `O`-arc

Every arc of the plane is part of an `O`-arc (`exists_closing_arc`), so by the Schoenflies theorem
some homeomorphism of the plane maps it to an arc of the unit circle (`exists_straight`).

To close an arc we must reach its two ends from the outside. Take a double cover of the plane
branched at the two ends: the Joukowski map `w ↦ (w + 1 / w) / 2`, after an affine change that puts
the ends at `-1` and `1`. The preimage of the arc is an `O`-arc through `-1` and `1`. Each side of
an `O`-arc is simple by the Schoenflies theorem, and the side that misses the pole `0` maps down to
a path between the two ends that misses the rest of the arc.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Complex

local notation "𝕀" => unitInterval

/-- The Joukowski map. -/
noncomputable def jou (w : ℂ) : ℂ := (w + w⁻¹) / 2

/-- Every continuous function on the open unit interval without zeros, which extends continuously to
the closed interval, has a continuous square root that vanishes at the ends. -/
theorem exists_sqrt_of_ends {d : 𝕀 → ℂ} (hd : Continuous d) (h0 : d 0 = 0) (h1 : d 1 = 0)
    (hne : ∀ t, t ≠ 0 → t ≠ 1 → d t ≠ 0) : ∃ r : 𝕀 → ℂ, Continuous r ∧ ∀ t, r t ^ 2 = d t := by
  classical
  have hmem : ∀ x : ℝ, (x / (1 + |x|) + 1) / 2 ∈ Ioo (0 : ℝ) 1 := fun x => by
    have hp : 0 < 1 + |x| := by positivity
    have h1 : -(1 + |x|) < x := by linarith [neg_abs_le x]
    have h2 : x < 1 + |x| := by linarith [le_abs_self x]
    have h3 : -1 < x / (1 + |x|) := by rw [lt_div_iff₀ hp]; linarith
    have h4 : x / (1 + |x|) < 1 := by rw [div_lt_iff₀ hp]; linarith
    constructor <;> linarith
  let τ : ℝ → 𝕀 := fun x => ⟨(x / (1 + |x|) + 1) / 2, (hmem x).1.le, (hmem x).2.le⟩
  have hτc : Continuous τ := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.div_const (Continuous.add (Continuous.div continuous_id (by fun_prop) fun x
      => ?_) continuous_const) _
    positivity
  let ν : 𝕀 → ℝ := fun t => (2 * t.1 - 1) / (1 - |2 * t.1 - 1|)
  have hτν : ∀ t : 𝕀, t ≠ 0 → t ≠ 1 → τ (ν t) = t ∧ ContinuousAt ν t := by
    intro t h0' h1'
    have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => h0' (Subtype.ext h.symm)
    have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => h1' (Subtype.ext h)
    have hab : |2 * t.1 - 1| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hp : 0 < 1 - |2 * t.1 - 1| := by linarith
    constructor
    · apply Subtype.ext
      change (ν t / (1 + |ν t|) + 1) / 2 = t.1
      have h2 : |ν t| = |2 * t.1 - 1| / (1 - |2 * t.1 - 1|) := by
        simp only [ν]
        rw [abs_div, abs_of_pos hp]
      rw [h2]
      have h3 : 1 + |2 * t.1 - 1| / (1 - |2 * t.1 - 1|) = 1 / (1 - |2 * t.1 - 1|) := by
        field_simp
        ring
      rw [h3]
      simp only [ν]
      field_simp
      ring
    · refine ContinuousAt.div (by fun_prop) (by fun_prop) hp.ne'
  obtain ⟨g, hg, hfg⟩ := hasLogOn_univ_of_ne_zero (E := ℝ) (f := fun x => d (τ x)) (hd.comp hτc)
    (fun x => by
    apply hne
    · intro h
      have := congrArg Subtype.val h
      exact (hmem x).1.ne' this
    · intro h
      have := congrArg Subtype.val h
      exact (hmem x).2.ne this)
  have hgc : Continuous g := continuousOn_univ.mp hg
  let r : 𝕀 → ℂ := fun t => if t = 0 ∨ t = 1 then 0 else exp (g (ν t) / 2)
  have hr2 : ∀ t, r t ^ 2 = d t := by
    intro t
    by_cases h : t = 0 ∨ t = 1
    · rcases h with rfl | rfl
      · simp [r, h0]
      · simp [r, h1]
    · push Not at h
      simp only [r, ite_eq_right (not_or.mpr h)]
      rw [← exp_nat_mul, Nat.cast_ofNat, mul_div_cancel₀ _ (two_ne_zero)]
      have h5 : d (τ (ν t)) = exp (g (ν t)) := hfg (ν t) (mem_univ _)
      rw [← h5, (hτν t h.1 h.2).1]
  refine ⟨r, ?_, hr2⟩
  rw [continuous_iff_continuousAt]
  intro t
  by_cases h : t = 0 ∨ t = 1
  · have hz : r t = 0 := by simp [r, h]
    have hdz : d t = 0 := by
      rcases h with rfl | rfl
      · exact h0
      · exact h1
    rw [ContinuousAt, hz]
    have h3 : Tendsto (fun s => Real.sqrt ‖d s‖) (𝓝 t) (𝓝 0) := by
      have := (hd.norm.sqrt).tendsto t
      simpa [hdz] using this
    refine squeeze_zero_norm (fun s => ?_) h3
    apply le_of_eq
    rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt
      (norm_nonneg _), ← norm_pow, hr2]
  · push Not at h
    have hopen : IsOpen {s : 𝕀 | s ≠ 0 ∧ s ≠ 1} := isOpen_ne.inter isOpen_ne
    have hev : r =ᶠ[𝓝 t] fun s => exp (g (ν s) / 2) := by
      filter_upwards [hopen.mem_nhds h] with s hs
      simp only [r, ite_eq_right (not_or.mpr hs)]
    refine ContinuousAt.congr ?_ hev.symm
    have := (hτν t h.1 h.2).2
    exact (Complex.continuous_exp.continuousAt).comp (((hgc.continuousAt (x
      := ν t)).comp this).div_const _)

/-- Each `O`-arc of the plane goes to the unit circle under some homeomorphism of the plane. -/
theorem exists_plane_circle {F : Set ℂ} (hF : Nonempty (Circle ≃ₜ F)) :
    ∃ g : ℂ ≃ₜ ℂ, g '' F = sphere 0 1 := by
  obtain ⟨φ⟩ := id hF
  obtain ⟨φ₀⟩ := oArc_sphere
  let t : sphere (0 : ℂ) 1 ≃ₜ F := φ₀.symm.trans φ
  obtain ⟨h₀, k₀, m, hv⟩ := exists_bdMatch t
  obtain ⟨G, hG⟩ := exists_homeomorph_of_bdMatch hF m
  refine ⟨G.symm, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : G (t.symm ⟨x, hx⟩).1 = x := by
      rw [hG (t.symm ⟨x, hx⟩).2, hv]
      simp
    have h2 : G.symm x = (t.symm ⟨x, hx⟩).1 := by
      apply G.injective
      rw [G.apply_symm_apply, h1]
    rw [h2]
    exact (t.symm ⟨x, hx⟩).2
  · intro hz
    refine ⟨G z, ?_, G.symm_apply_apply z⟩
    rw [hG hz, hv ⟨z, hz⟩]
    exact (t ⟨z, hz⟩).2

/-- A path between two points of the unit circle, off the circle between its ends, and off a given
point that is not on the circle. -/
theorem exists_side_path {p q z₀ : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z₀‖ ≠ 1) :
    ∃ ξ : 𝕀 → ℂ, Continuous ξ ∧ ξ 0 = p ∧ ξ 1 = q ∧ (∀ t, t ≠ 0 → t ≠ 1 → ‖ξ t‖ ≠ 1)
      ∧ ∀ t, ξ t ≠ z₀ := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  rcases lt_or_gt_of_ne hz with hz | hz
  · obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, q = p * exp (θ * I) := by
      refine ⟨arg (q / p), ?_⟩
      have h1 : ‖q / p‖ = 1 := by rw [norm_div, hp, hq]; norm_num
      have h2 := Complex.norm_mul_exp_arg_mul_I (q / p)
      rw [h1] at h2
      simp only [ofReal_one, one_mul] at h2
      rw [h2]
      field_simp
    refine ⟨fun t => ((1 + t.1 * (1 - t.1) : ℝ) : ℂ) * (p * exp ((t.1 * θ : ℝ) * I)), by
      have : Continuous fun t : 𝕀 => t.1 := continuous_subtype_val
      fun_prop, by simp, by simp [hθ], ?_, ?_⟩
    · intro t h0 h1
      have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
      have hpos : 0 < t.1 * (1 - t.1) := mul_pos ht0 (by linarith)
      rw [norm_mul, norm_mul, hp, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg
        (by positivity)]
      simp only [mul_one]
      linarith
    · intro t he
      have hpos : 0 ≤ t.1 * (1 - t.1) := mul_nonneg t.2.1 (by linarith [t.2.2])
      have : ‖z₀‖ = 1 + t.1 * (1 - t.1) := by
        rw [← he, norm_mul, norm_mul, hp, norm_exp_ofReal_mul_I, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        simp
      linarith
  · have key : ∀ t : 𝕀, ‖(1 - t.1 : ℂ) * p + t.1 * q‖ ≤ 1 := fun t => by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(1 - (t.1 : ℂ))‖ = 1 - t.1 := by
        rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg
          (by linarith [t.2.2])]
      rw [norm_mul, norm_mul, h1, hp, hq, Complex.norm_real, Real.norm_of_nonneg t.2.1]
      linarith
    refine ⟨fun t => (1 - t.1 : ℂ) * p + t.1 * q, by
      have : Continuous fun t : 𝕀 => (t.1 : ℂ) := continuous_ofReal.comp continuous_subtype_val
      fun_prop, by simp, by simp, ?_, ?_⟩
    · intro t h0 h1 he
      have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
      have hs : ‖(1 - t.1) • p + t.1 • q‖ < 1 := by
        have h4 := (strictConvex_closedBall ℝ (0 : ℂ) 1) (x := p) (y := q) (by simpa using hp.le)
          (by simpa using hq.le) hpq (a := 1 - t.1) (b := t.1) (by linarith) ht0 (by ring)
        rw [interior_closedBall _ one_ne_zero] at h4
        simpa using h4
      have h3 : (1 - t.1) • p + t.1 • q = (1 - (t.1 : ℂ)) * p + t.1 * q := by
        simp [Complex.real_smul]
      rw [h3] at hs
      exact hs.ne he
    · intro t he
      have := key t
      rw [show (1 - (t.1 : ℂ)) * p + t.1 * q = z₀ from he] at this
      linarith

theorem jou_eq {w n r : ℂ} (h1 : w = n + r) (h2 : (n + r) * (n - r) = 1) : jou w = n := by
  subst h1
  have h3 : (n + r)⁻¹ = n - r := (eq_inv_of_mul_eq_one_right h2).symm
  rw [jou, h3]
  ring

/-- **Every arc of the plane lies on an `O`-arc.** -/
theorem exists_closing_arc {a : 𝕀 → ℂ} (ha : IsArcMap a) :
    ∃ b : 𝕀 → ℂ, IsArcMap b ∧ b 0 = a 0 ∧ b 1 = a 1 ∧
      ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  have hne : a 0 ≠ a 1 := fun h => zero_ne_one (ha.2 h)
  set c : ℂ := (a 0 + a 1) / 2 with hc
  set e : ℂ := (a 1 - a 0) / 2 with he
  have he0 : e ≠ 0 := by
    rw [he]
    exact div_ne_zero (sub_ne_zero.mpr hne.symm) two_ne_zero
  let n : 𝕀 → ℂ := fun t => (a t - c) / e
  have hnc : Continuous n := (ha.1.sub continuous_const).div_const _
  have hninj : Function.Injective n := fun s t h => by
    have h1 : a s - c = a t - c := by
      have := div_left_inj₀ he0 |>.mp h
      exact this
    exact ha.2 (sub_left_inj.mp h1)
  have hn0 : n 0 = -1 := by
    simp only [n, hc, he]
    field_simp [sub_ne_zero.mpr hne.symm]
    ring
  have hn1 : n 1 = 1 := by
    simp only [n, hc, he]
    field_simp [sub_ne_zero.mpr hne.symm]
    ring
  have h01 : ∀ t, t ≠ 0 → t ≠ 1 → n t ^ 2 - 1 ≠ 0 := by
    intro t h0 h1 h
    have h2 : (n t - 1) * (n t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h1 (hninj (by rw [hn1]; linear_combination h3))
    · exact h0 (hninj (by rw [hn0]; linear_combination h3))
  obtain ⟨r, hrc, hr⟩ := exists_sqrt_of_ends (d := fun t => n t ^ 2 - 1) (by fun_prop)
    (by simp [hn0]) (by simp [hn1]) h01
  have hprod : ∀ t, (n t + r t) * (n t - r t) = 1 := fun t => by
    linear_combination -(hr t)
  have hr0 : r 0 = 0 := by
    have := hr 0
    simp only [hn0] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (by rw [this]; norm_num)
  have hr1 : r 1 = 0 := by
    have := hr 1
    simp only [hn1] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (by rw [this]; norm_num)
  let w₁ : 𝕀 → ℂ := fun t => n t + r t
  let w₂ : 𝕀 → ℂ := fun t => n t - r t
  have hj₁ : ∀ t, jou (w₁ t) = n t := fun t => jou_eq rfl (hprod t)
  have hj₂ : ∀ t, jou (w₂ t) = n t := fun t => by
    have := jou_eq (n := n t) (r := -r t) (w := w₂ t) (by simp [w₂, sub_eq_add_neg]) (by
      linear_combination hprod t)
    exact this
  have hw₁ : IsArcMap w₁ := ⟨hnc.add hrc, fun s t h => hninj (by rw [← hj₁, ← hj₁, h])⟩
  have hw₂ : IsArcMap w₂ := ⟨hnc.sub hrc, fun s t h => hninj (by rw [← hj₂, ← hj₂, h])⟩
  have hmeet : ∀ s t, w₁ s = w₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hst : s = t := hninj (by rw [← hj₁, ← hj₂, h])
    subst hst
    have h3 : r s = 0 := by
      have : (2 : ℂ) * r s = 0 := by
        have h4 : n s + r s = n s - r s := h
        linear_combination h4
      simpa using this
    by_cases h0 : s = 0
    · exact .inl ⟨h0, h0⟩
    · by_cases h1 : s = 1
      · exact .inr ⟨h1, h1⟩
      · exact absurd (by rw [← hr s, h3]; simp) (h01 s h0 h1)
  have hO := oArc_of_two_arcs hw₁ hw₂ (by simp [w₁, w₂, hr0]) (by simp [w₁, w₂, hr1]) hmeet
  obtain ⟨g, hg⟩ := exists_plane_circle hO
  have hmemC : ∀ w : ℂ, w ≠ 0 → ∀ t, jou w = n t → w ∈ range w₁ ∪ range w₂ := by
    intro w hw t h
    have h1 : (w - w₁ t) * (w - w₂ t) = 0 := by
      have h2 : w + w⁻¹ = 2 * n t := by
        rw [jou] at h
        linear_combination 2 * h
      have h3 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have h4 := hprod t
      simp only [w₁, w₂]
      linear_combination w * h2 - h3 + h4
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact .inl ⟨t, (sub_eq_zero.mp h2).symm⟩
    · exact .inr ⟨t, (sub_eq_zero.mp h2).symm⟩
  have hsph : ∀ w, w ∈ range w₁ ∪ range w₂ → ‖g w‖ = 1 := fun w hw => by
    have : g w ∈ sphere (0 : ℂ) 1 := hg ▸ mem_image_of_mem g hw
    simpa using this
  have hsph' : ∀ w, ‖g w‖ = 1 → w ∈ range w₁ ∪ range w₂ := fun w hw => by
    have : g w ∈ g '' (range w₁ ∪ range w₂) := by
      rw [hg]
      simpa using hw
    obtain ⟨y, hy, he'⟩ := this
    rwa [← g.injective he']
  have h1C : w₁ 0 = -1 ∧ w₁ 1 = 1 := by simp [w₁, hn0, hn1, hr0, hr1]
  have hzero : (0 : ℂ) ∉ range w₁ ∪ range w₂ := by
    rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · have := hprod t
      simp only [w₁] at ht
      rw [ht] at this
      simp at this
    · have := hprod t
      simp only [w₂] at ht
      rw [ht] at this
      simp at this
  have hp : ‖g 1‖ = 1 := hsph _ (.inl ⟨1, h1C.2⟩)
  have hq : ‖g (-1)‖ = 1 := hsph _ (.inl ⟨0, h1C.1⟩)
  have hpq : g 1 ≠ g (-1) := fun h => by
    have := g.injective h
    norm_num at this
  have hz : ‖g 0‖ ≠ 1 := fun h => hzero (hsph' _ h)
  obtain ⟨ξ, hξc, hξ0, hξ1, hξn, hξz⟩ := exists_side_path hp hq hpq hz
  let y : 𝕀 → ℂ := fun t => g.symm (ξ t)
  have hyc : Continuous y := g.symm.continuous.comp hξc
  have hy0 : ∀ t, y t ≠ 0 := fun t h => hξz t (by
    rw [← g.apply_symm_apply (ξ t)]
    exact congrArg g h)
  let β : 𝕀 → ℂ := fun t => c + e * jou (y t)
  have hβc : Continuous β := by
    have h1 : Continuous fun t => (y t)⁻¹ := hyc.inv₀ hy0
    simp only [β, jou]
    fun_prop
  have hy00 : y 0 = 1 := by simp [y, hξ0]
  have hy1 : y 1 = -1 := by simp [y, hξ1]
  have hβ0 : β 0 = a 1 := by
    simp only [β, hy00, jou, hc, he]
    norm_num
    field_simp
    ring
  have hβ1 : β 1 = a 0 := by
    simp only [β, hy1, jou, hc, he]
    norm_num
    field_simp
    ring
  have hβa : ∀ t s, β t = a s → t = 0 ∨ t = 1 := by
    intro t s h
    by_contra hc'
    push Not at hc'
    have h1 : jou (y t) = n s := by
      simp only [n, ← h, β]
      field_simp
      ring
    have h2 := hsph _ (hmemC _ (hy0 t) s h1)
    simp only [y, g.apply_symm_apply] at h2
    exact hξn t hc'.1 hc'.2 h2
  obtain ⟨e', he'c, he'i, he'0, he'1, he'r⟩ := exists_arc_of_path hβc
    (by rw [hβ0, hβ1]; exact hne.symm)
  let σ : 𝕀 → 𝕀 := unitInterval.symm
  refine ⟨e' ∘ σ, ⟨he'c.comp unitInterval.continuous_symm, he'i.comp
    unitInterval.symm_bijective.injective⟩, ?_, ?_, ?_⟩
  · simp [σ, he'1, hβ1]
  · simp [σ, he'0, hβ0]
  · intro s t h
    obtain ⟨u, hu⟩ := he'r (mem_range_self (σ t))
    have h3 : β u = a s := by rw [hu]; exact h.symm
    rcases hβa u s h3 with rfl | rfl
    · have h4 : a s = a 1 := by rw [← h3, hβ0]
      have hs : s = 1 := ha.2 h4
      have h5 : e' (σ t) = e' 0 := by rw [← hu, he'0]
      have h6 := he'i h5
      right
      refine ⟨hs, ?_⟩
      have : σ (σ t) = σ 0 := congrArg σ h6
      simpa [σ] using this
    · have h4 : a s = a 0 := by rw [← h3, hβ1]
      have hs : s = 0 := ha.2 h4
      have h5 : e' (σ t) = e' 1 := by rw [← hu, he'1]
      have h6 := he'i h5
      left
      refine ⟨hs, ?_⟩
      have : σ (σ t) = σ 1 := congrArg σ h6
      simpa [σ] using this

/-- **Straightening an arc of the plane.** A homeomorphism of the plane maps the arc to an arc of
the unit circle, with an increasing angle. -/
theorem exists_straight {a : 𝕀 → ℂ} (ha : IsArcMap a) :
    ∃ (g : ℂ ≃ₜ ℂ) (θ : 𝕀 → ℝ), Continuous θ ∧ StrictMono θ ∧ (∀ t, θ t ∈ Ioo (-Real.pi) Real.pi) ∧
      ∀ t, g (a t) = exp (θ t * I) := by
  obtain ⟨b, hb, h0, h1, hm⟩ := exists_closing_arc ha
  have hO := oArc_of_two_arcs ha hb h0.symm h1.symm hm
  obtain ⟨g₀, hg₀⟩ := exists_plane_circle hO
  have hnorm : ∀ x ∈ range a ∪ range b, ‖g₀ x‖ = 1 := fun x hx => by
    have : g₀ x ∈ sphere (0 : ℂ) 1 := hg₀ ▸ mem_image_of_mem g₀ hx
    simpa using this
  set m : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩ with hmd
  have hm0 : m ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    norm_num [hmd] at this
  have hm1 : m ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    norm_num [hmd] at this
  set z := g₀ (b m) with hz
  have hzn : ‖z‖ = 1 := hnorm _ (.inr ⟨m, rfl⟩)
  have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
  have hzu : (-z⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz0)
  let ρ : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (-z⁻¹) hzu
  let g₁ : ℂ ≃ₜ ℂ := g₀.trans ρ
  have hg₁ : ∀ t, ‖g₁ (a t)‖ = 1 := fun t => by
    change ‖-z⁻¹ * g₀ (a t)‖ = 1
    rw [norm_mul, norm_neg, norm_inv, hzn, hnorm _ (.inl ⟨t, rfl⟩)]
    simp
  have hne : ∀ t, g₁ (a t) ≠ -1 := fun t h => by
    have h2 : g₀ (a t) = z := by
      have h3 : -z⁻¹ * g₀ (a t) = -1 := h
      have h4 : z⁻¹ * g₀ (a t) = 1 := by linear_combination -h3
      rw [inv_mul_eq_iff_eq_mul₀ hz0, mul_one] at h4
      exact h4
    have h3 : a t = b m := g₀.injective h2
    rcases hm t m h3 with h4 | h4
    · exact hm0 h4.2
    · exact hm1 h4.2
  have hslit : ∀ t, g₁ (a t) ∈ slitPlane := fun t => by
    rw [mem_slitPlane_iff]
    by_contra h
    push Not at h
    have h3 : (g₁ (a t)).re ^ 2 = 1 := by
      have h4 := hg₁ t
      have h5 : normSq (g₁ (a t)) = 1 := by rw [normSq_eq_norm_sq, h4]; norm_num
      rw [normSq_apply, h.2] at h5
      nlinarith
    apply hne t
    apply Complex.ext
    · have : (g₁ (a t)).re = -1 := by nlinarith [h.1]
      simpa using this
    · simpa using h.2
  let θ₀ : 𝕀 → ℝ := fun t => arg (g₁ (a t))
  have hc : Continuous θ₀ := continuous_iff_continuousAt.mpr fun t =>
    ContinuousAt.comp (g := arg) (f := fun t => g₁ (a t)) (continuousAt_arg (hslit t))
      (g₁.continuous.comp ha.1).continuousAt
  have hexp : ∀ t, g₁ (a t) = exp (θ₀ t * I) := fun t => by
    have := Complex.norm_mul_exp_arg_mul_I (g₁ (a t))
    rw [hg₁] at this
    simpa using this.symm
  have hinj : Function.Injective θ₀ := fun s t h => ha.2 (g₁.injective (by rw [hexp, hexp, h]))
  have hrange : ∀ t, θ₀ t ∈ Ioo (-Real.pi) Real.pi := fun t =>
    ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (fun h => hne t (by
      have := hexp t
      rw [h] at this
      rw [this]
      simp [exp_pi_mul_I]))⟩
  rcases hc.strictMono_of_inj hinj with hmono | hanti
  · exact ⟨g₁, θ₀, hc, hmono, hrange, hexp⟩
  · let κ : ℂ ≃ₜ ℂ := conjCLE.toHomeomorph
    refine ⟨g₁.trans κ, fun t => -θ₀ t, hc.neg, fun s t h => neg_lt_neg (hanti h), fun t
      => ⟨by linarith [(hrange t).2], by linarith [(hrange t).1]⟩, fun t => ?_⟩
    change (starRingEnd ℂ) (g₁ (a t)) = _
    rw [hexp, ← exp_conj]
    simp

end GraphMinor.Surface
