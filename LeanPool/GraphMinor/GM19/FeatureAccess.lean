/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureCode
public import Mathlib.Analysis.Complex.CoveringMap

/-!
# The free end of an arc in a disc can be reached

An arc in the closed unit disc goes from the centre to the boundary, and is otherwise in the open
disc. We find a second arc from the
centre to the boundary that meets the first only at the centre. The map `z ↦ z²` unfolds the first
arc: its preimage is a chord of the
disc through the centre, invariant under `z ↦ -z`. A chord of one of the two half discs, from the
centre to the boundary, goes down to
the second arc, because `z ↦ z²` is one to one on an open half disc (`exists_access`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- An arc from the centre has a continuous square root. -/
theorem exists_sqrt_path {b : 𝕀 → ℂ} (hc : Continuous b) (h0 : b 0 = 0) (hne : ∀ t, t ≠ 0
  → b t ≠ 0) :
    ∃ r : 𝕀 → ℂ, Continuous r ∧ r 0 = 0 ∧ ∀ t, r t ^ 2 = b t := by
  classical
  let u : ℝ → 𝕀 := fun t ↦ ⟨Real.exp (-|t|), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by simp)⟩
  have hu : Continuous u := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hu0 : ∀ t, u t ≠ 0 := fun t he ↦ (Real.exp_pos (-|t|)).ne' (congrArg Subtype.val he)
  let p : C(ℝ, {z : ℂ // z ≠ 0}) := ⟨fun t ↦ ⟨b (u t), hne _ (hu0 t)⟩, (hc.comp hu).subtype_mk _⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, Complex.exp w = b (u 0) := ⟨Complex.log (b (u 0)), Complex.exp_log
    (hne _ (hu0 0))⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts p 0 w
    (Subtype.ext hw)
  have hF' : ∀ t, Complex.exp (F t) = b (u t) := fun t ↦ congrArg Subtype.val (congrFun hF t)
  have hlog : ∀ s : 𝕀, s ≠ 0 → u (-Real.log s) = s := fun s hs ↦ by
    have hs0 : (0 : ℝ) < s := lt_of_le_of_ne s.2.1 (fun h ↦ hs (Subtype.ext h.symm))
    apply Subtype.ext
    have h₁ : Real.log s ≤ 0 := Real.log_nonpos s.2.1 s.2.2
    simp only [u, abs_neg, abs_of_nonpos h₁, neg_neg, Real.exp_log hs0]
  let r : 𝕀 → ℂ := fun s ↦ if s = 0 then 0 else Complex.exp (F (-Real.log s) / 2)
  have hr2 : ∀ s, r s ^ 2 = b s := fun s ↦ by
    by_cases hs : s = 0
    · simp [r, hs, h0]
    · simp only [r, hs, ite_false]
      have h := hF' (-Real.log s)
      rw [hlog s hs] at h
      rw [← Complex.exp_nat_mul, ← h]
      congr 1
      push_cast
      ring
  have hnorm : ∀ s, ‖r s‖ = √‖b s‖ := fun s ↦ by
    rw [← hr2, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨r, ?_, by simp [r], hr2⟩
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have h₁ : Filter.Tendsto (fun x ↦ ‖r x‖) (𝓝 0) (𝓝 0) := by
      have h₂ : Continuous fun x ↦ √‖b x‖ := by fun_prop
      have h₃ := h₂.tendsto 0
      simp only [h0, norm_zero, Real.sqrt_zero] at h₃
      exact h₃.congr fun x ↦ (hnorm x).symm
    have h₄ : r 0 = 0 := by simp [r]
    rw [ContinuousAt, h₄]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h₁
  · have hs0 : (s : ℝ) ≠ 0 := fun h ↦ hs (Subtype.ext h)
    have hc₁ : ContinuousAt (fun x : 𝕀 ↦ Complex.exp (F (-Real.log x) / 2)) s := by
      have h₁ : ContinuousAt (fun x : 𝕀 ↦ Real.log x) s := (Real.continuousAt_log hs0).comp
        continuous_subtype_val.continuousAt
      have h₂ : ContinuousAt (fun x : 𝕀 ↦ F (-Real.log x)) s := F.continuous.continuousAt.comp
        h₁.neg
      exact Complex.continuous_exp.continuousAt.comp (h₂.div_const 2)
    refine hc₁.congr ?_
    have h₁ : ∀ᶠ x in 𝓝 s, x ≠ 0 := isOpen_ne.mem_nhds hs
    filter_upwards [h₁] with x hx
    simp [r, hx]

/-- A point of the unit circle other than `p` and `-p` has nonzero height over the line through `p`.
-/
theorem im_div_ne {p z : ℂ} (hp : ‖p‖ = 1) (hz : ‖z‖ = 1) (h1 : z ≠ p) (h2 : z ≠ -p) :
  (z / p).im ≠ 0 := by
  intro h
  have hp0 : p ≠ 0 := fun h' ↦ by simp [h'] at hp
  have hn : ‖z / p‖ = 1 := by rw [norm_div, hz, hp, div_one]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, z / p = x := ⟨(z / p).re, Complex.ext (by simp) (by simpa using h)⟩
  rw [hx, Complex.norm_real, Real.norm_eq_abs] at hn
  rcases abs_eq (zero_le_one) |>.mp hn with rfl | rfl
  · apply h1
    field_simp at hx
    simpa using hx
  · apply h2
    field_simp at hx
    simpa using hx

private theorem component_ne_neg
    (r : 𝕀 → ℂ)
    (L : Set ℂ)
    (A₁ : Set ℂ)
    (A₂ : Set ℂ)
    (Δ₁ : Set ℂ)
    (Δ₂ : Set ℂ)
    (hc : componentsIn (sphere 0 1 \ {r 1, -r 1}) = {A₁, A₂})
    (hi : Δ₁ ∩ Δ₂ = L)
    (y : ℂ)
    (hyA₁ : y ∈ A₁)
    (hA₁sub : A₁ ⊆ sphere 0 1 \ {r 1, -r 1})
    (hA₁Δ : A₁ ⊆ Δ₁ \ L)
    (hA₂Δ : A₂ ⊆ Δ₂)
    (hnotneg : ∀ z ∈ A₁, -z ∉ A₁)
    (p₀ : ℂ)
    (hp₀e : connectedComponentIn (closedBall 0 1 \ L) p₀ = Δ₁ \ L)
    (hnegL : ∀ z ∈ L, -z ∈ L)
    (hΔsub : Δ₁ ⊆ closedBall 0 1) :
    ∀ z ∈ Δ₁ \ L, -z ∉ Δ₁ \ L := by
  intro z hz hz'
  have hpre : IsPreconnected ((fun w : ℂ ↦ -w) '' (Δ₁ \ L)) := by
    have h' : IsPreconnected (Δ₁ \ L) := hp₀e ▸ isPreconnected_connectedComponentIn
    exact h'.image _ continuous_neg.continuousOn
  have hsub : (fun w : ℂ ↦ -w) '' (Δ₁ \ L) ⊆ closedBall 0 1 \ L := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨by simpa using hΔsub hw.1, fun hL' ↦ hw.2 (by simpa using hnegL _ hL')⟩
  have hin' : (fun w : ℂ ↦ -w) '' (Δ₁ \ L) ⊆ Δ₁ \ L := by
    have h' := hpre.subset_connectedComponentIn (x := -z) ⟨z, hz, rfl⟩ hsub
    have hne' : connectedComponentIn (closedBall (0 : ℂ) 1 \ L) (-z) = Δ₁ \ L := by
      rw [← hp₀e]
      exact (connectedComponentIn_eq (by rw [hp₀e]; exact hz')).symm
    rwa [hne'] at h'
  have hm := hin' (mem_image_of_mem _ (hA₁Δ hyA₁))
  have hys := hA₁sub hyA₁
  have hmS : -y ∈ sphere (0 : ℂ) 1 \ {r 1, -r 1} := by
    refine ⟨by simpa using hys.1, ?_⟩
    rintro (h' | h')
    · exact hys.2 (.inr (by rw [← h', neg_neg]; rfl))
    · exact hys.2 (.inl (neg_injective h'))
  have hcov : connectedComponentIn (sphere (0 : ℂ) 1 \ {r 1, -r 1}) (-y) ∈ ({A₁, A₂} : Set
    (Set ℂ)) :=
    hc ▸ ⟨-y, hmS, rfl⟩
  have hmem := mem_connectedComponentIn hmS
  rcases hcov with h' | h'
  · exact hnotneg y hyA₁ (h' ▸ hmem)
  · have : -y ∈ Δ₁ ∩ Δ₂ := ⟨hm.1, hA₂Δ (h' ▸ hmem)⟩
    rw [hi] at this
    exact hm.2 this

private theorem opposite_arc_inter
    {a : 𝕀 → ℂ}
    (ha : IsArcMap a)
    (r : 𝕀 → ℂ)
    (hr0 : r 0 = 0)
    (hr2 : ∀ (t : 𝕀), r t ^ 2 = a t) :
    (range r ∩ range fun t => -r t) = {0} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, u, hu⟩
    have hu' : r u ^ 2 = r t ^ 2 := by
      have : -r u = r t := hu
      rw [← this]
      ring
    rw [hr2, hr2] at hu'
    have htu := ha.2 hu'
    rw [htu] at hu
    have hz : r t = 0 := by
      have : -r t = r t := hu
      have h2 : (2 : ℂ) * r t = 0 := by linear_combination -this
      simpa using h2
    exact hz
  · rintro rfl
    exact ⟨⟨0, hr0⟩, 0, by simp [hr0]⟩

private theorem quadratic_chord_injective
    {a : 𝕀 → ℂ}
    (hne0 : ∀ (t : 𝕀), t ≠ 0 → a t ≠ 0)
    (L : Set ℂ)
    (Δ₁ : Set ℂ)
    (hinjΔ : ∀ z ∈ Δ₁ \ L, ∀ w ∈ Δ₁ \ L, z ^ 2 = w ^ 2 → z = w)
    (h₁ : ℂ → ℂ)
    (g₁ : ℂ → ℂ)
    (c : IsChart Δ₁ h₁ g₁)
    (s : 𝕀)
    (hs0 : s ≠ 0)
    (seg : 𝕀 → ℂ)
    (hsegm : ∀ (u : 𝕀), seg u ∈ closedBall 0 1)
    (hseginj : Injective seg)
    (hz : ∀ (u : 𝕀), u ≠ 0 → u ≠ 1 → g₁ (seg u) ∈ Δ₁ \ L)
    (hoff : ∀ (t : 𝕀), t ≠ 0 → t ≠ 1 → (fun u => g₁ (seg u) ^ 2) t ∉ range a)
    (hq0 : (fun u => g₁ (seg u) ^ 2) 0 = 0)
    (hq1 : (fun u => g₁ (seg u) ^ 2) 1 = a s)
    (hends : ∀ (t : 𝕀), t = 0 ∨ t = 1 ∨ t ≠ 0 ∧ t ≠ 1)
    (hendr : ∀ (t : 𝕀), t = 0 ∨ t = 1 → (fun u => g₁ (seg u) ^ 2) t ∈ range a) :
    Injective (fun u => g₁ (seg u) ^ 2) := by
  let q := fun u => g₁ (seg u) ^ 2
  intro u v huv
  rcases hends u with hu | hu | hu <;> rcases hends v with hv | hv | hv
  · rw [hu, hv]
  · exfalso
    rw [hu, hv, hq0, hq1] at huv
    exact hne0 s hs0 huv.symm
  · exact absurd (huv ▸ hendr u (.inl hu)) (hoff v hv.1 hv.2)
  · exfalso
    rw [hu, hv, hq0, hq1] at huv
    exact hne0 s hs0 huv
  · rw [hu, hv]
  · exact absurd (huv ▸ hendr u (.inr hu)) (hoff v hv.1 hv.2)
  · exact absurd (huv.symm ▸ hendr v (.inl hv)) (hoff u hu.1 hu.2)
  · exact absurd (huv.symm ▸ hendr v (.inr hv)) (hoff u hu.1 hu.2)
  · have := hinjΔ _ (hz u hu.1 hu.2) _ (hz v hv.1 hv.2) huv
    have h2 : seg u = seg v := by
      rw [← c.hg (hsegm u), ← c.hg (hsegm v), this]
    exact hseginj h2

private theorem chord_square_image_avoids_cut_arc
    {a : 𝕀 → ℂ}
    (r : 𝕀 → ℂ)
    (hr2 : ∀ (t : 𝕀), r t ^ 2 = a t)
    (Δ₁ : Set ℂ)
    (g₁ : ℂ → ℂ)
    (seg : 𝕀 → ℂ)
    (hz : ∀ (u : 𝕀), u ≠ 0 → u ≠ 1 → g₁ (seg u) ∈ Δ₁ \ (range r ∪ range (fun t => -r t))) :
    ∀ (t : 𝕀), t ≠ 0 → t ≠ 1 → g₁ (seg t) ^ 2 ∉ range a := by
  rintro t ht0 ht1 ⟨u, hu⟩
  have h2 : r u ^ 2 = g₁ (seg t) ^ 2 := by rw [hr2]; exact hu
  obtain ⟨hzΔ, hzL⟩ := hz t ht0 ht1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · exact hzL (h3 ▸ .inl ⟨u, rfl⟩)
  · exact hzL (.inr ⟨u, by simp only; rw [h3, neg_neg]⟩)

private theorem preconnected_circle_side_excludes_antipodes
    (r : 𝕀 → ℂ)
    (hr1 : ‖r 1‖ = 1)
    (A₁ : Set ℂ)
    (hA₁sub : A₁ ⊆ sphere 0 1 \ {r 1, -r 1})
    (hA₁pre : IsPreconnected A₁) :
    ∀ z ∈ A₁, -z ∉ A₁ := by
  intro z hz hz'
  obtain ⟨hzs, hzn⟩ := hA₁sub hz
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hzs
  have hf : ContinuousOn (fun w : ℂ ↦ (w / r 1).im) A₁ := by fun_prop
  have hv : ∀ w ∈ A₁, (w / r 1).im ≠ 0 := fun w hw ↦ by
    obtain ⟨hws, hwn⟩ := hA₁sub hw
    exact im_div_ne hr1 (mem_sphere_zero_iff_norm.mp hws) (fun h' ↦ hwn (.inl h')) (fun h' ↦ hwn
      (.inr h'))
  have h3 : ((-z) / r 1).im = -(z / r 1).im := by
    rw [neg_div, Complex.neg_im]
  have h0' := hv z hz
  rcases lt_or_gt_of_ne h0' with h4 | h4
  · obtain ⟨w, hw, hw0⟩ := hA₁pre.intermediate_value hz hz' hf
      (show (0 : ℝ) ∈ Icc _ _ from ⟨h4.le, by rw [h3]; linarith⟩)
    exact hv w hw hw0
  · obtain ⟨w, hw, hw0⟩ := hA₁pre.intermediate_value hz' hz hf
      (show (0 : ℝ) ∈ Icc _ _ from ⟨by rw [h3]; linarith, h4.le⟩)
    exact hv w hw hw0

/-- **The second side of an arc from the centre.** The arc `a` goes from the centre of the unit disc
to the circle. Near the centre
there is a second arc from the centre to a point of `a`, otherwise off `a`. -/
theorem exists_chord {a : 𝕀 → ℂ} (ha : IsArcMap a) (h0 : a 0 = 0) (h1 : ‖a 1‖ = 1)
  (hlt : ∀ t, t ≠ 1 → ‖a t‖ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : 𝕀, s ≠ 0 ∧ s ≠ 1 ∧ ∃ q : 𝕀 → ℂ, IsArcMap q ∧ q 0 = 0 ∧ q 1 = a s ∧ range q ⊆ ball 0 ε ∧
      ∀ t, t ≠ 0 → t ≠ 1 → q t ∉ range a := by
  classical
  have hne0 : ∀ t, t ≠ 0 → a t ≠ 0 := fun t ht he ↦ ht (ha.2 (he.trans h0.symm))
  obtain ⟨r, hrc, hr0, hr2⟩ := exists_sqrt_path ha.1 h0 hne0
  have hsq : ∀ t, ‖r t‖ ^ 2 = ‖a t‖ := fun t ↦ by rw [← hr2, norm_pow]
  have hrinj : Injective r := fun t u h ↦ ha.2 (by rw [← hr2, ← hr2, h])
  have hr : IsArcMap r := ⟨hrc, hrinj⟩
  have hn : IsArcMap fun t ↦ -r t := ⟨hrc.neg, fun t u h ↦ hrinj (neg_injective h)⟩
  have hr1 : ‖r 1‖ = 1 := by
    have h' := hsq 1
    rw [h1] at h'
    nlinarith [norm_nonneg (r 1)]
  have hrne : ∀ t, t ≠ 1 → ‖r t‖ < 1 := fun t ht ↦ by
    have h' := hsq t
    have h'' := hlt t ht
    nlinarith [norm_nonneg (r t)]
  have hile : ∀ t, ‖r t‖ ≤ 1 := fun t ↦ by
    by_cases ht : t = 1
    · rw [ht, hr1]
    · exact (hrne t ht).le
  have hin : range r ∩ range (fun t ↦ -r t) = {0} := by
    exact opposite_arc_inter (a := a) ha r hr0 hr2
  let L : Set ℂ := range r ∪ range fun t ↦ -r t
  have hl1 := hr.isLineWithEnds
  have hl2 := hn.isLineWithEnds
  simp only [hr0, neg_zero] at hl1 hl2
  have hL : IsLineWithEnds L (r 1) (-r 1) := hl1.symm.union hl2 hin
  have hLball : L ⊆ closedBall 0 1 := by
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact mem_closedBall_zero_iff.mpr (hile t)
    · exact mem_closedBall_zero_iff.mpr (by simpa using hile t)
  have hne : r 1 ≠ -r 1 := fun h' ↦ by
    have : r 1 = 0 := by
      have h2 : (2 : ℂ) * r 1 = 0 := by linear_combination h'
      simpa using h2
    rw [this] at hr1
    simp at hr1
  obtain ⟨hD, hbdD⟩ := isClosedDisc_closedBall
  have hmeet : L ∩ discBd (closedBall (0 : ℂ) 1) = {r 1, -r 1} := by
    rw [hbdD]
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩ | ⟨t, rfl⟩, hz⟩
      · have ht : t = 1 := by
          by_contra ht
          exact (hrne t ht).ne (mem_sphere_zero_iff_norm.mp hz)
        exact .inl (by rw [ht])
      · have ht : t = 1 := by
          by_contra ht
          exact (hrne t ht).ne (by simpa using mem_sphere_zero_iff_norm.mp hz)
        exact .inr (by simp [ht])
    · rintro (rfl | rfl)
      · exact ⟨hL.left_mem, mem_sphere_zero_iff_norm.mpr hr1⟩
      · exact ⟨hL.right_mem, mem_sphere_zero_iff_norm.mpr (by simpa using hr1)⟩
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hc, d1, -, hu, hi, b1, b2, hc2⟩ := disc_iArc _ L _ _ hD hLball hne hL
    hmeet
  rw [hbdD] at hc
  have hsubL : L ⊆ Δ₁ := fun z hz ↦ by
    have : z ∈ Δ₁ ∩ Δ₂ := hi.symm ▸ hz
    exact this.1
  have hLbd : L ⊆ discBd Δ₁ := b1 ▸ subset_union_right
  have hA₁ : A₁ ∈ componentsIn (sphere (0 : ℂ) 1 \ {r 1, -r 1}) := hc ▸ .inl rfl
  have hA₂ : A₂ ∈ componentsIn (sphere (0 : ℂ) 1 \ {r 1, -r 1}) := hc ▸ .inr rfl
  obtain ⟨y, hy, hyA⟩ : ∃ y ∈ sphere (0 : ℂ) 1 \ {r 1, -r 1}, connectedComponentIn (sphere
    (0 : ℂ) 1 \ {r 1, -r 1}) y = A₁ := hA₁
  have hyA₁ : y ∈ A₁ := hyA ▸ mem_connectedComponentIn hy
  have hA₁sub : A₁ ⊆ sphere (0 : ℂ) 1 \ {r 1, -r 1} := hyA ▸ connectedComponentIn_subset _ _
  have hA₁pre : IsPreconnected A₁ := hyA ▸ isPreconnected_connectedComponentIn
  have hA₁Δ : A₁ ⊆ Δ₁ \ L := fun z hz ↦ by
    have hzs := hA₁sub hz
    have hb : discBd Δ₁ ⊆ Δ₁ := Subtype.coe_image_subset _ _
    refine ⟨hb (by rw [b1]; exact .inl hz), fun hzL ↦ hzs.2 ?_⟩
    rw [← hmeet, hbdD]
    exact ⟨hzL, hzs.1⟩
  have hA₂Δ : A₂ ⊆ Δ₂ := (b2 ▸ subset_union_left : A₂ ⊆ discBd Δ₂).trans
    (Subtype.coe_image_subset _ _)
  have hr1n : ‖r 1‖ = 1 := hr1
  have hnotneg : ∀ z ∈ A₁, -z ∉ A₁ := by
    exact preconnected_circle_side_excludes_antipodes r hr1 A₁ hA₁sub hA₁pre
  have hcomp : Δ₁ \ L ∈ componentsIn (closedBall (0 : ℂ) 1 \ L) := hc2 ▸ .inl rfl
  obtain ⟨p₀, hp₀, hp₀e⟩ : ∃ p ∈ closedBall (0 : ℂ) 1 \ L, connectedComponentIn (closedBall
    (0 : ℂ) 1 \ L) p = Δ₁ \ L := hcomp
  have hnegL : ∀ z, z ∈ L → -z ∈ L := by
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact .inr ⟨t, rfl⟩
    · exact .inl ⟨t, by simp⟩
  have hΔsub : Δ₁ ⊆ closedBall 0 1 := hu ▸ subset_union_left
  have hkey : ∀ z ∈ Δ₁ \ L, -z ∉ Δ₁ \ L := by
    exact component_ne_neg r L A₁ A₂ Δ₁ Δ₂ hc hi y hyA₁ hA₁sub hA₁Δ hA₂Δ hnotneg p₀ hp₀e hnegL
      hΔsub
  have hinjΔ : ∀ z ∈ Δ₁ \ L, ∀ w ∈ Δ₁ \ L, z ^ 2 = w ^ 2 → z = w := by
    intro z hz w hw h'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hz) (hkey w hw)
  obtain ⟨h₁, g₁, c⟩ := d1.exists_isChart
  have h0L : (0 : ℂ) ∈ L := .inl ⟨0, hr0⟩
  have h0Δ : (0 : ℂ) ∈ Δ₁ := hsubL h0L
  have hsph : ∀ z ∈ L, ‖h₁ z‖ = 1 := fun z hz ↦ by
    have : h₁ z ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem _ (hLbd hz)
    exact mem_sphere_zero_iff_norm.mp this
  have hgP : g₁ (h₁ 0) = 0 := c.gh h0Δ
  have hPm : h₁ 0 ∈ closedBall (0 : ℂ) 1 := c.hm h0Δ
  obtain ⟨δ, hδ, hg⟩ := Metric.continuousOn_iff.mp c.gc _ hPm (√ε) (Real.sqrt_pos.mpr hε)
  have hφ : Continuous fun t ↦ h₁ (r t) := c.hc.comp_continuous hrc fun t ↦ hsubL (.inl ⟨t, rfl⟩)
  obtain ⟨ρ, hρ, hφρ⟩ := Metric.continuous_iff.mp hφ 0 δ hδ
  have hsv : 0 < min (ρ / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hsv2 : min (ρ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  let s : 𝕀 := ⟨min (ρ / 2) (1 / 2), hsv.le, by linarith⟩
  have hs0 : s ≠ 0 := fun h' ↦ hsv.ne' (congrArg Subtype.val h')
  have hs1 : s ≠ 1 := fun h' ↦ by
    have : min (ρ / 2) (1 / 2) = 1 := congrArg Subtype.val h'
    linarith
  have hsρ : dist s 0 < ρ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have : ((s : ℝ) - ((0 : 𝕀) : ℝ)) = min (ρ / 2) (1 / 2) := by simp [s]
    rw [this, abs_of_pos hsv]
    linarith [min_le_left (ρ / 2) (1 / 2 : ℝ)]
  have hy₁ := hφρ s hsρ
  rw [hr0] at hy₁
  let y₁ := h₁ (r s)
  have hrsL : r s ∈ L := .inl ⟨s, rfl⟩
  have hrs0 : r s ≠ 0 := fun h' ↦ hs0 (hrinj (h'.trans hr0.symm))
  have hne₁ : h₁ 0 ≠ y₁ := fun h' ↦ hrs0 ((c.gh (hsubL hrsL)).symm.trans
    ((congrArg g₁ h'.symm).trans hgP))
  have hy₁m : y₁ ∈ closedBall (0 : ℂ) 1 := c.hm (hsubL hrsL)
  let seg : 𝕀 → ℂ := fun u ↦ (1 - (u : ℝ)) • h₁ 0 + (u : ℝ) • y₁
  have hsegc : Continuous seg := by
    simp only [seg]
    fun_prop
  have hconv := convex_closedBall (0 : ℂ) 1
  have hsegm : ∀ u, seg u ∈ closedBall (0 : ℂ) 1 := fun u ↦
    hconv hPm hy₁m (by linarith [u.2.2]) u.2.1 (by ring)
  have hsegd : ∀ u, dist (seg u) (h₁ 0) < δ := fun u ↦ by
    have e : seg u - h₁ 0 = (u : ℝ) • (y₁ - h₁ 0) := by
      simp only [seg, smul_sub, sub_smul, one_smul]
      abel
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg u.2.1]
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    have hy' : ‖y₁ - h₁ 0‖ < δ := by simpa [dist_eq_norm] using hy₁
    nlinarith [norm_nonneg (y₁ - h₁ 0)]
  have hsegin : ∀ u : 𝕀, u ≠ 0 → u ≠ 1 → seg u ∈ ball (0 : ℂ) 1 := fun u hu0 hu1 ↦ by
    have hu0' : (0 : ℝ) < u := lt_of_le_of_ne u.2.1 (fun h' ↦ hu0 (Subtype.ext h'.symm))
    have hu1' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun h' ↦ hu1 (Subtype.ext h'))
    have := (strictConvex_closedBall ℝ (E := ℂ) 0 1) hPm hy₁m hne₁ (a := 1 - (u : ℝ)) (b := u)
      (by linarith) hu0' (by ring)
    rwa [interior_closedBall _ one_ne_zero] at this
  have hseginj : Injective seg := fun u v h' ↦ by
    have e : ((u : ℝ) - v) • (y₁ - h₁ 0) = 0 := by
      have : seg u - seg v = 0 := sub_eq_zero.mpr h'
      simp only [seg, smul_sub, sub_smul, one_smul] at this ⊢
      linear_combination this
    rcases smul_eq_zero.mp e with h2 | h2
    · exact Subtype.ext (sub_eq_zero.mp h2)
    · exact absurd (sub_eq_zero.mp h2).symm hne₁
  let q : 𝕀 → ℂ := fun u ↦ g₁ (seg u) ^ 2
  have hz : ∀ u : 𝕀, u ≠ 0 → u ≠ 1 → g₁ (seg u) ∈ Δ₁ \ L := fun u hu0 hu1 ↦ by
    refine ⟨c.gm (hsegm u), fun hL' ↦ ?_⟩
    have h2 := hsph _ hL'
    rw [c.hg (hsegm u)] at h2
    exact (mem_ball_zero_iff.mp (hsegin u hu0 hu1)).ne h2
  have hoff : ∀ t, t ≠ 0 → t ≠ 1 → q t ∉ range a := by
    exact chord_square_image_avoids_cut_arc (a := a) r hr2 Δ₁ g₁ seg hz
  have hseg0 : seg 0 = h₁ 0 := by simp [seg]
  have hseg1 : seg 1 = y₁ := by simp [seg]
  have hq0 : q 0 = 0 := by simp [q, hseg0, hgP]
  have hq1 : q 1 = a s := by
    simp only [q, hseg1, y₁]
    rw [c.gh (hsubL hrsL), hr2]
  have hends : ∀ t : 𝕀, t = 0 ∨ t = 1 ∨ (t ≠ 0 ∧ t ≠ 1) := fun t ↦ by
    by_cases h' : t = 0
    · exact .inl h'
    · by_cases h'' : t = 1
      · exact .inr (.inl h'')
      · exact .inr (.inr ⟨h', h''⟩)
  have hendr : ∀ t : 𝕀, (t = 0 ∨ t = 1) → q t ∈ range a := by
    rintro _ (rfl | rfl)
    · exact ⟨0, h0.trans hq0.symm⟩
    · exact ⟨s, hq1.symm⟩
  have hqinj : Injective q := by
    exact quadratic_chord_injective (a := a) hne0 L Δ₁ hinjΔ h₁ g₁ c s hs0 seg hsegm hseginj hz
      hoff hq0 hq1 hends hendr
  have hqc : Continuous q := by
    have : Continuous fun u ↦ g₁ (seg u) := c.gc.comp_continuous hsegc hsegm
    exact this.pow 2
  refine ⟨s, hs0, hs1, q, ⟨hqc, hqinj⟩, hq0, hq1, ?_, hoff⟩
  rintro _ ⟨u, rfl⟩
  have h2 := hg _ (hsegm u) (hsegd u)
  rw [hgP, dist_zero_right] at h2
  have h3 : ‖q u‖ = ‖g₁ (seg u)‖ ^ 2 := norm_pow _ _
  have h4 : ‖g₁ (seg u)‖ ^ 2 < ε := by
    have := Real.lt_sqrt (norm_nonneg _) |>.mp h2
    exact this
  exact mem_ball_zero_iff.mpr (h3 ▸ h4)

end GraphMinor.GM19
