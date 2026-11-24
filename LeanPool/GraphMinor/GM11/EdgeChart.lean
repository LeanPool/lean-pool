/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.GlueDiscs
public import LeanPool.GraphMinor.Surface.Collar

/-!
# A chart around a point of an edge

`exists_edge_chart`: near a point of an edge `e` of a drawing, there is a closed disc that meets
`U(Γ)` in a
piece of `e` which is a diameter of the disc. Two facts give this. By `exists_edge_piece`, a piece
of `e`
is a chord of a small disc, so it lies in the boundary of a closed disc. A collar of this closed
disc
makes the boundary round.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval Metric

universe u

variable {S : Type u} [TopologicalSpace S]

theorem cis'_eq_exp (θ : ℝ) : cis' θ = (Circle.exp θ : ℂ) := by
  rw [Circle.coe_exp]
  rfl

private theorem exists_small_polar_chart
    {c : ℂ → S} {W : Set S} (hW : IsOpen W)
    (hc : ContinuousOn c (closedBall (0 : ℂ) 2))
    (hcinj : InjOn c (closedBall (0 : ℂ) 2))
    {w₀ : Circle} {θ₀ : ℝ} (hw₀c : cis' θ₀ = w₀) (hpW : c w₀ ∈ W) :
    ∃ ε δ : ℝ, 0 < ε ∧
      let m : ℂ → ℂ := fun z => ((1 + ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖m z‖ = 1 + ε * z.im) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ ball (0 : ℂ) 2 ∧ c (m z) ∈ W) ∧
      ContinuousOn (c ∘ m) (closedBall 0 1) ∧ InjOn (c ∘ m) (closedBall 0 1) := by
  have hopen : IsOpen (ball (0 : ℂ) 2 ∩ c ⁻¹' W) :=
    (hc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball hW
  have hmemw : (w₀ : ℂ) ∈ ball (0 : ℂ) 2 ∩ c ⁻¹' W := by
    refine ⟨by simp, ?_⟩
    exact hpW
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen _ hmemw
  obtain ⟨δ₁, hδ₁, hd⟩ := Metric.continuous_iff.mp continuous_cis' θ₀ (r / 2) (by positivity)
  obtain ⟨ε, hε, hεr, hε1⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ r / 2 ∧ ε ≤ 1 / 2 :=
    ⟨min (r / 2) (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ, hδ, hδ₂, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ δ ≤ 1 :=
    ⟨min (δ₁ / 2) 1, by positivity, (min_le_left _ _).trans_lt (by linarith), min_le_right _ _⟩
  let m : ℂ → ℂ := fun z => ((1 + ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)
  have hmc : Continuous m := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (continuous_cis'.comp ?_)
    · exact continuous_const.add (continuous_const.mul Complex.continuous_im)
    · exact continuous_const.add (continuous_const.mul Complex.continuous_re)
  have hbound : ∀ z ∈ closedBall (0 : ℂ) 1, |z.re| ≤ 1 ∧ |z.im| ≤ 1 := fun z hz => by
    have hn : ‖z‖ ≤ 1 := by simpa using hz
    exact ⟨(Complex.abs_re_le_norm z).trans hn, (Complex.abs_im_le_norm z).trans hn⟩
  have hpos : ∀ z ∈ closedBall (0 : ℂ) 1, 0 < 1 + ε * z.im := fun z hz => by
    have h₁ := abs_le.mp (hbound z hz).2
    nlinarith [h₁.1, h₁.2]
  have hmn : ∀ z ∈ closedBall (0 : ℂ) 1, ‖m z‖ = 1 + ε * z.im := fun z hz => by
    simp only [m, norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (hpos z hz)
  have hmball : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ ball (w₀ : ℂ) r := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hbound z hz
    have h₃ : dist (θ₀ + δ * z.re) θ₀ < δ₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hδ]
      nlinarith [abs_nonneg z.re]
    have h₄ : ‖cis' (θ₀ + δ * z.re) - w₀‖ < r / 2 := by
      have := hd _ h₃
      rwa [dist_eq_norm, hw₀c] at this
    have h₅ : m z - w₀ = ((ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re) + (cis' (θ₀ + δ * z.re) - w₀)
      := by
      simp only [m]
      push_cast
      ring
    have h₆ : ‖((ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)‖ ≤ r / 2 := by
      rw [norm_mul, norm_cis', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hε]
      nlinarith [abs_nonneg z.im]
    rw [mem_ball, dist_eq_norm, h₅]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hmW : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ ball (0 : ℂ) 2 ∧ c (m z) ∈ W := fun z hz =>
    hball (hmball z hz)
  have hmball2 : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ closedBall (0 : ℂ) 2 := fun z hz =>
    ball_subset_closedBall (hmW z hz).1
  let G : ℂ → S := fun z => c (m z)
  have hGc : ContinuousOn G (closedBall 0 1) :=
    hc.comp hmc.continuousOn hmball2
  have hGi : InjOn G (closedBall 0 1) := by
    intro y hy z hz hyz
    have h₁ : m y = m z := hcinj (hmball2 y hy) (hmball2 z hz) hyz
    have h₂ : y.im = z.im := by
      have := congrArg norm h₁
      rw [hmn y hy, hmn z hz] at this
      exact mul_left_cancel₀ hε.ne' (add_left_cancel this)
    have h₃ : cis' (θ₀ + δ * y.re) = cis' (θ₀ + δ * z.re) := by
      have hne : ((1 + ε * y.im : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (hpos y hy).ne'
      simp only [m, h₂] at h₁
      rw [h₂] at hne
      exact mul_left_cancel₀ hne h₁
    have h₄ : Circle.exp (θ₀ + δ * y.re) = Circle.exp (θ₀ + δ * z.re) := by
      apply Circle.ext
      rw [← cis'_eq_exp, ← cis'_eq_exp, h₃]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h₄
    have h₅ : δ * (y.re - z.re) = k * (2 * Real.pi) := by linarith
    have h₆ : |y.re - z.re| ≤ 2 := by
      have a₁ := abs_le.mp (hbound y hy).1
      have a₂ := abs_le.mp (hbound z hz).1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h₇ : |(k : ℝ) * (2 * Real.pi)| ≤ 2 := by
      rw [← h₅, abs_mul, abs_of_pos hδ]
      nlinarith [abs_nonneg (y.re - z.re)]
    have hπ := Real.pi_gt_three
    have hk0 : k = 0 := by
      by_contra hk0
      have h₈ : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h₇
      nlinarith
    have h₉ : δ * (y.re - z.re) = 0 := by rw [h₅, hk0]; simp
    have h₁₀ : y.re = z.re := by
      have := (mul_eq_zero.mp h₉).resolve_left hδ.ne'
      linarith
    exact Complex.ext h₁₀ h₂
  exact ⟨ε, δ, hε, hmn, hmW, hGc, hGi⟩

private theorem edge_chart_endpoints [T2Space S] {H : Drawing S}
    {γ : I → S} (hγ : Continuous γ) (hinj : InjOn γ (Ioo 0 1))
    {a₀ b₀ s t₀ u : I} (hIcc : Icc a₀ b₀ ⊆ Ioo 0 1)
    (hpiece : ∀ {t : I}, γ t = γ t₀ → t = t₀)
    {G : ℂ → S} (hGc : ContinuousOn G (closedBall 0 1)) (hGi : InjOn G (closedBall 0 1))
    (hG0 : G 0 = γ t₀)
    (hUiff : ∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0)
    (hreal : ∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → G z ∈ γ '' Ioo a₀ b₀)
    (havoid : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ t : I, t ≤ s ∨ u ≤ t → γ t ≠ G z) :
    ∃ (G : ℂ → S) (a b : I), ContinuousOn G (closedBall 0 1) ∧ InjOn G (closedBall 0 1) ∧
      s < a ∧ a < t₀ ∧ t₀ < b ∧ b < u ∧ G 0 = γ t₀ ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0) ∧
      G '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = γ '' Ioo a b ∧
      G '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = γ '' Icc a b ∧
      ((G (-1) = γ a ∧ G 1 = γ b) ∨ (G (-1) = γ b ∧ G 1 = γ a)) := by
  let F := γ '' Icc a₀ b₀
  -- The parameter along the diameter.
  let zv : I → ℂ := fun v => ((2 * v.1 - 1 : ℝ) : ℂ)
  have hzvc : Continuous zv := Complex.continuous_ofReal.comp (by fun_prop)
  have hzvi : Function.Injective zv := fun v w h => by
    have h₁ : 2 * v.1 - 1 = 2 * w.1 - 1 := Complex.ofReal_injective h
    exact Subtype.ext (by linarith)
  have hzvb : ∀ v, zv v ∈ closedBall (0 : ℂ) 1 := fun v => by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have := v.2.1
    have := v.2.2
    constructor <;> linarith
  have hzvim : ∀ v, (zv v).im = 0 := fun v => Complex.ofReal_im _
  have hzvex : ∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → ∃ v, z = zv v := by
    intro z hz him
    have hz_norm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have h := abs_le.mp ((Complex.abs_re_le_norm z).trans hz_norm)
    refine ⟨⟨(z.re + 1) / 2, by linarith [h.1], by linarith [h.2]⟩, Complex.ext ?_ ?_⟩
    · simp [zv]
      ring
    · simp [zv, him]
  have hzvball : ∀ v, v ∈ Ioo (0 : I) 1 ↔ zv v ∈ ball (0 : ℂ) 1 := by
    intro v
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · rintro ⟨h₁, h₂⟩
      have h₁' : (0 : ℝ) < v.1 := h₁
      have h₂' : v.1 < 1 := h₂
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      exact ⟨show (0 : ℝ) < v.1 by linarith, show v.1 < 1 by linarith⟩
  have hIccF : ∀ v, G (zv v) ∈ F := fun v => by
    obtain ⟨t, ht, hte⟩ := hreal _ (hzvb v) (hzvim v)
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hte⟩
  have hc₁ : CompactSpace (Icc a₀ b₀) := isCompact_iff_compactSpace.mp isCompact_Icc
  let j : Icc a₀ b₀ → F := fun t => ⟨γ t.1, mem_image_of_mem γ t.2⟩
  have hjc : Continuous j := Continuous.subtype_mk (hγ.comp continuous_subtype_val) _
  have hjb : Function.Bijective j := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj (hIcc x.2) (hIcc y.2) (congrArg Subtype.val hxy))
    · rintro ⟨_, t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  let q : Icc a₀ b₀ ≃ₜ F := hjc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j hjb)
  let ψ : I → I := fun v => (q.symm ⟨G (zv v), hIccF v⟩).1
  have hψγ : ∀ v, γ (ψ v) = G (zv v) := fun v =>
    congrArg Subtype.val (q.apply_symm_apply ⟨G (zv v), hIccF v⟩)
  have hψc : Continuous ψ := by
    refine continuous_subtype_val.comp (q.symm.continuous.comp (Continuous.subtype_mk ?_ _))
    exact hGc.comp_continuous hzvc hzvb
  have hψi : Function.Injective ψ := fun v w h => by
    have h₁ : G (zv v) = G (zv w) := by rw [← hψγ, ← hψγ, h]
    exact hzvi (hGi (hzvb v) (hzvb w) h₁)
  have hmid : ψ ⟨1 / 2, by norm_num, by norm_num⟩ = t₀ := by
    apply hpiece
    rw [hψγ]
    have : zv ⟨1 / 2, by norm_num, by norm_num⟩ = 0 := by simp [zv]
    rw [this, hG0]
  have hboth : ∀ v, s < ψ v ∧ ψ v < u := by
    intro v
    exact ⟨lt_of_not_ge fun h => havoid _ (hzvb v) _ (Or.inl h) (hψγ v),
      lt_of_not_ge fun h => havoid _ (hzvb v) _ (Or.inr h) (hψγ v)⟩
  have hz0 : zv 0 = -1 := by simp [zv]
  have hz1 : zv 1 = 1 := by
    simp only [zv]
    norm_num
  have hmid₀ : (0 : I) < ⟨1 / 2, by norm_num, by norm_num⟩ :=
    show (0 : ℝ) < 1 / 2 by norm_num
  have hmid₁ : (⟨1 / 2, by norm_num, by norm_num⟩ : I) < 1 :=
    show (1 / 2 : ℝ) < 1 by norm_num
  have hrange : ∀ {a b : I}, a ∈ range ψ → b ∈ range ψ → Icc a b ⊆ range ψ := fun ha hb =>
    isPreconnected_range hψc |>.Icc_subset ha hb
  have hseg₁ : ∀ X : Set I, G '' (zv '' X) = γ '' (ψ '' X) := by
    intro X
    rw [image_image, image_image]
    exact image_congr fun v _ => (hψγ v).symm
  have hball' : {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = zv '' Ioo 0 1 := by
    ext z
    constructor
    · rintro ⟨hz, him⟩
      obtain ⟨v, rfl⟩ := hzvex z (ball_subset_closedBall hz) him
      exact ⟨v, (hzvball v).mpr hz, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(hzvball v).mp hv, hzvim v⟩
  have hclosed' : {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = zv '' univ := by
    ext z
    constructor
    · rintro ⟨hz, him⟩
      obtain ⟨v, rfl⟩ := hzvex z hz him
      exact ⟨v, mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩
      exact ⟨hzvb v, hzvim v⟩
  rcases Continuous.strictMono_of_inj hψc hψi with hmono | hanti
  · refine ⟨G, ψ 0, ψ 1, hGc, hGi, (hboth 0).1, ?_, ?_, (hboth 1).2, hG0, hUiff, ?_, ?_, Or.inl ?_⟩
    · rw [← hmid]
      exact hmono hmid₀
    · rw [← hmid]
      exact hmono hmid₁
    · rw [hball', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨hmono hv.1, hmono hv.2⟩
      · rintro t ⟨h₁, h₂⟩
        obtain ⟨v, rfl⟩ := hrange ⟨0, rfl⟩ ⟨1, rfl⟩ (⟨h₁.le, h₂.le⟩ : t ∈ Icc (ψ 0) (ψ 1))
        exact ⟨v, ⟨hmono.lt_iff_lt.mp h₁, hmono.lt_iff_lt.mp h₂⟩, rfl⟩
    · rw [hclosed', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, -, rfl⟩
        exact ⟨hmono.monotone v.2.1, hmono.monotone v.2.2⟩
      · rintro t ht
        obtain ⟨v, rfl⟩ := hrange ⟨0, rfl⟩ ⟨1, rfl⟩ ht
        exact ⟨v, mem_univ _, rfl⟩
    · exact ⟨by rw [← hz0, hψγ], by rw [hψγ 1, hz1]⟩
  · refine ⟨G, ψ 1, ψ 0, hGc, hGi, (hboth 1).1, ?_, ?_, (hboth 0).2, hG0, hUiff, ?_, ?_, Or.inr ?_⟩
    · rw [← hmid]
      exact hanti hmid₁
    · rw [← hmid]
      exact hanti hmid₀
    · rw [hball', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨hanti hv.2, hanti hv.1⟩
      · rintro t ⟨h₁, h₂⟩
        obtain ⟨v, rfl⟩ := hrange ⟨1, rfl⟩ ⟨0, rfl⟩ (⟨h₁.le, h₂.le⟩ : t ∈ Icc (ψ 1) (ψ 0))
        exact ⟨v, ⟨hanti.lt_iff_gt.mp h₂, hanti.lt_iff_gt.mp h₁⟩, rfl⟩
    · rw [hclosed', hseg₁]
      congr 1
      apply subset_antisymm
      · rintro _ ⟨v, -, rfl⟩
        exact ⟨hanti.antitone v.2.2, hanti.antitone v.2.1⟩
      · rintro t ht
        obtain ⟨v, rfl⟩ := hrange ⟨1, rfl⟩ ⟨0, rfl⟩ ht
        exact ⟨v, mem_univ _, rfl⟩
    · exact ⟨by rw [← hz0, hψγ], by rw [hψγ 1, hz1]⟩

/-- **A chart around a point of an edge.** Here `G` maps the closed unit disc of `ℂ` onto a closed
disc
around `γ t₀`. The real part of the disc is the piece of `e` from `γ a` to `γ b`, and there is no
other
point of `U(H)` in the disc. -/
theorem exists_edge_chart (hS : IsClosedSurface S) (H : Drawing S) {e : Set S} (he : e ∈ H.E)
    {γ : I → S} (hγ : Continuous γ) (hγ0 : γ 0 ∈ H.V) (hγ1 : γ 1 ∈ H.V) (hinj : InjOn γ (Ioo 0 1))
    (hγe : γ '' Ioo 0 1 = e) {s t₀ u : I} (ht₀ : t₀ ∈ Ioo (0 : I) 1) (hs : s < t₀) (hu : t₀ < u) :
    ∃ (G : ℂ → S) (a b : I), ContinuousOn G (closedBall 0 1) ∧ InjOn G (closedBall 0 1) ∧
      s < a ∧ a < t₀ ∧ t₀ < b ∧ b < u ∧ G 0 = γ t₀ ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0) ∧
      G '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = γ '' Ioo a b ∧
      G '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} = γ '' Icc a b ∧
      ((G (-1) = γ a ∧ G 1 = γ b) ∨ (G (-1) = γ b ∧ G 1 = γ a)) := by
  classical
  have hT2 : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hpe : γ t₀ ∈ e := hγe ▸ mem_image_of_mem γ ht₀
  have hX₀ := isClosed_U_sdiff_edge H he
  have hmemIoo : ∀ {t : I}, γ t ∈ e → γ t ∉ H.V := fun h => (he.2.1 h).2
  have hend : ∀ {t : I}, t ∉ Ioo (0 : I) 1 → γ t ∈ H.V := by
    intro t ht
    have : t = 0 ∨ t = 1 := by
      by_contra hc
      push Not at hc
      exact ht ⟨unitInterval.pos_iff_ne_zero.mpr hc.1, unitInterval.lt_one_iff_ne_one.mpr hc.2⟩
    rcases this with rfl | rfl
    · exact hγ0
    · exact hγ1
  have hpiece : ∀ {t : I}, γ t = γ t₀ → t = t₀ := by
    intro t ht
    by_cases hti : t ∈ Ioo (0 : I) 1
    · exact hinj hti ht₀ ht
    · exact absurd (ht ▸ hend hti) (hmemIoo hpe)
  -- The closed set to avoid.
  let Y₀ : Set S := (H.U \ e) ∪ γ '' {t | t ≤ s ∨ u ≤ t}
  have hY₀ : IsClosed Y₀ :=
    hX₀.union ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY₀ : γ t₀ ∉ Y₀ := by
    rintro (h | ⟨t, ht, hte⟩)
    · exact h.2 hpe
    · have := hpiece hte
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr hs)
      · exact absurd h (not_le.mpr hu)
  obtain ⟨D, D', a₀, b₀, hD, hD', hpD', hD'D, hDO, hbdD, ha₀, hb₀, hIcc, hIoo, hFline, hFD, hFcap,
    hst⟩ :=
    exists_edge_piece hS H he hγ hγ0 hγ1 hinj hγe ht₀ hY₀.isOpen_compl hpY₀
      (disjoint_left.mpr fun x hx h => hx (Or.inl h))
  set F : Set S := γ '' Icc a₀ b₀ with hF
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, -, -, -, hbd₁, -, -⟩ :=
    disc_iArc D F (γ a₀) (γ b₀) hD hFD hst hFline hFcap
  have hA₁ : A₁ ⊆ discBd D := by
    have hmem : A₁ ∈ componentsIn (discBd D \ {γ a₀, γ b₀}) := by rw [hcomp]; simp
    obtain ⟨x, -, rfl⟩ := hmem
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hA₁D' : Disjoint A₁ D' := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    have := hA₁ hx
    rw [← hbdD] at this
    exact this.2 hx'
  have hFU : F ⊆ H.U := by
    rintro _ ⟨t, ht, rfl⟩
    exact (he.2.1 (hγe ▸ mem_image_of_mem γ (hIcc ht))).1
  -- The rest of `U(H)`.
  let Y₁ : Set S := (H.U \ e) ∪ γ '' {t | t ≤ a₀ ∨ b₀ ≤ t}
  have hY₁ : IsClosed Y₁ :=
    hX₀.union ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY₁ : γ t₀ ∉ Y₁ := by
    rintro (h | ⟨t, ht, hte⟩)
    · exact h.2 hpe
    · have := hpiece hte
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr ha₀)
      · exact absurd h (not_le.mpr hb₀)
  let W : Set S := D' ∩ Y₁ᶜ
  have hW : IsOpen W := hD'.inter hY₁.isOpen_compl
  have hpW : γ t₀ ∈ W := ⟨hpD', hpY₁⟩
  have hWO : ∀ {x}, x ∈ W → x ∉ Y₀ := fun hx => hDO (hD'D hx.1)
  -- The collar of `Δ₁`.
  have hpbd : γ t₀ ∈ discBd Δ₁ := by
    rw [hbd₁]
    exact Or.inr (mem_image_of_mem γ ⟨ha₀.le, hb₀.le⟩)
  obtain ⟨p⟩ := hΔ₁.isOArc_discBd
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hΔ₁ (fun x _ => hS.2.2 x) isOpen_univ
    (subset_univ _)
  obtain ⟨c, c', hc, -, -, -, hl, -, -, -, hcp⟩ := exists_disc_collar hΔ₁ hΔ' hin p
  have hcinj : InjOn c (closedBall 0 2) := hl.injOn
  let w₀ : Circle := p.symm ⟨γ t₀, hpbd⟩
  have hcw₀ : c w₀ = γ t₀ := by
    rw [hcp]
    simp [w₀]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, Circle.exp θ₀ = w₀ := by
    refine ⟨Complex.arg (w₀ : ℂ), ?_⟩
    exact Circle.exp_arg w₀
  have hw₀c : cis' θ₀ = w₀ := by rw [cis'_eq_exp, hθ₀]
  obtain ⟨ε, δ, hε, hmn, hmW, hGc, hGi⟩ :=
    exists_small_polar_chart hW hc hcinj hw₀c (hcw₀.symm ▸ hpW)
  let m : ℂ → ℂ := fun z => ((1 + ε * z.im : ℝ) : ℂ) * cis' (θ₀ + δ * z.re)
  have hmball2 : ∀ z ∈ closedBall (0 : ℂ) 1, m z ∈ closedBall (0 : ℂ) 2 := fun z hz =>
    ball_subset_closedBall (hmW z hz).1
  let G : ℂ → S := c ∘ m
  have hG0 : G 0 = γ t₀ := by
    change c (m 0) = _
    have : m 0 = w₀ := by simp [m, hw₀c]
    rw [this, hcw₀]
  -- The real points map to the piece.
  have hreal : ∀ z ∈ closedBall (0 : ℂ) 1, z.im = 0 → G z ∈ γ '' Ioo a₀ b₀ := by
    intro z hz him
    have hmz : m z = (Circle.exp (θ₀ + δ * z.re) : ℂ) := by
      simp only [m, him, mul_zero, add_zero, Complex.ofReal_one, one_mul]
      exact cis'_eq_exp _
    have hW' := (hmW z hz).2
    have hb : G z ∈ discBd Δ₁ := by
      change c (m z) ∈ _
      rw [hmz, hcp]
      exact (p _).2
    rw [hbd₁] at hb
    rcases hb with hb | ⟨t, ht, hte⟩
    · exact absurd hW'.1 (disjoint_left.mp hA₁D' hb)
    · refine ⟨t, ?_, hte⟩
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · rintro rfl
        exact hW'.2 (Or.inr ⟨_, Or.inl le_rfl, hte⟩)
      · rintro rfl
        exact hW'.2 (Or.inr ⟨_, Or.inr le_rfl, hte⟩)
  have hUiff : ∀ z ∈ closedBall (0 : ℂ) 1, G z ∈ H.U ↔ z.im = 0 := by
    intro z hz
    constructor
    · intro hzU
      have hW' := (hmW z hz).2
      have hze : G z ∈ e := by
        by_contra hn
        exact hW'.2 (Or.inl ⟨hzU, hn⟩)
      obtain ⟨t, ht, hte⟩ : G z ∈ γ '' Ioo 0 1 := hγe ▸ hze
      have htab : t ∈ Icc a₀ b₀ := by
        by_contra hn
        have : t ≤ a₀ ∨ b₀ ≤ t := by
          by_contra hc'
          push Not at hc'
          exact hn ⟨hc'.1.le, hc'.2.le⟩
        exact hW'.2 (Or.inr ⟨t, this, hte⟩)
      have hb : G z ∈ discBd Δ₁ := by
        rw [hbd₁]
        exact Or.inr ⟨t, htab, hte⟩
      obtain ⟨w, hw⟩ := (show ∃ w : discBd Δ₁, w.1 = G z from ⟨⟨_, hb⟩, rfl⟩)
      have hcw : c (p.symm w) = G z := by
        rw [hcp]
        simpa using hw
      have hwn : ((p.symm w : Circle) : ℂ) ∈ closedBall (0 : ℂ) 2 := by simp
      have heq := hcinj hwn (hmball2 z hz) hcw
      have hn₁ : ‖m z‖ = 1 + ε * z.im := hmn z hz
      rw [← heq] at hn₁
      simp only [Circle.norm_coe] at hn₁
      have : ε * z.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hε.ne'
    · intro him
      obtain ⟨t, ht, hte⟩ := hreal z hz him
      exact hte ▸ hFU ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  exact edge_chart_endpoints hγ hinj hIcc hpiece hGc hGi hG0 hUiff hreal
    (fun z hz t ht heq => hWO (hmW z hz).2 (Or.inr ⟨t, ht, heq⟩))

end GraphMinor.GM11
