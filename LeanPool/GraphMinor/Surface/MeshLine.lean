/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutTree

/-!
# A line and the long pieces of it inside a Jordan domain

Let `W` be the inner domain of an `O`-arc `F`, and `L` a line. `L ∩ W` is a union of open segments.
The theorem `no_cross` says: if a connected subset `G` of `W` avoids all segments of length at least
`δ`, then `G` has no two points on opposite sides of `L` at distance more than `ρ` from it. Here `δ`
depends only on `F` and `ρ`.

The proof uses logarithms. Suppose `G` has such points `y₁, y₂`, and let `f = (z - y₂) / (z - y₁)`.
Let `K` be the complement of `W` in a large ball together with the long segments. `G` joins `y₁` to
`y₂` off `K`, so `f` has a logarithm `l` on `K`. It also has a logarithm `g` on a long piece `I` of
`L`, since `I` is an arc. The difference `l - g` on `K ∩ I` takes values in `2πiℤ`. It does not
jump across a short segment `s` of `L ∩ W`: the ends of `s` are near each other on `F`, so a small
arc `A` of `F` joins them, and `f` has a logarithm on a small disc around `s ∪ A`, which compares
`l` and `g` at the two ends. So `l - g` is constant, and the two logarithms paste on `K ∪ I`. Then
`y₁, y₂` lie in one component of the complement of `K ∪ I`, and this is false because `I` is a
piece of `L` that crosses the ball.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

local notation "𝕀" => unitInterval

/-- Near points of an `O`-arc are joined by a small connected subset of the arc. -/
theorem exists_small_arc {F : Set ℂ} (φ : Circle ≃ₜ F) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ F, ∀ v ∈ F, dist u v < δ →
      ∃ A ⊆ F, IsPreconnected A ∧ u ∈ A ∧ v ∈ A ∧ A ⊆ ball u ρ := by
  obtain ⟨η, δ, hη, hηπ, hδ, hnear, hfar⟩ := exists_arc_constants φ hρ
  refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
  let t : Circle := φ.symm ⟨u, hu⟩
  have hut : arcPoint φ t 0 = u := by simp [arcPoint, t]
  obtain ⟨θ, h1, h2, h3⟩ := exists_angle_near t (φ.symm ⟨v, hv⟩) η hη.le hηπ.le
  have hvθ : arcPoint φ t θ = v := by simp [arcPoint, ← h3]
  have hθ : θ ≤ η := by
    by_contra hc
    have := hfar t θ ⟨(not_le.mp hc).le, h2⟩
    rw [hvθ, hut, dist_comm] at this
    linarith
  have hthetac : Continuous fun θ : ℝ => arcPoint φ t θ :=
    (continuous_arcPoint φ).comp (continuous_const.prodMk continuous_id)
  refine ⟨(fun θ : ℝ => arcPoint φ t θ) '' Icc (-η) η, ?_, isPreconnected_Icc.image _
    hthetac.continuousOn,
    ⟨0, ⟨by linarith, hη.le⟩, hut⟩, ⟨θ, ⟨h1, hθ⟩, hvθ⟩, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact (φ _).2
  · rintro _ ⟨r, hr, rfl⟩
    rw [mem_ball, ← hut]
    exact hnear t r (abs_le.mpr hr)

/-- A point of a bounded open set of reals lies in an interval of the set with ends outside it. -/
theorem exists_interval_of_mem {V : Set ℝ} (hV : IsOpen V) (hb : Bornology.IsBounded V) {r : ℝ}
    (hr : r ∈ V) : ∃ a b, r ∈ Ioo a b ∧ Ioo a b ⊆ V ∧ a ∉ V ∧ b ∉ V := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hout : ∀ x, R < |x| → x ∉ V := fun x hx hxV => by
    have := hR hxV
    rw [mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  have hA : IsClosed (Vᶜ ∩ Iic r) := hV.isClosed_compl.inter isClosed_Iic
  have hB : IsClosed (Vᶜ ∩ Ici r) := hV.isClosed_compl.inter isClosed_Ici
  have hRabs : |r| ≤ R := by
    have := hR hr
    rwa [mem_closedBall, Real.dist_eq, sub_zero] at this
  have hRnn : 0 ≤ R := (abs_nonneg r).trans hRabs
  have hneA : (Vᶜ ∩ Iic r).Nonempty := by
    refine ⟨-R - 1, hout _ ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · have := (abs_le.mp hRabs).1
      change -R - 1 ≤ r
      linarith
  have hneB : (Vᶜ ∩ Ici r).Nonempty := by
    refine ⟨R + 1, hout _ ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · have := (abs_le.mp hRabs).2
      change r ≤ R + 1
      linarith
  have hbddA : BddAbove (Vᶜ ∩ Iic r) := ⟨r, fun _ h => h.2⟩
  have hbddB : BddBelow (Vᶜ ∩ Ici r) := ⟨r, fun _ h => h.2⟩
  have ha := hA.csSup_mem hneA hbddA
  have hb' := hB.csInf_mem hneB hbddB
  set a := sSup (Vᶜ ∩ Iic r)
  set b := sInf (Vᶜ ∩ Ici r)
  have har : a < r := lt_of_le_of_ne ha.2 fun h => ha.1 (h ▸ hr)
  have hrb : r < b := lt_of_le_of_ne hb'.2 fun h => hb'.1 (h.symm ▸ hr)
  refine ⟨a, b, ⟨har, hrb⟩, fun x hx => ?_, ha.1, hb'.1⟩
  by_contra hn
  rcases le_total x r with h | h
  · exact absurd (le_csSup hbddA ⟨hn, h⟩) (not_le.mpr hx.1)
  · exact absurd (csInf_le hbddB ⟨hn, h⟩) (not_le.mpr hx.2)

/-- Two such intervals through a point are equal. -/
theorem interval_unique {V : Set ℝ} {a b c d : ℝ} (h1 : Ioo a b ⊆ V) (h2 : Ioo c d ⊆ V) (ha : a ∉ V)
    (hb : b ∉ V) (hc : c ∉ V) (hd : d ∉ V) {r : ℝ} (hr : r ∈ Ioo a b) (hr' : r ∈ Ioo c d) :
    a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with h | h | h
    · exact absurd (h1 ⟨h, hr'.1.trans hr.2⟩) hc
    · exact h
    · exact absurd (h2 ⟨h, hr.1.trans hr'.2⟩) ha
  have hbd : b = d := by
    rcases lt_trichotomy b d with h | h | h
    · exact absurd (h2 ⟨hr'.1.trans hr.2, h⟩) hb
    · exact h
    · exact absurd (h1 ⟨hr.1.trans hr'.2, h⟩) hd
  exact ⟨hac, hbd⟩

private theorem exp_sub_eq_one {w u v : ℂ} (h1 : w = exp u) (h2 : w = exp v) : exp (u - v) = 1 := by
  rw [exp_sub, ← h1, ← h2]
  exact div_self (h1 ▸ exp_ne_zero u)

/-- Different elements of a coset of `2πiℤ` are at least `2π` apart. -/
private theorem two_pi_le_norm {u : ℂ} (h : exp u = 1) (hne : u ≠ 0) : 2 * Real.pi ≤ ‖u‖ := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk)
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : 1 ≤ |k| := Int.one_le_abs hk0
    exact_mod_cast this
  rw [hk, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

/-- The logarithms differ by a constant beyond the short gaps cut out of the line. -/
private theorem lineLogDifference_constant {F : Set ℂ} (J : IsJordanParts F)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδρ : δ ≤ ρ)
    (hsmall : ∀ u ∈ F, ∀ v ∈ F, dist u v < δ →
      ∃ A ⊆ F, IsPreconnected A ∧ u ∈ A ∧ v ∈ A ∧ A ⊆ ball u ρ)
    {ι : ℝ → ℂ} (hιc : Continuous ι)
    (hdistι : ∀ r s, dist (ι r) (ι s) = |r - s|) {ℓ : ℂ → ℝ} {t : ℝ}
    (hlip : ∀ z r, |ℓ z - t| ≤ dist z (ι r)) {y₁ y₂ : ℂ}
    (h1 : ℓ y₁ < t - ρ) (h2 : t + ρ < ℓ y₂) {R N : ℝ}
    (hRF : ∀ z ∈ F, ‖z‖ < R) (hNpos : 0 < N) :
    let W := inner F
    let V := ι ⁻¹' W
    let Z := {r | r ∈ V ∧ ∃ a b, r ∈ Ioo a b ∧ Ioo a b ⊆ V ∧ a ∉ V ∧ b ∉ V ∧ δ ≤ b - a}
    let E := Vᶜ ∪ Z
    let Q := Icc (-N) N
    let P := E ∩ Q
    let B := closedBall (0 : ℂ) (‖ι 0‖ + N + R)
    let K := (Wᶜ ∩ B) ∪ ι '' P
    let I := ι '' Q
    let f := fun z : ℂ => (z - y₂) / (z - y₁)
    ∀ l g : ℂ → ℂ,
      let n := fun r : ℝ => l (ι r) - g (ι r)
      let n₀ := n (-N)
      IsCompact P → ContinuousOn n P → (∀ r ∈ P, exp (n r) = 1) → (-N) ∈ P →
      ContinuousOn l K → (∀ z ∈ K, f z = exp (l z)) →
      ContinuousOn g I → (∀ z ∈ I, f z = exp (g z)) → ∀ r ∈ P, n r = n₀ := by
  classical
  intro W V Z E Q P B K I f l g n n₀ hPc hnc hnexp hstart hlc hl hgc hg
  have hW : W = inner F := rfl
  have hn₀ : n₀ = n (-N) := rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨r₂, hr₂, hne⟩ := hcon
  let d : ℝ → ℝ := fun r => ‖n r - n₀‖
  have hdc : ContinuousOn d P := (hnc.sub continuousOn_const).norm
  have hP₁ : IsClosed (P ∩ d ⁻¹' Iic 0) :=
    hdc.preimage_isClosed_of_isClosed hPc.isClosed isClosed_Iic
  have hP₂ : IsClosed (P ∩ d ⁻¹' Ici (2 * Real.pi)) :=
    hdc.preimage_isClosed_of_isClosed hPc.isClosed isClosed_Ici
  have hcase : ∀ r ∈ P, r ∈ d ⁻¹' Iic 0 ∨ r ∈ d ⁻¹' Ici (2 * Real.pi) := by
    intro r hr
    by_cases h : n r = n₀
    · left
      change ‖n r - n₀‖ ≤ 0
      rw [h, sub_self, norm_zero]
    · right
      refine two_pi_le_norm ?_ (sub_ne_zero.mpr h)
      rw [exp_sub, hnexp r hr, hnexp _ hstart, div_one]
  have hd₀ : (-N) ∈ d ⁻¹' Iic 0 := by
    change ‖n (-N) - n₀‖ ≤ 0
    rw [← hn₀, sub_self, norm_zero]
  have hd₂ : r₂ ∈ d ⁻¹' Ici (2 * Real.pi) := by
    refine (hcase r₂ hr₂).resolve_left fun h => hne ?_
    have : ‖n r₂ - n₀‖ ≤ 0 := h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hdisj : ∀ r, r ∈ d ⁻¹' Iic 0 → r ∈ d ⁻¹' Ici (2 * Real.pi) → False := by
    intro r h1' h2'
    have h3 : d r ≤ 0 := h1'
    have h4 : 2 * Real.pi ≤ d r := h2'
    linarith [Real.pi_pos]
  obtain ⟨u, hu, humax⟩ := ((hPc.of_isClosed_subset hP₁ inter_subset_left).inter_right
    (isClosed_Iic (a := r₂))).exists_isGreatest ⟨-N, ⟨hstart, hd₀⟩, hr₂.2.1⟩
  obtain ⟨v, hv, hvmin⟩ := ((hPc.of_isClosed_subset hP₂ inter_subset_left).inter_right
    (isClosed_Ici (a := u))).exists_isLeast ⟨r₂, ⟨hr₂, hd₂⟩, hu.2⟩
  have huv : u < v := lt_of_le_of_ne hv.2 fun h => hdisj u hu.1.2 (h ▸ hv.1.2)
  have hgapP : ∀ r ∈ Ioo u v, r ∉ P := by
    intro r hr hrP
    rcases hcase r hrP with h | h
    · exact absurd (humax ⟨⟨hrP, h⟩, (hr.2.le.trans (hvmin ⟨⟨hr₂, hd₂⟩, hu.2⟩))⟩) (not_le.mpr hr.1)
    · exact absurd (hvmin ⟨⟨hrP, h⟩, hr.1.le⟩) (not_le.mpr hr.2)
  have huQ : u ∈ Q := hu.1.1.2
  have hvQ : v ∈ Q := hv.1.1.2
  have hgapV : ∀ r ∈ Ioo u v, r ∈ V ∧ r ∉ Z := by
    intro r hr
    have hrQ : r ∈ Q := ⟨huQ.1.trans hr.1.le, hr.2.le.trans hvQ.2⟩
    have hrE : r ∉ E := fun h => hgapP r hr ⟨h, hrQ⟩
    constructor
    · by_contra hn
      exact hrE (Or.inl hn)
    · exact fun h => hrE (Or.inr h)
  have hsub : Ioo u v ⊆ V := fun r hr => (hgapV r hr).1
  have huV : u ∉ V := by
    intro huV
    rcases hu.1.1.1 with h | ⟨-, c, e, hce, hs, hc, he, hl⟩
    · exact h huV
    · obtain ⟨r, hr⟩ := exists_between (lt_min huv hce.2)
      have hrIoo : r ∈ Ioo u v := ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
      have hrce : r ∈ Ioo c e := ⟨hce.1.trans hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
      exact (hgapV r hrIoo).2 ⟨hs hrce, c, e, hrce, hs, hc, he, hl⟩
  have hvV : v ∉ V := by
    intro hvV
    rcases hv.1.1.1 with h | ⟨-, c, e, hce, hs, hc, he, hl⟩
    · exact h hvV
    · obtain ⟨r, hr⟩ := exists_between (max_lt huv hce.1)
      have hrIoo : r ∈ Ioo u v := ⟨lt_of_le_of_lt (le_max_left _ _) hr.1, hr.2⟩
      have hrce : r ∈ Ioo c e := ⟨lt_of_le_of_lt (le_max_right _ _) hr.1, hr.2.trans hce.2⟩
      exact (hgapV r hrIoo).2 ⟨hs hrce, c, e, hrce, hs, hc, he, hl⟩
  have hshort : v - u < δ := by
    by_contra hc
    rw [not_lt] at hc
    obtain ⟨r, hr⟩ := exists_between huv
    exact (hgapV r hr).2 ⟨hsub hr, u, v, hr, hsub, huV, hvV, hc⟩
  -- The ends of the short segment lie on `F`.
  have hend : ∀ x ∈ Icc u v, x ∉ V → ι x ∈ F := by
    intro x hx hxV
    have h3 : ι x ∈ closure (ι '' Ioo u v) := by
      have h4 : x ∈ closure (Ioo u v) := by rw [closure_Ioo huv.ne]; exact hx
      exact image_closure_subset_closure_image hιc ⟨x, h4, rfl⟩
    have h5 : ι '' Ioo u v ⊆ W := by
      rintro _ ⟨r, hr, rfl⟩
      exact hsub hr
    have h6 := closure_mono h5 h3
    rw [hW, J.closure_inner] at h6
    exact h6.resolve_left hxV
  have huF := hend u ⟨le_rfl, huv.le⟩ huV
  have hvF := hend v ⟨huv.le, le_rfl⟩ hvV
  have hduv : dist (ι u) (ι v) < δ := by
    rw [hdistι, abs_sub_comm, abs_of_pos (by linarith)]
    exact hshort
  obtain ⟨A, hAF, hApre, huA, hvA, hAball⟩ := hsmall _ huF _ hvF hduv
  set D := closedBall (ι u) ρ with hD
  have hyD : ∀ y, ρ < |ℓ y - t| → y ∉ D := by
    intro y hy hyD
    have h3 := hlip y u
    have h4 : dist y (ι u) ≤ ρ := hyD
    linarith
  have hy₁D : y₁ ∉ D := hyD _ (by rw [abs_of_neg (by linarith)]; linarith)
  have hy₂D : y₂ ∉ D := hyD _ (by rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨lD, hlDc, hlD⟩ := hasLogOn_closedBall (f := f) hρ.le
    (ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_id.sub continuousOn_const) fun z hz => sub_ne_zero.mpr fun e => hy₁D (e ▸ hz))
    (fun z hz => div_ne_zero (sub_ne_zero.mpr fun e => hy₂D (e ▸ hz))
      (sub_ne_zero.mpr fun e => hy₁D (e ▸ hz)))
  have hAD : A ⊆ D := fun z hz => ball_subset_closedBall (hAball hz)
  have hFK : ∀ z ∈ F, z ∈ K := fun z hz => Or.inl ⟨hz |> fun hz' hzW => hzW.1 hz', by
    refine mem_closedBall_zero_iff.mpr ?_
    have := hRF z hz
    have h0 := norm_nonneg (ι 0)
    linarith⟩
  have hAK : A ⊆ K := fun z hz => hFK z (hAF hz)
  have hval1 : l (ι v) - lD (ι v) = l (ι u) - lD (ι u) :=
    eq_of_exp_eq_one hApre ((hlc.mono hAK).sub (hlDc.mono hAD))
      (fun z hz => exp_sub_eq_one (hl z (hAK hz)) (hlD z (hAD hz))) hvA huA
  let S := ι '' Icc u v
  have hSpre : IsPreconnected S := isPreconnected_Icc.image _ hιc.continuousOn
  have hSI : S ⊆ I := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, ⟨huQ.1.trans hr.1, hr.2.trans hvQ.2⟩, rfl⟩
  have hSD : S ⊆ D := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hD, mem_closedBall, hdistι, abs_of_nonneg (by linarith [hr.1])]
    linarith [hr.2]
  have hval2 : g (ι v) - lD (ι v) = g (ι u) - lD (ι u) :=
    eq_of_exp_eq_one hSpre ((hgc.mono hSI).sub (hlDc.mono hSD))
      (fun z hz => exp_sub_eq_one (hg z (hSI hz)) (hlD z (hSD hz)))
      ⟨v, ⟨huv.le, le_rfl⟩, rfl⟩ ⟨u, ⟨le_rfl, huv.le⟩, rfl⟩
  have hnuv : n v = n u := by
    simp only [n]
    linear_combination hval1 - hval2
  have hdv : d v = d u := by simp only [d, hnuv]
  exact hdisj u hu.1.2 (by
    have : d u ∈ Ici (2 * Real.pi) := hdv ▸ hv.1.2
    exact this)

/-- A connected subset of `inner F` that avoids the long segments of a line cannot reach far on
both sides of the line. See the module docstring for the proof. -/
theorem no_cross {F : Set ℂ} (φ : Circle ≃ₜ F) {ρ δ : ℝ} (hρ : 0 < ρ) (hδρ : δ ≤ ρ)
    (hsmall : ∀ u ∈ F, ∀ v ∈ F, dist u v < δ →
      ∃ A ⊆ F, IsPreconnected A ∧ u ∈ A ∧ v ∈ A ∧ A ⊆ ball u ρ)
    {ι : ℝ → ℂ} (hι : Isometry ι) {ℓ : ℂ → ℝ} (hℓ : Continuous ℓ) {t : ℝ}
    (hline : ∀ z, ℓ z = t → z ∈ range ι) (hℓι : ∀ r, ℓ (ι r) = t)
    (hlip : ∀ z r, |ℓ z - t| ≤ dist z (ι r)) {G : Set ℂ} (hG : IsPreconnected G)
    (hGW : G ⊆ inner F)
    (hlong : ∀ a b, Ioo a b ⊆ ι ⁻¹' inner F → ι a ∉ inner F → ι b ∉ inner F → δ ≤ b - a →
      ∀ r ∈ Ioo a b, ι r ∉ G)
    {y₁ y₂ : ℂ} (hy₁ : y₁ ∈ G) (hy₂ : y₂ ∈ G) (h1 : ℓ y₁ < t - ρ) (h2 : t + ρ < ℓ y₂) : False := by
  classical
  have J := isJordanParts φ
  set W := inner F with hW
  have hWo : IsOpen W := J.isOpen_inner
  have hιc := hι.continuous
  have hιi := hι.injective
  obtain ⟨R, hR⟩ := J.isCompact_closure_inner.isBounded.subset_ball 0
  have hRW : ∀ z ∈ W, ‖z‖ < R := fun z hz => mem_ball_zero_iff.mp (hR (Or.inl hz))
  have hRF : ∀ z ∈ F, ‖z‖ < R := fun z hz => mem_ball_zero_iff.mp (hR (Or.inr hz))
  have hdistι : ∀ r s, dist (ι r) (ι s) = |r - s| := fun r s => by
    rw [hι.dist_eq, Real.dist_eq]
  have hnorm_le : ∀ r, ‖ι r‖ ≤ ‖ι 0‖ + |r| := fun r => by
    have h := norm_sub_norm_le (ι r) (ι 0)
    rw [← dist_eq_norm, hdistι, sub_zero] at h
    linarith
  have hnorm_ge : ∀ r, |r| ≤ ‖ι r‖ + ‖ι 0‖ := fun r => by
    have h := norm_sub_le (ι r) (ι 0)
    rw [← dist_eq_norm, hdistι, sub_zero] at h
    exact h
  have hR0 : 0 ≤ R := by
    obtain ⟨z, hz⟩ := J.isConnected_inner.nonempty
    exact (norm_nonneg z).trans (hRW z hz).le
  set N := R + ‖ι 0‖ + 1 with hN
  have hNpos : 0 < N := by positivity
  set R' := ‖ι 0‖ + N + R with hR'
  set V := ι ⁻¹' W with hV
  have hVo : IsOpen V := hWo.preimage hιc
  have hVb : Bornology.IsBounded V := by
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := N)).subset fun r hr => ?_
    have h3 := hRW _ hr
    have h4 := hnorm_ge r
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    linarith
  let Z : Set ℝ := {r | r ∈ V ∧ ∃ a b, r ∈ Ioo a b ∧ Ioo a b ⊆ V ∧ a ∉ V ∧ b ∉ V ∧ δ ≤ b - a}
  let E : Set ℝ := Vᶜ ∪ Z
  have hEc : IsClosed E := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro r hr
    have hrV : r ∈ V := by
      by_contra hn
      exact hr (Or.inl hn)
    have hrZ : r ∉ Z := fun h => hr (Or.inr h)
    obtain ⟨a, b, hab, hsub, ha, hb⟩ := exists_interval_of_mem hVo hVb hrV
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hab) fun r' hr' hE => ?_
    rcases hE with hE | ⟨hr'V, c, d, hcd, hsub', hc, hd, hl⟩
    · exact hE (hsub hr')
    · obtain ⟨rfl, rfl⟩ := interval_unique hsub hsub' ha hb hc hd hr' hcd
      exact hrZ ⟨hrV, _, _, hab, hsub, ha, hb, hl⟩
  set Q := Icc (-N) N with hQ
  set P := E ∩ Q with hP
  have hPc : IsCompact P := isCompact_Icc.inter_left hEc
  set B := closedBall (0 : ℂ) R' with hB
  set K := (Wᶜ ∩ B) ∪ ι '' P with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) R').inter_left hWo.isClosed_compl).union (hPc.image hιc)
  have hGK : G ⊆ Kᶜ := by
    rintro z hz (h | ⟨r, hr, rfl⟩)
    · exact h.1 (hGW hz)
    · rcases hr.1 with h | ⟨hrV, a, b, hab, hsub, ha, hb, hl⟩
      · exact h (hGW hz)
      · exact hlong a b hsub ha hb hl r hab hz
  have hcomp : y₂ ∈ connectedComponentIn Kᶜ y₁ := hG.subset_connectedComponentIn hy₁ hGK hy₂
  obtain ⟨l, hlc, hl⟩ := hasLogOn_div_of_same_component hKc.isClosed (hGK hy₁) hcomp
  let f : ℂ → ℂ := fun z => (z - y₂) / (z - y₁)
  have hy₁L : ∀ r, ι r ≠ y₁ := fun r h => by
    have := hℓι r
    rw [h] at this
    linarith
  have hy₂L : ∀ r, ι r ≠ y₂ := fun r h => by
    have := hℓι r
    rw [h] at this
    linarith
  have hfι : HasLogOn (univ : Set ℝ) fun r => f (ι r) := by
    refine hasLogOn_univ_of_ne_zero ?_ fun r => ?_
    · exact (hιc.sub continuous_const).div (hιc.sub continuous_const)
        fun r => sub_ne_zero.mpr (hy₁L r)
    · exact div_ne_zero (sub_ne_zero.mpr (hy₂L r)) (sub_ne_zero.mpr (hy₁L r))
  set I := ι '' Q with hI
  have hIc : IsCompact I := isCompact_Icc.image hιc
  obtain ⟨g, hgc, hg⟩ : HasLogOn I f :=
    hasLogOn_image isCompact_Icc hιc.continuousOn hιi.injOn (hfι.mono (subset_univ _))
  have hPK : ∀ r ∈ P, ι r ∈ K := fun r hr => Or.inr ⟨r, hr, rfl⟩
  have hPI : ∀ r ∈ P, ι r ∈ I := fun r hr => ⟨r, hr.2, rfl⟩
  let n : ℝ → ℂ := fun r => l (ι r) - g (ι r)
  have hnc : ContinuousOn n P := by
    refine ContinuousOn.sub ?_ ?_
    · exact hlc.comp hιc.continuousOn hPK
    · exact hgc.comp hιc.continuousOn hPI
  have hnexp : ∀ r ∈ P, exp (n r) = 1 :=
    fun r hr => exp_sub_eq_one (hl _ (hPK r hr)) (hg _ (hPI r hr))
  have hstart : -N ∈ P := by
    refine ⟨Or.inl fun h => ?_, ⟨le_rfl, by linarith⟩⟩
    have h3 := hRW _ h
    have h4 := hnorm_ge (-N)
    rw [abs_neg, abs_of_pos hNpos] at h4
    linarith
  set n₀ := n (-N) with hn₀
  have hconst : ∀ r ∈ P, n r = n₀ :=
    lineLogDifference_constant J hρ hδρ hsmall hιc hdistι hlip h1 h2 hRF hNpos l g
      hPc hnc hnexp hstart hlc hl hgc hg
  -- The two logarithms paste.
  have hlog : HasLogOn (K ∪ I) f := by
    refine hasLogOn_union (gA := l) (gB := fun z => g z + n₀) hKc.isClosed hIc.isClosed hlc
      (hgc.add continuousOn_const) hl (fun z hz => ?_) ?_
    · rw [exp_add, show exp n₀ = 1 from hnexp _ hstart, mul_one]
      exact hg z hz
    · rintro _ ⟨hzK, r, hrQ, rfl⟩
      have hrP : r ∈ P := by
        refine ⟨?_, hrQ⟩
        rcases hzK with h | ⟨r', hr', he⟩
        · exact Or.inl h.1
        · rw [← hιi he]
          exact hr'.1
      have := hconst r hrP
      simp only [n] at this
      linear_combination this
  have hUc : IsCompact (K ∪ I) := hKc.union hIc
  have hy₁U : y₁ ∉ K ∪ I := by
    rintro (h | ⟨r, -, h⟩)
    · exact hGK hy₁ h
    · exact hy₁L r h
  have hy₂U : y₂ ∉ K ∪ I := by
    rintro (h | ⟨r, -, h⟩)
    · exact hGK hy₂ h
    · exact hy₂L r h
  have heq := component_eq_of_hasLogOn hUc hy₁U hy₂U
    (hlog.inv.congr fun z _ => by simp only [f, inv_div])
  have hin₂ : y₂ ∈ connectedComponentIn (K ∪ I)ᶜ y₁ := heq ▸ mem_connectedComponentIn hy₂U
  have hin₁ : y₁ ∈ connectedComponentIn (K ∪ I)ᶜ y₁ := mem_connectedComponentIn hy₁U
  have hCpre : IsPreconnected (connectedComponentIn (K ∪ I)ᶜ y₁) :=
    isPreconnected_connectedComponentIn
  have hsph : ∀ z, ‖z‖ = R → z ∈ K := fun z hz => Or.inl ⟨fun hzW => (hRW z hzW).ne hz, by
    refine mem_closedBall_zero_iff.mpr ?_
    rw [hz]
    linarith [norm_nonneg (ι 0)]⟩
  have hCball : ∀ z ∈ connectedComponentIn (K ∪ I)ᶜ y₁, ‖z‖ < R := by
    intro z hz
    by_contra hc
    obtain ⟨w, hw1, hw2⟩ := inter_frontier_nonempty_of_isPreconnected (U := ball (0 : ℂ) R) hCpre
      ⟨y₁, hin₁, mem_ball_zero_iff.mpr (hRW _ (hGW hy₁))⟩
      ⟨z, hz, fun h => hc (mem_ball_zero_iff.mp h)⟩
    have hwn : ‖w‖ = R := mem_sphere_zero_iff_norm.mp (frontier_ball_subset_sphere hw2)
    exact connectedComponentIn_subset _ _ hw1 (Or.inl (hsph w hwn))
  obtain ⟨w, hw1, hw2⟩ := inter_frontier_nonempty_of_isPreconnected (U := {z | ℓ z < t}) hCpre
    ⟨y₁, hin₁, show ℓ y₁ < t by linarith⟩ ⟨y₂, hin₂, fun h => by
      have : ℓ y₂ < t := h
      linarith⟩
  have hwt : ℓ w = t := frontier_lt_subset_eq hℓ continuous_const hw2
  obtain ⟨r, rfl⟩ := hline w hwt
  have hrN : |r| ≤ N := by
    have h3 := hCball _ hw1
    have h4 := hnorm_ge r
    linarith
  exact connectedComponentIn_subset _ _ hw1 (Or.inr ⟨r, abs_le.mp hrN, rfl⟩)

end GraphMinor.Surface
