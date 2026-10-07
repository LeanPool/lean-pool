/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.CIVAxisymmetric.Axis.Domain

/-!
# A maximum principle for functions vanishing on the axis

`lem:aniso:axis`: a function `φ(r, z, t)` which is continuous on the closed half-disc
`K = {r ≥ 0, r² + z² ≤ R²} × [t₁, s]`, vanishes on the axis `r = 0`, and satisfies the
parabolic equation `eq:aniso:axis:pde` on the open set `D` obeys
`|φ| ≤ max_Σ |φ| + M (t - t₁)` on `K`, where `Σ` is the parabolic boundary and `M` bounds
the forcing `F`. No bound is assumed on the drift `b_r`, `b_z`, the zeroth-order coefficient
`γ ≥ 0`, or the singular coefficient `k / r`: at an interior maximum point they multiply
first derivatives which vanish.

The proof is the printed one: the perturbation `φ - (M + ε)(t - t₁)` attains its maximum on
the compact set `K`; the maximum point lies neither on `Σ` nor on the axis, so it lies in `D`,
where the first-order spatial derivatives vanish, the second-order ones are nonpositive, and
the left time derivative is nonnegative, contradicting the equation.
-/

public section


open Filter Topology Set

namespace CIV

/-- `∂_r` commutes with negation. -/
theorem dr_neg (φ : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : dr (fun q => -φ q) p = -dr φ p := by
  simp only [dr]
  exact deriv.neg

/-- `∂_z` commutes with negation. -/
theorem dz_neg (φ : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : dz (fun q => -φ q) p = -dz φ p := by
  simp only [dz]
  exact deriv.neg

/-- The one-sided time derivative commutes with negation. -/
theorem dtPast_neg (φ : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) :
    dtPast (fun q => -φ q) p = -dtPast φ p := by
  simp only [dtPast]
  exact derivWithin.neg

/-- At a local maximum of a `C²` function of one real variable, the second derivative is
nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a)
    (hmax : IsLocalMax f a) : deriv (deriv f) a ≤ 0 := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  have hopen : IsOpen (interior u) := isOpen_interior
  have hau : a ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
  have hfu' : ContDiffOn ℝ (1 + 1) f (interior u) := by
    have h2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    rw [h2]
    exact hfu.mono interior_subset
  obtain ⟨hdiff, -, -⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hopen).mp hfu'
  have hd : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x := by
    filter_upwards [hopen.mem_nhds hau] with x hx
    exact hdiff.differentiableAt (hopen.mem_nhds hx)
  have h1 : deriv f a = 0 := hmax.deriv_eq_zero
  by_contra hc
  have hc : 0 < deriv (deriv f) a := not_le.mp hc
  have hsign : ∀ᶠ x in 𝓝[≠] a, SignType.sign (deriv f x) = SignType.sign (x - a) :=
    nhdsWithin_le_nhds (eventually_nhdsWithin_sign_eq_of_deriv_pos hc h1)
  have hpos : ∀ᶠ b in 𝓝[>] a, deriv f b > 0 := deriv_pos_right_of_sign_deriv hsign
  have hmax' : ∀ᶠ x in 𝓝 a, f x ≤ f a := hmax
  obtain ⟨b, hab, hb⟩ := (nhdsGT_basis a).eventually_iff.mp
    (hpos.and (nhdsWithin_le_nhds (hd.and hmax')))
  have hac : a < (a + b) / 2 := by linarith only [hab]
  have hcb : (a + b) / 2 < b := by linarith only [hab]
  have hmono : StrictMonoOn f (Icc a ((a + b) / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a _) ?_ ?_
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with h | hax
      · rw [← h]
        exact hd.self_of_nhds.continuousAt.continuousWithinAt
      · exact (hb ⟨hax, lt_of_le_of_lt hx.2 hcb⟩).2.1.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hb ⟨hx.1, hx.2.trans hcb⟩).1
  have hlt : f a < f ((a + b) / 2) := hmono ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩ hac
  have hle : f ((a + b) / 2) ≤ f a := (hb ⟨hac, hcb⟩).2.2
  exact absurd hlt (not_lt.mpr hle)

/-- The closed half-disc with its time interval is compact. -/
theorem isCompact_axisClosedDomain (R t₁ s : ℝ) (hR : 0 < R) :
    IsCompact (axisClosedDomain R t₁ s) := by
  refine IsCompact.of_isClosed_subset
    (((isCompact_Icc (a := -R) (b := R)).prod (isCompact_Icc (a := -R) (b := R))).prod
      (isCompact_Icc (a := t₁) (b := s))) ?_ ?_
  · have h1 : IsClosed {p : (ℝ × ℝ) × ℝ | 0 ≤ p.1.1} := isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {p : (ℝ × ℝ) × ℝ | p.1.1 ^ 2 + p.1.2 ^ 2 ≤ R ^ 2} :=
      isClosed_le (by fun_prop) continuous_const
    have h3 : IsClosed {p : (ℝ × ℝ) × ℝ | t₁ ≤ p.2} := isClosed_le continuous_const (by fun_prop)
    have h4 : IsClosed {p : (ℝ × ℝ) × ℝ | p.2 ≤ s} := isClosed_le (by fun_prop) continuous_const
    exact h1.inter (h2.inter (h3.inter h4))
  · intro p hp
    obtain ⟨h0, hsq, ht1, hts⟩ := hp
    have hr : p.1.1 ^ 2 ≤ R ^ 2 := by linarith only [hsq, sq_nonneg p.1.2]
    have hz : p.1.2 ^ 2 ≤ R ^ 2 := by linarith only [hsq, sq_nonneg p.1.1]
    obtain ⟨hr1, hr2⟩ := abs_le_of_sq_le_sq' hr hR.le
    obtain ⟨hz1, hz2⟩ := abs_le_of_sq_le_sq' hz hR.le
    exact ⟨⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩, ⟨ht1, hts⟩⟩

/-- The one-sided bound of `lem:aniso:axis`: under its hypotheses, `φ ≤ max_Σ |φ| + M (t - t₁)`
on the closed domain. -/
theorem axisMaximumPrinciple_upper (R t₁ s k M : ℝ) (hR : 0 < R) (hts : t₁ < s) (hM : 0 ≤ M)
    (φ br bz γ F : (ℝ × ℝ) × ℝ → ℝ)
    (hcont : ContinuousOn φ (axisClosedDomain R t₁ s))
    (haxis : ∀ z t : ℝ, |z| ≤ R → t₁ ≤ t → t ≤ s → φ ((0, z), t) = 0)
    (hreg : ∀ p ∈ axisDomain R t₁ s,
      ContDiffAt ℝ 2 (fun y : ℝ × ℝ => φ (y, p.2)) p.1 ∧
        DifferentiableWithinAt ℝ (fun t => φ (p.1, t)) (Set.Iic p.2) p.2)
    (hγ : ∀ p ∈ axisDomain R t₁ s, 0 ≤ γ p)
    (hF : ∀ p ∈ axisDomain R t₁ s, |F p| ≤ M)
    (hpde : ∀ p ∈ axisDomain R t₁ s,
      dtPast φ p + br p * dr φ p + bz p * dz φ p + γ p * φ p =
        dr (dr φ) p + k / p.1.1 * dr φ p + dz (dz φ) p + F p)
    (m : ℝ) (hm : ∀ p ∈ axisParabolicBoundary R t₁ s, |φ p| ≤ m) :
    ∀ p ∈ axisClosedDomain R t₁ s, φ p ≤ m + M * (p.2 - t₁) := by
  -- `m ≥ 0`, since `φ` vanishes at the axis point `((0, 0), t₁) ∈ Σ`.
  have hR2 : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith only [hR]
  have hm0 : 0 ≤ m := by
    have h0 : ((0, 0), t₁) ∈ axisParabolicBoundary R t₁ s := Or.inl ⟨le_rfl, hR2, rfl⟩
    have h1 := hm _ h0
    rw [haxis 0 t₁ (by rw [abs_zero]; exact hR.le) le_rfl hts.le, abs_zero] at h1
    exact h1
  have hK : IsCompact (axisClosedDomain R t₁ s) := isCompact_axisClosedDomain R t₁ s hR
  have hne : (axisClosedDomain R t₁ s).Nonempty :=
    ⟨((0, 0), t₁), le_rfl, hR2, le_rfl, hts.le⟩
  -- The bound with `M + ε` in place of `M`.
  have key : ∀ ε : ℝ, 0 < ε →
      ∀ p ∈ axisClosedDomain R t₁ s, φ p ≤ m + (M + ε) * (p.2 - t₁) := by
    intro ε hε
    obtain ⟨ψ, hψ⟩ : ∃ ψ : (ℝ × ℝ) × ℝ → ℝ, ψ = fun p => φ p - (M + ε) * (p.2 - t₁) := ⟨_, rfl⟩
    have hψc : ContinuousOn ψ (axisClosedDomain R t₁ s) := by
      rw [hψ]
      exact hcont.sub (by fun_prop : Continuous fun p : (ℝ × ℝ) × ℝ =>
        (M + ε) * (p.2 - t₁)).continuousOn
    obtain ⟨p₀, hp₀K, hmax⟩ := hK.exists_isMaxOn hne hψc
    suffices hψm : ψ p₀ ≤ m by
      intro p hp
      have h1 : ψ p ≤ ψ p₀ := hmax hp
      rw [hψ] at h1
      simp only at h1
      have h2 : ψ p₀ = φ p₀ - (M + ε) * (p₀.2 - t₁) := by rw [hψ]
      linarith only [h1, hψm, h2]
    by_contra hlt
    have hlt : m < ψ p₀ := not_le.mp hlt
    obtain ⟨⟨r₀, z₀⟩, t₀⟩ := p₀
    obtain ⟨hr0, hsq, ht1, hts'⟩ := hp₀K
    simp only at hr0 hsq ht1 hts'
    have hMε : 0 ≤ (M + ε) * (t₀ - t₁) :=
      mul_nonneg (by linarith only [hM, hε]) (by linarith only [ht1])
    have hψφ : ψ ((r₀, z₀), t₀) = φ ((r₀, z₀), t₀) - (M + ε) * (t₀ - t₁) := by rw [hψ]
    -- The maximum point is not on the axis.
    have hr : 0 < r₀ := by
      rcases eq_or_lt_of_le hr0 with h | h
      · exfalso
        subst h
        have hz : |z₀| ≤ R := abs_le_of_sq_le_sq (by linarith only [hsq]) hR.le
        have h2 := haxis z₀ t₀ hz ht1 hts'
        linarith only [hlt, hψφ, h2, hMε, hm0]
      · exact h
    -- The maximum point is not on the initial slice.
    have ht : t₁ < t₀ := by
      rcases eq_or_lt_of_le ht1 with h | h
      · exfalso
        have hbd : ((r₀, z₀), t₀) ∈ axisParabolicBoundary R t₁ s := Or.inl ⟨hr0, hsq, h.symm⟩
        have h2 := hm _ hbd
        have h3 := le_abs_self (φ ((r₀, z₀), t₀))
        linarith only [hlt, hψφ, h2, h3, hMε]
      · exact h
    -- The maximum point is not on the lateral boundary.
    have hsq' : r₀ ^ 2 + z₀ ^ 2 < R ^ 2 := by
      rcases eq_or_lt_of_le hsq with h | h
      · exfalso
        have hbd : ((r₀, z₀), t₀) ∈ axisParabolicBoundary R t₁ s := Or.inr ⟨hr0, h, ht1, hts'⟩
        have h2 := hm _ hbd
        have h3 := le_abs_self (φ ((r₀, z₀), t₀))
        linarith only [hlt, hψφ, h2, h3, hMε]
      · exact h
    have hD : ((r₀, z₀), t₀) ∈ axisDomain R t₁ s := ⟨hr, hsq', ht, hts'⟩
    obtain ⟨hC2, hDt⟩ := hreg _ hD
    simp only at hC2 hDt
    -- Nearby points of the time slice lie in the closed domain.
    have hnhr : ∀ᶠ r in 𝓝 r₀, ((r, z₀), t₀) ∈ axisClosedDomain R t₁ s := by
      have h1 : ∀ᶠ r in 𝓝 r₀, 0 < r := eventually_gt_nhds hr
      have h2 : ∀ᶠ r in 𝓝 r₀, r ^ 2 + z₀ ^ 2 < R ^ 2 :=
        (by fun_prop : ContinuousAt (fun r : ℝ => r ^ 2 + z₀ ^ 2) r₀).eventually_lt
          continuousAt_const hsq'
      filter_upwards [h1, h2] with r h1 h2
      exact ⟨h1.le, h2.le, ht1, hts'⟩
    have hnhz : ∀ᶠ z in 𝓝 z₀, ((r₀, z), t₀) ∈ axisClosedDomain R t₁ s := by
      have h2 : ∀ᶠ z in 𝓝 z₀, r₀ ^ 2 + z ^ 2 < R ^ 2 :=
        (by fun_prop : ContinuousAt (fun z : ℝ => r₀ ^ 2 + z ^ 2) z₀).eventually_lt
          continuousAt_const hsq'
      filter_upwards [h2] with z h2
      exact ⟨hr0, h2.le, ht1, hts'⟩
    -- The spatial slices have a local maximum at `(r₀, z₀)`.
    have hmaxr : IsLocalMax (fun r => φ ((r, z₀), t₀)) r₀ := by
      refine hnhr.mono fun r hrK => ?_
      have h1 : ψ ((r, z₀), t₀) ≤ ψ ((r₀, z₀), t₀) := hmax hrK
      rw [hψ] at h1
      simp only at h1 ⊢
      linarith only [h1]
    have hmaxz : IsLocalMax (fun z => φ ((r₀, z), t₀)) z₀ := by
      refine hnhz.mono fun z hzK => ?_
      have h1 : ψ ((r₀, z), t₀) ≤ ψ ((r₀, z₀), t₀) := hmax hzK
      rw [hψ] at h1
      simp only at h1 ⊢
      linarith only [h1]
    have hdr : dr φ ((r₀, z₀), t₀) = 0 := hmaxr.deriv_eq_zero
    have hdz : dz φ ((r₀, z₀), t₀) = 0 := hmaxz.deriv_eq_zero
    have hfr : ContDiffAt ℝ 2 (fun r => φ ((r, z₀), t₀)) r₀ :=
      ContDiffAt.comp (g := fun y : ℝ × ℝ => φ (y, t₀)) (f := fun r : ℝ => (r, z₀)) r₀ hC2
        (contDiff_id.prodMk contDiff_const).contDiffAt
    have hfz : ContDiffAt ℝ 2 (fun z => φ ((r₀, z), t₀)) z₀ :=
      ContDiffAt.comp (g := fun y : ℝ × ℝ => φ (y, t₀)) (f := fun z : ℝ => (r₀, z)) z₀ hC2
        (contDiff_const.prodMk contDiff_id).contDiffAt
    have hdrr : dr (dr φ) ((r₀, z₀), t₀) ≤ 0 := deriv_deriv_nonpos_of_isLocalMax hfr hmaxr
    have hdzz : dz (dz φ) ((r₀, z₀), t₀) ≤ 0 := deriv_deriv_nonpos_of_isLocalMax hfz hmaxz
    -- The left time derivative of the perturbation is nonnegative.
    have hnht : ∀ᶠ t in 𝓝[Iic t₀] t₀, ((r₀, z₀), t) ∈ axisClosedDomain R t₁ s := by
      have h1 : ∀ᶠ t in 𝓝 t₀, t₁ < t := eventually_gt_nhds ht
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t h1 h2
      exact ⟨hr0, hsq, h1.le, le_trans h2 hts'⟩
    have hmaxt : IsLocalMaxOn (fun t => ψ ((r₀, z₀), t)) (Iic t₀) t₀ :=
      hnht.mono fun t htK => hmax htK
    have hderφ : HasDerivWithinAt (fun t => φ ((r₀, z₀), t)) (dtPast φ ((r₀, z₀), t₀))
        (Iic t₀) t₀ := hDt.hasDerivWithinAt
    have hderlin : HasDerivWithinAt (fun t => (M + ε) * (t - t₁)) ((M + ε) * 1) (Iic t₀) t₀ :=
      ((hasDerivAt_id t₀).sub_const t₁ |>.const_mul (M + ε)).hasDerivWithinAt
    have hderψ : HasDerivWithinAt (fun t => ψ ((r₀, z₀), t))
        (dtPast φ ((r₀, z₀), t₀) - (M + ε) * 1) (Iic t₀) t₀ := by
      rw [hψ]
      exact hderφ.sub hderlin
    have hneg1 : (-1 : ℝ) ∈ posTangentConeAt (Iic t₀) t₀ := by
      apply mem_posTangentConeAt_of_segment_subset
      exact (convex_Iic t₀).segment_subset (mem_Iic.2 le_rfl) (mem_Iic.2 (by linarith only))
    have hnonneg := hmaxt.hasFDerivWithinAt_nonpos hderψ.hasFDerivWithinAt hneg1
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, neg_one_mul,
      neg_nonpos] at hnonneg
    -- The equation at the maximum point.
    have hφpos : 0 ≤ φ ((r₀, z₀), t₀) := by linarith only [hlt, hψφ, hMε, hm0]
    have hγφ : 0 ≤ γ ((r₀, z₀), t₀) * φ ((r₀, z₀), t₀) := mul_nonneg (hγ _ hD) hφpos
    have hFle : F ((r₀, z₀), t₀) ≤ M := (abs_le.mp (hF _ hD)).2
    have hpde' := hpde _ hD
    rw [hdr, hdz, mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero] at hpde'
    linarith only [hpde', hnonneg, hγφ, hFle, hdrr, hdzz, hε]
  -- Let `ε → 0`.
  intro p hp
  have hpt : p.2 - t₁ ≤ s - t₁ := by linarith only [hp.2.2.2]
  have hst : 0 < s - t₁ := by linarith only [hts]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (s - t₁) := div_pos hε hst
  have h1 := key (ε / (s - t₁)) hδ p hp
  have h2 : ε / (s - t₁) * (p.2 - t₁) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hst]
    exact mul_le_mul_of_nonneg_left hpt hε.le
  linarith only [h1, h2]

/-- `lem:aniso:axis`, the maximum principle for functions vanishing on the axis: if `φ` is
continuous on the closed half-disc `K = {r ≥ 0, r² + z² ≤ R²} × [t₁, s]`, vanishes on the axis
`r = 0`, is `C²` in `(r, z)` and differentiable from the past in `t` on `D`, and satisfies
`eq:aniso:axis:pde` on `D` with `γ ≥ 0` and `|F| ≤ M`, then `|φ| ≤ max_Σ |φ| + M (t - t₁)`
on `K` (`eq:aniso:axis:bound`). The maximum over the parabolic boundary `Σ` enters as any
bound `m` for `|φ|` on `Σ`. -/
theorem axisMaximumPrinciple_of_profile (R t₁ s k M : ℝ) (hR : 0 < R) (hts : t₁ < s) (hM : 0 ≤ M)
    (φ br bz γ F : (ℝ × ℝ) × ℝ → ℝ)
    (hcont : ContinuousOn φ (axisClosedDomain R t₁ s))
    (haxis : ∀ z t : ℝ, |z| ≤ R → t₁ ≤ t → t ≤ s → φ ((0, z), t) = 0)
    (hreg : ∀ p ∈ axisDomain R t₁ s,
      ContDiffAt ℝ 2 (fun y : ℝ × ℝ => φ (y, p.2)) p.1 ∧
        DifferentiableWithinAt ℝ (fun t => φ (p.1, t)) (Set.Iic p.2) p.2)
    (hγ : ∀ p ∈ axisDomain R t₁ s, 0 ≤ γ p)
    (hF : ∀ p ∈ axisDomain R t₁ s, |F p| ≤ M)
    (hpde : ∀ p ∈ axisDomain R t₁ s,
      dtPast φ p + br p * dr φ p + bz p * dz φ p + γ p * φ p =
        dr (dr φ) p + k / p.1.1 * dr φ p + dz (dz φ) p + F p) :
    ∀ m : ℝ, (∀ p ∈ axisParabolicBoundary R t₁ s, |φ p| ≤ m) →
      ∀ p ∈ axisClosedDomain R t₁ s, |φ p| ≤ m + M * (p.2 - t₁) := by
  intro m hm p hp
  have hup := axisMaximumPrinciple_upper R t₁ s k M hR hts hM φ br bz γ F hcont haxis hreg hγ hF
    hpde m hm p hp
  have hdr' : dr (fun q => -φ q) = fun q => -dr φ q := funext (dr_neg φ)
  have hdz' : dz (fun q => -φ q) = fun q => -dz φ q := funext (dz_neg φ)
  have hlow := axisMaximumPrinciple_upper R t₁ s k M hR hts hM (fun q => -φ q) br bz γ
    (fun q => -F q) hcont.neg
    (fun z t hz h1 h2 => by rw [haxis z t hz h1 h2, neg_zero])
    (fun q hq => ⟨ContDiffAt.neg (hreg q hq).1, (hreg q hq).2.neg⟩) hγ
    (fun q hq => by rw [abs_neg]; exact hF q hq)
    (fun q hq => by
      rw [dtPast_neg, hdr', hdz', dr_neg, dz_neg]
      simp only
      linarith only [hpde q hq])
    m (fun q hq => by rw [abs_neg]; exact hm q hq) p hp
  rw [abs_le]
  constructor <;> linarith only [hup, hlow]

end CIV
