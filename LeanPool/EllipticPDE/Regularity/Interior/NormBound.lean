/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Interior.EnergyBound


/-!
# Uniform interior difference-quotient norm bound

The master energy bound of `EllipticPdes.Regularity.Interior.EnergyBound` is run along a
cutoff tower to produce a bound
on `‖Dₖ^h (ζ ∂ᵢu)‖` that is uniform in the step `h`, which is the hypothesis the weak-limit
converse consumes to produce the second weak derivative.

## Main declarations

* `interior_diffQuot_norm_bound`: the `h`-uniform bound on the difference quotient of the
  cut-off first derivatives.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Uniform difference-quotient norm bound for the limit passage -/

/-- **One-neighbourhood shift margin.** If the cutoff `η` is `≡ 1` on a neighbourhood of a
compact set `K`, then there is a positive margin `δ` such that `η` is locally constant `≡ 1`
near every point within `δ` of `K`. This localises the tower cutoffs: shifting a support point
of one cutoff by less than the margin lands where the next cutoff is identically `1` (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma exists_one_margin {η : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hη : ∀ᶠ x in nhdsSet K, η x = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      (∃ p ∈ K, dist x p < δ) → η =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
  obtain ⟨U, hUopen, hKU, hUsub⟩ := mem_nhdsSet_iff_exists.mp hη
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hUopen hKU
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hxU : x ∈ U :=
    hδ (Metric.thickening_subset_cthickening δ K (Metric.mem_thickening_iff.mpr hx))
  exact Filter.eventually_of_mem (hUopen.mem_nhds hxU) (fun y hy => hUsub hy)

private lemma norm_diffQuot_le_of_large_step (k : Fin d) (h : ℝ) (g : EucL2 d)
    {δ : ℝ} (hδ : 0 < δ) (hlarge : δ ≤ |h|) : ‖diffQuot k h g‖ ≤ 2 * ‖g‖ / δ := by
  have habs : 0 < |h| := hδ.trans_le hlarge
  have hval : diffQuot k h g = h⁻¹ • (transL2 (hshift k h) g - g) := by
    simp only [diffQuot, _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap]
  have hti : ‖transL2 (hshift k h) g - g‖ ≤ 2 * ‖g‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [(transL2 (hshift k h)).norm_map]
    linarith
  rw [hval, norm_smul, Real.norm_eq_abs, abs_inv]
  calc |h|⁻¹ * ‖transL2 (hshift k h) g - g‖ ≤ |h|⁻¹ * (2 * ‖g‖) :=
        mul_le_mul_of_nonneg_left hti (by positivity)
    _ ≤ δ⁻¹ * (2 * ‖g‖) :=
        mul_le_mul_of_nonneg_right ((inv_le_inv₀ habs hδ).mpr hlarge) (by positivity)
    _ = 2 * ‖g‖ / δ := by rw [div_eq_inv_mul]

/-- **Uniform bound on the difference quotient of a test function.** A test function has a
globally bounded gradient (continuous with compact support), so its difference quotient is
uniformly bounded, independently of the step `h` and direction `k`, by the segment mean-value
inequality (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma exists_abs_diffQuot_bound {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (k : Fin d) (h : ℝ), h ≠ 0 → ∀ x,
      |(η (x + hshift k h) - η x) / h| ≤ L := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖fderiv ℝ η x‖ ≤ C := by
    have hcont : Continuous (fun x => fderiv ℝ η x) := hη.1.continuous_fderiv (by simp)
    have hcs : HasCompactSupport (fun x => fderiv ℝ η x) := hη.2.1.fderiv (𝕜 := ℝ)
    exact hcont.bounded_above_of_compact_support hcs
  refine ⟨max C 0, le_max_right _ _, fun k h hh x => ?_⟩
  have hMVT : ‖η (x + hshift k h) - η x‖ ≤ C * ‖(x + hshift k h) - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := η) (s := Set.univ) (C := C)
      (fun y _ => (hη.1.differentiable (by simp)) y) (fun y _ => hC y)
      convex_univ (Set.mem_univ x) (Set.mem_univ (x + hshift k h))
  have hnorm : ‖(x + hshift k h) - x‖ = |h| := by
    rw [show (x + hshift k h) - x = hshift k h from by abel, hshift, norm_smul]; simp
  rw [hnorm] at hMVT
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  calc |η (x + hshift k h) - η x| = ‖η (x + hshift k h) - η x‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * |h| := hMVT
    _ ≤ max C 0 * |h| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)


private theorem shift_support_subset_of_tower {V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) (k : Fin d) (h : ℝ) (hm : |h| < T.margin) {g : EucL2 d}
    (hg : ∀ᵐ x ∂volume, g x ≠ 0 → x ∈ tsupport T.ζ) :
    ∀ᵐ x ∂volume, g (x + hshift k h) ≠ 0 → x ∈ Ω := by
  have htζξ : tsupport T.ζ ⊆ tsupport T.ξ := fun x hx =>
    subset_tsupport T.ξ (by rw [Function.mem_support, T.xi_eqOn_one hx]; exact one_ne_zero)
  have htξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  have hshift_support : ∀ᵐ x ∂volume, g (x + hshift k h) ≠ 0 → x + hshift k h ∈ tsupport T.ζ :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving.ae hg
  filter_upwards [hshift_support] with x hx hne
  have hmemθ := htξθ (htζξ (hx hne))
  have hmem := T.hmargin k (-h) (by rw [abs_neg]; exact hm) (x + hshift k h) hmemθ
  rwa [show x + hshift k h + hshift k (-h) = x from by rw [hshift_neg]; abel] at hmem

private theorem div_mul_cancel_factor (a b δ : ℝ) (hδ : δ ≠ 0) :
    a / δ * b * δ = a * b := by
  field_simp

private theorem dist_hshift (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) (h : ℝ) :
    dist x (x + hshift k h) = |h| := by
  rw [dist_eq_norm, show x - (x + hshift k h) = -hshift k h from by abel, norm_neg]
  simp [hshift, norm_smul]

private theorem norm_le_sqrt_coefficient_sum {E : Type*} [NormedAddCommGroup E]
    {w : E} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ‖w‖ ^ 2 ≤ c * (a ^ 2 + b ^ 2)) : ‖w‖ ≤ Real.sqrt c * (a + b) := by
  have hstep : ‖w‖ ≤ Real.sqrt (c * (a ^ 2 + b ^ 2)) := by
    rw [show ‖w‖ = Real.sqrt (‖w‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt h
  refine hstep.trans ?_
  rw [Real.sqrt_mul hc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith only [ha, hb]
    _ = a + b := Real.sqrt_sq (add_nonneg ha hb)

/-- **Uniform difference-quotient norm bound (Evans §5.8.2 / §6.3.1).** For a cutoff tower `T`
and each `(k, i)`, there is a constant `Cd` such that every weak solution `u` of
`L u = f` has the whole-space difference quotient of the extension of `ζ · ∂ᵢu` bounded in `L²`
by `M`, uniformly over all steps `h ≠ 0`, with `M ≤ Cd (‖f‖ + ‖u₀‖)`. The step-uniform bound
`M` depends on `u` and `f`; `Cd` is quantified before both, so it depends only on
`λ, Λ, A₁, d, γ, ‖b‖∞, ‖c‖∞` and the tower. For small `h` the discrete
Leibniz split localises the difference quotient onto the master energy bound
(`interior_diffQuot_energy_bound`) and the first-order energy; for large `h` the crude
operator bound `‖Dₖʰ g‖ ≤ 2‖g‖/|h|` closes it. This uniform bound is exactly the hypothesis of
the weak-limit converse `weakDeriv_of_diffQuot_bounded`. -/
theorem interior_diffQuot_norm_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V) (k i : Fin d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ M : ℝ, 0 ≤ M
        ∧ (∀ h : ℝ, h ≠ 0 →
            ‖diffQuot k h (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ)))‖ ≤ M)
        ∧ M ≤ Cd * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  classical
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  have hγnn : (0 : ℝ) ≤ Op.gardingγ := Op.gardingγ_nonneg
  -- Sup bound of `ζ` and its difference quotient.
  let Mζ: ℝ := (exists_abs_bound T.hζ).choose
  have hMζdef : Mζ = (exists_abs_bound T.hζ).choose := rfl
  have hMζbd : ∀ z, |T.ζ z| ≤ Mζ := (exists_abs_bound T.hζ).choose_spec
  have hMζ0 : (0 : ℝ) ≤ Mζ := le_trans (abs_nonneg _) (hMζbd 0)
  obtain ⟨L, hL0, hLbd⟩ := exists_abs_diffQuot_bound T.hζ
  -- Tower support inclusions.
  have htξ2ξ : tsupport (fun y => T.ξ y * T.ξ y) ⊆ tsupport T.ξ := tsupport_mul_subset_left
  have htζξ : tsupport T.ζ ⊆ tsupport T.ξ := fun x hx =>
    subset_tsupport T.ξ (by rw [Function.mem_support, T.xi_eqOn_one hx]; exact one_ne_zero)
  have htξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  -- The two localisation margins from the tower cutoff nesting.
  obtain ⟨δξ, hδξ, hξ1⟩ := exists_one_margin T.hζ.2.1 T.hξ_one
  obtain ⟨δθ, hδθ, hθ1m⟩ := exists_one_margin T.hξ.2.1 T.hθ_one
  let δ₀: ℝ := min T.margin (min δξ δθ)
  have hδ₀def : δ₀ = min T.margin (min δξ δθ) := rfl
  have hδ₀pos : (0 : ℝ) < δ₀ := by
    rw [hδ₀def]; exact lt_min T.hmargin_pos (lt_min hδξ hδθ)
  have hδ₀m : δ₀ ≤ T.margin := min_le_left _ _
  have hδ₀ξ : δ₀ ≤ δξ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀θ : δ₀ ≤ δθ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- The master energy constant, uniform in `h`.
  obtain ⟨CD2, hCD20, hD2⟩ :=
    interior_diffQuot_energy_bound Op hΩm hA T.hξ T.hθ k
  -- The two data coefficients: the first-order gradient coefficient `√((1 + 4γ)/(2λ))`, and
  -- the `h`-uniform energy coefficient `√(2 CD2 / λ)`.
  let dcoef: ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam))
  have hdcoefdef : dcoef = Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) := rfl
  have hrad : (0 : ℝ) ≤ (1 + 4 * Op.gardingγ) / (2 * Op.lam) := by positivity
  have hdcoef0 : (0 : ℝ) ≤ dcoef := Real.sqrt_nonneg _
  let CD2coef: ℝ := Real.sqrt (2 * CD2 / Op.lam)
  have hCD2coefdef : CD2coef = Real.sqrt (2 * CD2 / Op.lam) := rfl
  have hCD2coef0 : (0 : ℝ) ≤ CD2coef := Real.sqrt_nonneg _
  refine ⟨max (Mζ * CD2coef + L * dcoef) (2 * Mζ * dcoef / δ₀),
    le_max_of_le_left (add_nonneg (mul_nonneg hMζ0 hCD2coef0) (mul_nonneg hL0 hdcoef0)), ?_⟩
  intro u f hu
  let di: L2D Ω := (u : H1amb Ω) i.succ
  have hdidef : di = (u : H1amb Ω) i.succ := rfl
  let gζ: L2D Ω := mulTest T.hζ di
  have hgζdef : gζ = mulTest T.hζ di := rfl
  let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
  have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  have hdi : ‖di‖ ≤ dcoef * P := firstOrder_gradNorm_le Op u f hu i
  -- The bound value, in the two step regimes.
  let Msm: ℝ := Mζ * (CD2coef * P) + L * ‖di‖
  have hMsmdef : Msm = Mζ * (CD2coef * P) + L * ‖di‖ := rfl
  let Mlg: ℝ := 2 * (Mζ * ‖di‖) / δ₀
  have hMlgdef : Mlg = 2 * (Mζ * ‖di‖) / δ₀ := rfl
  have hMsm0 : (0 : ℝ) ≤ Msm := by
    rw [hMsmdef]
    exact add_nonneg (mul_nonneg hMζ0 (mul_nonneg hCD2coef0 hP0))
      (mul_nonneg hL0 (norm_nonneg _))
  refine ⟨max Msm Mlg, le_max_of_le_left hMsm0, ?_, ?_⟩
  · -- The uniform `∀ h` bound.
    intro h hh
    by_cases hsmall : |h| < δ₀
    · -- Small `h`: discrete Leibniz split localised onto the master estimate.
      refine le_trans ?_ (le_max_left _ _)
      -- The four `h`-smallness conditions for the master estimate.
      have hm : |h| < T.margin := lt_of_lt_of_le hsmall hδ₀m
      have hdistshift : ∀ x : EuclideanSpace ℝ (Fin d),
          dist x (x + hshift k (-h)) = |h| := fun x => by
        simpa only [abs_neg] using dist_hshift x k (-h)
      have hev_of : ∀ x, (∃ p ∈ tsupport (fun y => T.ξ y * T.ξ y), dist x p < δθ) →
          T.θ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
        rintro x ⟨p, hp, hdp⟩
        exact hθ1m x ⟨p, htξ2ξ hp, hdp⟩
      have hev_case : ∀ x,
          x ∈ tsupport (fun y => T.ξ y * T.ξ y)
              ∨ x + hshift k (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) →
            T.θ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
        intro x hcase
        rcases hcase with h1 | h2
        · exact hev_of x ⟨x, h1, by rw [dist_self]; exact hδθ⟩
        · exact hev_of x ⟨x + hshift k (-h), h2, by
            rw [hdistshift]; exact lt_of_lt_of_le hsmall hδ₀θ⟩
      have hsm_in : ∀ x ∈ tsupport (fun y => T.ξ y * T.ξ y), x + hshift k h ∈ Ω :=
        fun x hx => T.hmargin k h hm x (htξθ (htξ2ξ hx))
      have hsm_out : ∀ x ∈ tsupport T.θ, x + hshift k (-h) ∈ Ω :=
        fun x hx => T.hmargin k (-h) (by rw [abs_neg]; exact hm) x hx
      have hθ1 : ∀ x ∈ Ω,
          x ∈ tsupport (fun y => T.ξ y * T.ξ y)
              ∨ x + hshift k (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) → T.θ x = 1 := by
        intro x _ hcase
        simpa using (hev_case x hcase).eq_of_nhds
      have hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
          x ∈ tsupport (fun y => T.ξ y * T.ξ y)
              ∨ x + hshift k (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) → partialD j T.θ x = 0 := by
        intro j x _ hcase
        rw [partialD, (hev_case x hcase).fderiv_eq]
        simp
      -- The master energy bound for this `h`, specialised to index `i`.
      have hBsq : ‖mulTest T.hξ (diffQuotD k h hΩm di)‖ ^ 2
          ≤ 2 * CD2 / Op.lam * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
        have hmaster := hD2 u f hu h hh hsm_in hsm_out hθ1 hθ0
        have hsingle : ‖extendL2 hΩm (mulTest T.hξ (diffQuotD k h hΩm di))‖ ^ 2
            ≤ ∑ i : Fin d,
              ‖extendL2 hΩm (mulTest T.hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2 := by
          rw [hdidef]
          exact single_le_sum_fin
            (fun i => ‖extendL2 hΩm (mulTest T.hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2)
            (fun i => sq_nonneg _) i
        rw [norm_extendL2] at hsingle
        rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
        nlinarith only [hmaster, hsingle, hlam.le]
      have hB : ‖mulTest T.hξ (diffQuotD k h hΩm di)‖ ≤ CD2coef * P :=
        norm_le_sqrt_coefficient_sum (norm_nonneg f) (norm_nonneg _) (by positivity) hBsq
      -- Support facts for the difference-quotient identity.
      have hζsupp : ∀ᵐ x ∂volume,
          (extendL2 hΩm gζ : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ tsupport T.ζ :=
        extendL2_supp_of_ae_restrict hΩm gζ (mulTest_ae_eq_zero_off_tsupport T.hζ di)
      have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
        (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
      -- `extendL2 (ζ · di) = ζ · extendL2 di` a.e., and its shift.
      have hζext : (extendL2 hΩm gζ : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume] fun y => T.ζ y * (extendL2 hΩm di : EuclideanSpace ℝ (Fin d) → ℝ) y := by
        have hg : ∀ᵐ x ∂volume, x ∈ Ω → (gζ x : ℝ) = T.ζ x * (di x : ℝ) :=
          (ae_restrict_iff' hΩm).mp (mulTest_coeFn T.hζ di)
        filter_upwards [coeFn_extendL2 hΩm gζ, coeFn_extendL2 hΩm di, hg] with y hy1 hy2 himp
        rw [hy1, hy2]
        by_cases hyΩ : y ∈ Ω
        · rw [Set.indicator_of_mem hyΩ, Set.indicator_of_mem hyΩ]; exact himp hyΩ
        · rw [Set.indicator_of_notMem hyΩ, Set.indicator_of_notMem hyΩ, mul_zero]
      have hζext_shift : (fun x => (extendL2 hΩm gζ : EuclideanSpace ℝ (Fin d) → ℝ)
              (x + hshift k h))
          =ᵐ[volume] fun x => T.ζ (x + hshift k h)
              * (extendL2 hΩm di : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) :=
        hqmp.ae_eq_comp hζext
      -- The localisation `ζ(x + h eₖ) = 0 ∨ ξ x = 1`.
      have hloc : ∀ x, T.ζ (x + hshift k h) = 0 ∨ T.ξ x = 1 := by
        intro x
        by_cases hz : T.ζ (x + hshift k h) = 0
        · exact Or.inl hz
        · refine Or.inr ?_
          have hmem : x + hshift k h ∈ tsupport T.ζ :=
            subset_tsupport _ (Function.mem_support.mpr hz)
          have hdx : dist x (x + hshift k h) < δξ := by
            have hdeq : dist x (x + hshift k h) = |h| := by
              exact dist_hshift x k h
            rw [hdeq]; exact lt_of_lt_of_le hsmall hδ₀ξ
          simpa using (hξ1 x ⟨x + hshift k h, hmem, hdx⟩).eq_of_nhds
      -- The multiplier maps.
      have hm1meas : Measurable (fun y => T.ζ (y + hshift k h)) :=
        (T.hζ.continuous.comp (continuous_id.add continuous_const)).measurable
      have hm1bd : ∀ᵐ x ∂(volume.restrict Ω), |T.ζ (x + hshift k h)| ≤ Mζ :=
        ae_of_all _ (fun x => hMζbd (x + hshift k h))
      have hm2meas : Measurable (fun y => (T.ζ (y + hshift k h) - T.ζ y) / h) :=
        (((T.hζ.continuous.comp (continuous_id.add continuous_const)).sub
          T.hζ.continuous).div_const h).measurable
      have hm2bd : ∀ᵐ x ∂(volume.restrict Ω),
          |(T.ζ (x + hshift k h) - T.ζ x) / h| ≤ L :=
        ae_of_all _ (fun x => hLbd k h hh x)
      -- The discrete Leibniz identity, restricted-domain.
      have hLeibniz : diffQuotD k h hΩm gζ
          = mulCoeffL hm1meas hm1bd (mulTest T.hξ (diffQuotD k h hΩm di))
            + mulCoeffL hm2meas hm2bd di := by
        apply Lp.ext
        filter_upwards [coeFn_diffQuotD k h hΩm gζ,
          Lp.coeFn_add (mulCoeffL hm1meas hm1bd (mulTest T.hξ (diffQuotD k h hΩm di)))
            (mulCoeffL hm2meas hm2bd di),
          mulCoeffL_coeFn hm1meas hm1bd (mulTest T.hξ (diffQuotD k h hΩm di)),
          mulTest_coeFn T.hξ (diffQuotD k h hΩm di),
          mulCoeffL_coeFn hm2meas hm2bd di, coeFn_diffQuotD k h hΩm di,
          ae_restrict_of_ae hζext_shift, mulTest_coeFn T.hζ di]
          with x hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
        rw [hx1, hx7, hx8, hx2, Pi.add_apply, hx3, hx4, hx5, hx6]
        rcases hloc x with hz | hone
        · rw [hz]; field_simp; ring
        · rw [hone]; field_simp; ring
      have hnormLeib : ‖diffQuotD k h hΩm gζ‖ ≤ Msm := by
        rw [hLeibniz, hMsmdef]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · refine le_trans (norm_mulCoeffL_le hm1meas hm1bd _) ?_
          exact mul_le_mul_of_nonneg_left hB hMζ0
        · exact norm_mulCoeffL_le hm2meas hm2bd di
      -- Transfer the whole-space difference quotient via `extendL2_diffQuotD_eq`.
      have hsuppcond := shift_support_subset_of_tower T k h hm hζsupp
      rw [show ‖diffQuot k h (extendL2 hΩm gζ)‖ = ‖diffQuotD k h hΩm gζ‖ from by
        rw [← extendL2_diffQuotD_eq k h hΩm gζ hsuppcond, norm_extendL2]]
      exact hnormLeib
    · -- Large `h`: the translation operator bound is enough.
      refine le_trans ?_ (le_max_right _ _)
      have hgζbd : ‖extendL2 hΩm gζ‖ ≤ Mζ * ‖di‖ := by
        rw [norm_extendL2, hgζdef]
        exact norm_mulTest_le T.hζ di
      exact (norm_diffQuot_le_of_large_step k h _ hδ₀pos (not_lt.mp hsmall)).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgζbd (by norm_num)) hδ₀pos.le)
  · -- The data bound `M ≤ Cd · P`, against the constant fixed before `u` and `f`.
    apply max_le
    · -- The small-step regime.
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0)
      rw [hMsmdef]
      have h1 : L * ‖di‖ ≤ L * (dcoef * P) := mul_le_mul_of_nonneg_left hdi hL0
      nlinarith only [h1]
    · -- The large-step regime.
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hP0)
      rw [hMlgdef, div_le_iff₀ hδ₀pos]
      have hcancel : 2 * Mζ * dcoef / δ₀ * P * δ₀ = 2 * Mζ * dcoef * P :=
        div_mul_cancel_factor _ _ _ hδ₀pos.ne'
      rw [hcancel]
      have h1 : 2 * (Mζ * ‖di‖) ≤ 2 * (Mζ * (dcoef * P)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdi hMζ0) (by norm_num)
      nlinarith only [h1]

end EllipticPdes.Regularity
