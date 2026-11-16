/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardLocality

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in `JumpDiffusion.is_solution`, so that a
solution can be re-read with any proof of them. Two solutions on a common window and a common
filtration agree, by the Bielecki contraction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

/-- A process with a finite `S²` norm on every window has finite time-integrated `L²` energy. -/
theorem lintegral_lintegral_sq_lt_top_of_supL2 {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  rcases le_or_gt b 0 with hb | hb
  · have hvol : (volume (Set.Icc (0 : ℝ) b)) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (by linarith : b - 0 ≤ 0)
    have : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume = 0 := by
      intro ω
      exact setLIntegral_measure_zero _ _ hvol
    simp [this]
  · set F : Ω → ℝ≥0∞ :=
      fun ω => ⨆ t : Set.Icc (0 : ℝ) b, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2 with hF
    have hle : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
          ≤ ∫⁻ ω, F ω * ENNReal.ofReal b ∂P := by
      refine lintegral_mono fun ω => ?_
      have hpt : ∫⁻ s in Set.Icc (0 : ℝ) b,
          ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
            ≤ ∫⁻ _ in Set.Icc (0 : ℝ) b, F ω ∂volume := by
        refine setLIntegral_mono_ae ?_ ?_
        · exact measurable_const.aemeasurable
        · refine Filter.Eventually.of_forall fun s hs => ?_
          exact le_iSup (fun t : Set.Icc (0 : ℝ) b =>
            ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨s, hs⟩
      refine hpt.trans ?_
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top (hS b hb) (ENNReal.ofReal_lt_top)

/-! ### Auxiliary Bielecki facts -/

omit [MeasurableSpace E] in
/-- Two path maps agreeing a.s. at every time of the window have equal Bielecki norms. -/
theorem bieleckiNorm_congr_ae_on (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t ht] with ω hω
    rw [hω]
  rw [hinner]

omit [MeasurableSpace E] in
/-- A finite `S²` norm gives a finite Bielecki norm at weight `0`. -/
theorem bieleckiNorm_lt_top_of_supL2 {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T Z < ⊤ := by
  set M := ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P with hM
  have hMfin : M < ⊤ := hS T hT
  unfold bieleckiNorm
  have hMhalf : M ^ ((1 : ℝ) / 2) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne
  refine lt_of_le_of_lt ?_ hMhalf
  refine iSup_le fun t => iSup_le fun ht => ?_
  have hslice : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ≤ M := by
    refine lintegral_mono fun ω => ?_
    exact le_iSup (fun u : Set.Icc (0 : ℝ) T =>
      ∑ i, (‖Z (u : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨t, ht⟩
  calc ENNReal.ofReal (Real.exp (-(0 : ℝ) * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
        simp
    _ ≤ M ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hslice (by norm_num)

omit [MeasurableSpace E] in
/-- The Bielecki norm of a difference of two path maps of finite norm is finite. -/
theorem bieleckiNorm_sub_lt_top_of_lt_top {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hX : bieleckiNorm (P := P) 0 T X < ⊤) (hY : bieleckiNorm (P := P) 0 T Y < ⊤) :
    bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y t ω))
      = bieleckiNorm (P := P) 0 T Y := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X t ω i - Y t ω i)
      = fun t (ω : Ω) => X t ω + (fun i => -(Y t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y t ω)) :=
    measurable_neg.comp hYm
  have hadd := bieleckiNorm_add_le (P := P) 0 T X (fun t ω => -(Y t ω))
    (fun t => bieleckiNorm_inner_aemeasurable _ hXm t)
    (fun t => bieleckiNorm_inner_aemeasurable (fun t ω => -(Y t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨hX, hY⟩

/-- A finite extended real dominated by a strict multiple of itself vanishes. -/
theorem eq_zero_of_le_mul_self {a q : ℝ≥0∞} (ha : a ≠ ⊤) (hq : q < 1) (h : a ≤ q * a) :
    a = 0 := by
  by_contra h0
  have hlt : a * q < a * 1 := ENNReal.mul_lt_mul_right h0 ha hq
  rw [mul_one] at hlt
  rw [mul_comm q a] at h
  exact absurd h (not_le.mpr hlt)

/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

/-- `X` satisfies the jump-diffusion integral equation, relative to `ℱ`, at every time of
`[0, T]`. The integrand hypotheses that make the two stochastic integrals well-typed are
bundled existentially, as in `JumpDiffusion.is_solution`. -/
structure SolvesOn (X : ℝ → Ω → (Fin n → ℝ)) (T : ℝ) : Prop where
  /-- Joint measurability of the diffusion integrand along `X`. -/
  h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j)
  /-- Progressive measurability of the diffusion integrand along `X`. -/
  h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j
  /-- `L²` boundedness of the diffusion integrand on every finite horizon. -/
  h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- Joint measurability of the jump integrand along `X`. -/
  h_γ_meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i
  /-- Marked progressive measurability of the jump integrand along `X`. -/
  h_γ_progMeas : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i
  /-- `L²` boundedness of the jump integrand on every finite horizon. -/
  h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The integral equation at every time of the window. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
    X t ω i = picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i

/-- A solution on a window is a solution on every shorter window. -/
theorem SolvesOn.mono {X : ℝ → Ω → (Fin n → ℝ)} {T T' : ℝ} (hTT : T' ≤ T)
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T' := by
  obtain ⟨a, b, c, e, f, g, heq⟩ := h
  exact ⟨a, b, c, e, f, g, fun t ht => heq t ⟨ht.1, ht.2.trans hTT⟩⟩

/-- **Uniqueness on a window.** Two solutions of the equation on `[0, T]` relative to the same
filtration, each with a finite `S²` norm, agree almost surely at every time of the window. -/
theorem ae_eq_of_solvesOn
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hX : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (hY : SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i := by
  obtain ⟨hσmX, hσpX, hσsX, hγmX, hγpX, hγsX, heqX⟩ := hX
  obtain ⟨hσmY, hσpY, hσsY, hγmY, hγpY, hγsY, heqY⟩ := hY
  obtain ⟨β, hβ, hq⟩ := exists_bieleckiWeight_rate_lt_one (n := n) (d := d) (T := T) L hT
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  have hXe := lintegral_lintegral_sq_lt_top_of_supL2 hXS
  have hYe := lintegral_lintegral_sq_lt_top_of_supL2 hYS
  have hswapX : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) :=
    hXm.comp (measurable_snd.prodMk measurable_fst)
  have hswapY : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Y s ω) :=
    hYm.comp (measurable_snd.prodMk measurable_fst)
  have hsubm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω) :=
    hswapX.sub hswapY
  have hnorm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖) :=
    hsubm.norm
  have hcontr := bieleckiNorm_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X Y x₀
    hσmX hσpX hσsX hγmX hγpX hγsX hσmY hσpY hσsY hγmY hγpY hγsY
    (fun i => measurable_mu_comp_state coeffs hReg hXm i)
    (fun i => measurable_mu_comp_state coeffs hReg hYm i)
    hnorm
    (fun i b _ => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hXe i (by assumption))
    (fun i b _ => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hYe i (by assumption))
    (fun b _ => lintegral_sq_sub_lt_top_of_energy hXm hYm hXe hYe b)
    hsubm hβ hT
  have hcongr : bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i =>
          picardStep W N ℱ hℱW hℱN coeffs X x₀ hσmX hσpX hσsX hγmX hγpX hγsX t ω i
            - picardStep W N ℱ hℱW hℱN coeffs Y x₀ hσmY hσpY hσsY hγmY hγpY hγsY t ω i) := by
    refine bieleckiNorm_congr_ae_on β T fun t ht => ?_
    filter_upwards [heqX t ht, heqY t ht] with ω hωX hωY
    funext i
    rw [hωX i, hωY i]
  have hfin : bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) ≠ ⊤ :=
    (bieleckiNorm_sub_lt_top_of_lt_top hβ.le T hXm hYm
      (bieleckiNorm_lt_top_of_supL2 hT hXS) (bieleckiNorm_lt_top_of_supL2 hT hYS)).ne
  have hle : bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      ≤ q * bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
    rw [hqdef]
    conv_lhs => rw [hcongr]
    exact hcontr
  have hzero : bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) = 0 :=
    eq_zero_of_le_mul_self hfin hq hle
  intro t ht
  have hsl : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => X u ω i - Y u ω i := by
    intro u i
    exact ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hXm)).sub
      ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hYm))
  filter_upwards [ae_eq_zero_of_bieleckiNorm_eq_zero hsl hzero ht] with ω hω
  intro i
  exact sub_eq_zero.mp (hω i)

end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
/-- Progressive measurability of the diffusion integrand along a progressively measurable
state process. -/
theorem progressivelyMeasurable_sigma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state hXa h

omit [IsProbabilityMeasure P] in
/-- Marked progressive measurability of the jump integrand along a progressively measurable
state process. -/
theorem markedProgressivelyMeasurable_gamma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state
    (g := fun (s : ℝ) (x : Fin n → ℝ) (e : E) => coeffs.γ s x e i) hXa h

/-- The `L²` bound on the diffusion integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_sigma_lt_top_of_supL2
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip hXm
    (lintegral_lintegral_sq_lt_top_of_supL2 hXS) i j hT'

/-- The `L²` bound on the jump integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_gamma_lt_top_of_supL2 [SigmaFinite ν]
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip hXm
    (lintegral_lintegral_sq_lt_top_of_supL2 hXS) i hT'

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

/-- Freezing a path map at a horizon does not change the Picard step at earlier times. -/
theorem picardStep_rawStop_congr_ae
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (hZS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hT : 0 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω
        = picardStep W N ℱ hℱW hℱN coeffs Z x₀
            (measurable_sigma_comp_state coeffs hReg hZm)
            (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
            (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            (measurable_gamma_comp_state coeffs hReg hZm)
            (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
            (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            t ω := by
  have hfrozenm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  rcases ht0.lt_or_eq with ht0' | ht0'
  swap
  · subst ht0'
    filter_upwards [ae_picardStep_zero W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
        (measurable_sigma_rawStop coeffs hReg hZm T)
        (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
        (fun i j _ hb => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
        (measurable_gamma_rawStop coeffs hReg hZm T)
        (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
        (fun i _ hb => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (lintegral_sq_rawStop_lt_top hZm hZb hT) i hb),
      ae_picardStep_zero W N ℱ hℱW hℱN coeffs Z x₀
        (measurable_sigma_comp_state coeffs hReg hZm)
        (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
        (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
        (measurable_gamma_comp_state coeffs hReg hZm)
        (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
        (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)] with ω h1 h2
    funext i
    rw [h2 i]
    exact h1 i
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      (fun (s : ℝ) (ω : Ω) => Z (min s T) ω) s ω = Z s ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    simp only [min_eq_left (hs.2.trans htT)]
  exact picardStep_congr_ae W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) Z x₀
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hb => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hb => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (lintegral_sq_rawStop_lt_top hZm hZb hT) i hb)
    (measurable_sigma_comp_state coeffs hReg hZm)
    (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
    (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    (measurable_gamma_comp_state coeffs hReg hZm)
    (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
    (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    ht0' hae

/-- A fixed point of the frozen Picard step solves the equation on the window. -/
theorem solvesOn_of_isFixedPoint
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → (Fin n → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hYa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hYb : bieleckiNorm (P := P) 0 T Y < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
      Y t ω i = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT x₀ t ω i) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  refine ⟨measurable_sigma_comp_state coeffs hReg hYm,
    progressivelyMeasurable_sigma_comp_state coeffs hReg hYa,
    lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hYm hYS,
    measurable_gamma_comp_state coeffs hReg hYm,
    markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hYa,
    lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hYm hYS, ?_⟩
  intro t ht
  filter_upwards [hfix t ht,
    picardStep_rawStop_congr_ae W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hYb hYS hT
      ht.1 ht.2] with ω h1 h2
  intro i
  rw [h1 i, h2]

/-- **Existence on a window.** For every horizon there is a càdlàg, progressively measurable
path map with a finite `S²` norm solving the equation on `[0, T]`. -/
theorem exists_solvesOn [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  obtain ⟨β, hβ, hq⟩ := exists_bieleckiWeight_rate_lt_one (n := n) (d := d) (T := T) L hT
  set X₀ := constantZeroProcess (n := n) P ℱ T with hX₀
  set Z := picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hZ
  have hZm := measurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hZa := progressivelyMeasurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hZb := bieleckiNorm_picardLimit_lt_top W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Y := picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => lintegral_sq_iSup_picardSelfMapRaw_lt_top W N ℱ hℱW hℱN hℱ0 hnull coeffs
      hReg hLip x₀ hT hZm hZa hZb hT'
  refine ⟨Y.X, Y.measurable_path, Y.adapted, Y.cadlag_paths, hYS, ?_⟩
  refine solvesOn_of_isFixedPoint W N ℱ hℱW hℱN coeffs hReg hLip x₀ hT.le
    Y.measurable_path Y.adapted Y.sup_L2 hYS ?_
  intro t ht
  exact picardSelfMapRaw_isFixedPoint W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀
    hq ht

end FixedPoint

end LevyStochCalc.Ito.Picard
