/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.Pairing
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The `H^{-1}` dual energy norm

Letwin, arXiv:2607.24164v1, (2.19): for a probability law `μ` and `q ∈ L²(μ)`,
`‖q‖_{H^{-1}(μ)} = sup { ∫ q f dμ : f locally Lipschitz, ∫ ‖∇f‖² dμ ≤ 1 }`. The supremum is taken as
an extended real over the full test class (no centering, smoothness or compact support); it is
identified with the real signed supremum only once finiteness is proved. Constant inputs have
infinite dual norm (constants are zero-energy tests).

Elementary bounds: a finite dual norm controls every pairing `⟪q, h⟫ ≤ ‖q‖_{H⁻¹} (∫ ‖∇h‖²)^{1/2}`
with a locally Lipschitz `h ∈ L²` of square-integrable gradient (`inner_toLp_le_mul_sqrt_energy`)
and forces `∫ q dμ = 0` (`integral_eq_zero_of_dualNorm_ne_top`); the dual norm is subadditive
(`dualNorm_add_le`); and a gradient Poincaré inequality with constant `C` gives
`‖q‖_{H⁻¹} ≤ √C ‖q‖_{L²}` for centered `q` (`dualNorm_le_of_variance_le`). No log-concavity or
smoothness is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

noncomputable section

namespace FunctionalInequalities.Energy.Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- **Unit-energy tests** (Letwin (2.19)): locally Lipschitz `f ∈ L²(μ)` with `∇f ∈ L²(μ)` and
`∫ ‖∇f‖² dμ ≤ 1`; no centering, smoothness or compact support is required. -/
structure UnitEnergyTest (μ : ProbabilityMeasure E) where
  fn : E → ℝ
  locallyLipschitz : LocallyLipschitz fn
  memLp : MemLp fn 2 (μ : Measure E)
  gradLp : MemLp (gradient fn) 2 (μ : Measure E)
  energy : ‖gradLp.toLp (gradient fn)‖ ≤ 1

/-- The signed pairing `⟪q, f⟫_{L²(μ)}` of `q ∈ L²(μ)` with a unit-energy test. -/
def pairing (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) (t : UnitEnergyTest μ) : ℝ :=
  ⟪q, t.memLp.toLp t.fn⟫

/--
The `H^{-1}(μ)` dual norm `‖q‖_{H^{-1}} = sup_f ⟪q, f⟫` over unit-energy tests, as an extended real
(the positive part of each signed pairing). -/
def dualNorm (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) : ENNReal :=
  ⨆ t : UnitEnergyTest μ, ENNReal.ofReal (pairing μ q t)

def signedPairings (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) : Set ℝ :=
  Set.range (pairing μ q)

/-- The unit-energy condition is `∫ ‖∇f‖² dμ ≤ 1`. -/
theorem unit_gradient_norm_iff (μ : ProbabilityMeasure E) {f : E → ℝ}
    (hgrad : MemLp (gradient f) 2 (μ : Measure E)) :
    ‖hgrad.toLp (gradient f)‖ ≤ 1 ↔ ∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure E) ≤ 1 := by
  rw [Lp.norm_toLp, L2.integral_norm_sq_eq_eLpNorm_sq hgrad]
  have hn : 0 ≤ (eLpNorm (gradient f) 2 (μ : Measure E)).toReal := ENNReal.toReal_nonneg
  constructor <;> intro h <;> nlinarith

/-- The zero test. -/
def zeroTest (μ : ProbabilityMeasure E) : UnitEnergyTest μ where
  fn := fun _ => 0
  locallyLipschitz := LocallyLipschitz.const 0
  memLp := memLp_const 0
  gradLp := by rw [gradient_fun_const']; exact memLp_const (0 : E)
  energy := by
    have hg : gradient (fun _ : E => (0 : ℝ)) = 0 := by funext x; exact gradient_fun_const x 0
    rw [Lp.norm_toLp, hg, eLpNorm_zero, ENNReal.toReal_zero]
    norm_num

@[simp] theorem pairing_zero (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) :
    pairing μ q (zeroTest μ) = 0 := by
  change ⟪q, (0 : Lp ℝ 2 (μ : Measure E))⟫ = 0
  exact inner_zero_right q

omit [MeasurableSpace E] in
/-- `∇(−f) = −∇f`. -/
theorem gradient_neg_fn (f : E → ℝ) : gradient (fun x => -f x) = -gradient f := by
  funext x
  simp only [gradient, fderiv_fun_neg, map_neg, Pi.neg_apply]

/-- Negation of a unit-energy test. -/
def negTest (μ : ProbabilityMeasure E) (t : UnitEnergyTest μ) : UnitEnergyTest μ where
  fn := fun x => -t.fn x
  locallyLipschitz := by
    have hn : LocallyLipschitz (fun y : ℝ => -y) :=
      (LipschitzWith.id.neg).locallyLipschitz
    exact hn.comp t.locallyLipschitz
  memLp := t.memLp.neg
  gradLp := by rw [gradient_neg_fn]; exact t.gradLp.neg
  energy := by
    rw [Lp.norm_toLp, gradient_neg_fn, eLpNorm_neg]
    simpa only [Lp.norm_toLp] using t.energy

@[simp] theorem pairing_neg (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (t : UnitEnergyTest μ) : pairing μ q (negTest μ t) = -pairing μ q t := by
  change ⟪q, t.memLp.neg.toLp (-t.fn)⟫ = -⟪q, t.memLp.toLp t.fn⟫
  rw [MemLp.toLp_neg, inner_neg_right]

/-- The dual norm is also the supremum of the absolute pairings. -/
theorem dualNorm_eq_iSup_abs (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) :
    dualNorm μ q = ⨆ t : UnitEnergyTest μ, ENNReal.ofReal |pairing μ q t| := by
  apply le_antisymm
  · apply iSup_le
    intro t
    exact
      (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
        (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal |pairing μ q s|) t)
  · apply iSup_le
    intro t
    by_cases hp : 0 ≤ pairing μ q t
    · rw [abs_of_nonneg hp]
      exact le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) t
    · rw [abs_of_neg (lt_of_not_ge hp), ← pairing_neg μ q t]
      exact le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) (negTest μ t)

/-- Each signed pairing is at most the (finite) dual norm. -/
theorem pairing_le_toReal_of_ne_top (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) (t : UnitEnergyTest μ) :
    pairing μ q t ≤ (dualNorm μ q).toReal := by
  by_cases hp : 0 ≤ pairing μ q t
  · have h := (ENNReal.toReal_le_toReal (by simp) hfinite).mpr
      (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) t)
    simpa only [ENNReal.toReal_ofReal hp] using h
  · exact (lt_of_not_ge hp).le.trans ENNReal.toReal_nonneg

/-- Finite dual norm bounds the set of signed pairings. -/
theorem signedPairings_bdd_of_ne_top (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) : BddAbove (signedPairings μ q) := by
  refine ⟨(dualNorm μ q).toReal, ?_⟩
  rintro r ⟨t, rfl⟩
  exact pairing_le_toReal_of_ne_top μ q hfinite t

/-- When finite, the dual norm is the real supremum of the signed pairings (the paper's (2.19)). -/
theorem toReal_dualNorm_eq_signed_sSup (μ : ProbabilityMeasure E)
    (q : Lp ℝ 2 (μ : Measure E)) (hfinite : dualNorm μ q ≠ ⊤) :
    (dualNorm μ q).toReal = sSup (signedPairings μ q) := by
  have hb := signedPairings_bdd_of_ne_top μ q hfinite
  have hz : (0 : ℝ) ∈ signedPairings μ q := ⟨zeroTest μ, pairing_zero μ q⟩
  have hs0 : 0 ≤ sSup (signedPairings μ q) := le_csSup hb hz
  apply le_antisymm
  · have hle : dualNorm μ q ≤ ENNReal.ofReal (sSup (signedPairings μ q)) := by
      apply iSup_le
      intro t
      exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨t, rfl⟩)
    have h := (ENNReal.toReal_le_toReal hfinite (by simp)).mpr hle
    simpa only [ENNReal.toReal_ofReal hs0] using h
  · apply csSup_le ⟨0, hz⟩
    rintro r ⟨t, rfl⟩
    exact pairing_le_toReal_of_ne_top μ q hfinite t

section Bounds

omit [MeasurableSpace E] in
/-- `∇(c f) = c ∇f` for every real `c`, without differentiability of `f`. -/
theorem gradient_const_mul_fn (c : ℝ) (f : E → ℝ) :
    gradient (fun x => c * f x) = c • gradient f := by
  have hf : (fun x => c * f x) = c • f := rfl
  funext x
  rw [hf]
  simp only [gradient, fderiv_const_smul_field, Pi.smul_apply, map_smulₛₗ,
    RCLike.conj_to_real]

/-- A scaled copy `c h` of a locally Lipschitz `h ∈ L²(μ)` with `∇h ∈ L²(μ)` and
`c² ∫ ‖∇h‖² ≤ 1` is a unit-energy test. -/
private def scaledTest (μ : ProbabilityMeasure E) {h : E → ℝ} (hlip : LocallyLipschitz h)
    (h2 : MemLp h 2 (μ : Measure E)) (hg : MemLp (gradient h) 2 (μ : Measure E)) (c : ℝ)
    (hc : c ^ 2 * ∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E) ≤ 1) : UnitEnergyTest μ where
  fn := fun x => c * h x
  locallyLipschitz := by
    have hm : LocallyLipschitz (fun y : ℝ => c * y) :=
      (lipschitzWith_smul (β := ℝ) c).locallyLipschitz
    exact hm.comp hlip
  memLp := h2.const_mul c
  gradLp := by rw [gradient_const_mul_fn]; exact hg.const_smul c
  energy := by
    have hgc : MemLp (gradient (fun x => c * h x)) 2 (μ : Measure E) := by
      rw [gradient_const_mul_fn]; exact hg.const_smul c
    refine (unit_gradient_norm_iff μ hgc).mpr ?_
    rw [gradient_const_mul_fn]
    calc ∫ x, ‖(c • gradient h) x‖ ^ 2 ∂(μ : Measure E)
        = c ^ 2 * ∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E) := by
          rw [← integral_const_mul]
          congr 1
          funext x
          rw [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ 1 := hc

private theorem pairing_scaledTest (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    {h : E → ℝ} (hlip : LocallyLipschitz h) (h2 : MemLp h 2 (μ : Measure E))
    (hg : MemLp (gradient h) 2 (μ : Measure E)) (c : ℝ)
    (hc : c ^ 2 * ∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E) ≤ 1) :
    pairing μ q (scaledTest μ hlip h2 hg c hc) = c * ⟪q, h2.toLp h⟫ := by
  change ⟪q, (h2.const_mul c).toLp (fun x => c * h x)⟫ = c * ⟪q, h2.toLp h⟫
  have hsm : (h2.const_mul c).toLp (fun x => c * h x) = c • h2.toLp h :=
    MemLp.toLp_const_smul c h2
  rw [hsm, real_inner_smul_right]

/-- **Pairing bound from a finite dual norm**: for a locally Lipschitz `h ∈ L²(μ)` with
`∇h ∈ L²(μ)`, `⟪q, h⟫ ≤ ‖q‖_{H⁻¹(μ)} (∫ ‖∇h‖² dμ)^{1/2}`. The energy of `h` is not normalized;
when it vanishes the pairing is nonpositive. -/
theorem inner_toLp_le_mul_sqrt_energy (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) {h : E → ℝ} (hlip : LocallyLipschitz h)
    (h2 : MemLp h 2 (μ : Measure E)) (hg : MemLp (gradient h) 2 (μ : Measure E)) :
    ⟪q, h2.toLp h⟫ ≤
      (dualNorm μ q).toReal * Real.sqrt (∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E)) := by
  set En : ℝ := ∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E) with hEn
  set N : ℝ := (dualNorm μ q).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hE0 : 0 ≤ En := integral_nonneg fun x => sq_nonneg _
  rcases hE0.eq_or_lt with hzero | hpos
  · rw [← hzero, Real.sqrt_zero, mul_zero]
    by_contra hneg
    push Not at hneg
    set P : ℝ := ⟪q, h2.toLp h⟫
    have hc : ((N + 1) / P) ^ 2 * En ≤ 1 := by rw [← hzero, mul_zero]; exact zero_le_one
    have hle := pairing_le_toReal_of_ne_top μ q hfinite (scaledTest μ hlip h2 hg ((N + 1) / P) hc)
    rw [pairing_scaledTest, div_mul_cancel₀ _ hneg.ne'] at hle
    linarith
  · have hs : 0 < Real.sqrt En := Real.sqrt_pos.mpr hpos
    have hc : (1 / Real.sqrt En) ^ 2 * En ≤ 1 := by
      rw [div_pow, Real.sq_sqrt hE0, one_pow, one_div, inv_mul_cancel₀ hpos.ne']
    have hle := pairing_le_toReal_of_ne_top μ q hfinite (scaledTest μ hlip h2 hg _ hc)
    rw [pairing_scaledTest, one_div, inv_mul_le_iff₀ hs] at hle
    linarith [mul_comm N (Real.sqrt En)]


/-- The two-sided form of `inner_toLp_le_mul_sqrt_energy`:
`|⟪q, h⟫| ≤ ‖q‖_{H⁻¹(μ)} (∫ ‖∇h‖² dμ)^{1/2}`. -/
theorem abs_inner_toLp_le_mul_sqrt_energy (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) {h : E → ℝ} (hlip : LocallyLipschitz h)
    (h2 : MemLp h 2 (μ : Measure E)) (hg : MemLp (gradient h) 2 (μ : Measure E)) :
    |⟪q, h2.toLp h⟫| ≤
      (dualNorm μ q).toReal * Real.sqrt (∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E)) := by
  rw [abs_le]
  refine ⟨?_, inner_toLp_le_mul_sqrt_energy μ q hfinite hlip h2 hg⟩
  have hn : LocallyLipschitz (fun x => -h x) :=
    (LipschitzWith.id.neg.locallyLipschitz).comp hlip
  have hgn : MemLp (gradient (fun x => -h x)) 2 (μ : Measure E) := by
    rw [gradient_neg_fn]; exact hg.neg
  have h' := inner_toLp_le_mul_sqrt_energy μ q hfinite hn h2.neg hgn
  have htl : h2.neg.toLp (fun x => -h x) = -h2.toLp h := MemLp.toLp_neg h2
  rw [htl, inner_neg_right, gradient_neg_fn] at h'
  simp only [Pi.neg_apply, norm_neg] at h'
  linarith

/-- **A finite dual norm forces mean zero**: constants are zero-energy tests. -/
theorem integral_eq_zero_of_dualNorm_ne_top (μ : ProbabilityMeasure E)
    (q : Lp ℝ 2 (μ : Measure E)) (hfinite : dualNorm μ q ≠ ⊤) :
    ∫ x, q x ∂(μ : Measure E) = 0 := by
  have hconst (c : ℝ) : ⟪q, (memLp_const c).toLp (fun _ : E => c)⟫ ≤ 0 := by
    have hg : MemLp (gradient (fun _ : E => c)) 2 (μ : Measure E) := by
      rw [gradient_fun_const']; exact memLp_const (0 : E)
    have h := inner_toLp_le_mul_sqrt_energy μ q hfinite (LocallyLipschitz.const c)
      (memLp_const c) hg
    have hz : (∫ x, ‖gradient (fun _ : E => c) x‖ ^ 2 ∂(μ : Measure E)) = 0 := by
      simp [gradient_fun_const']
    rwa [hz, Real.sqrt_zero, mul_zero] at h
  have hval (c : ℝ) : ⟪q, (memLp_const c).toLp (fun _ : E => c)⟫ =
      c * ∫ x, q x ∂(μ : Measure E) := by
    rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(memLp_const (μ := (μ : Measure E)) (p := 2) c).coeFn_toLp] with x hx
    rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, RCLike.re_to_real, conj_trivial]
  have h1 := hconst 1
  have h2 := hconst (-1)
  rw [hval] at h1 h2
  linarith

/-- **Subadditivity** of the dual norm. -/
theorem dualNorm_add_le (μ : ProbabilityMeasure E) (q r : Lp ℝ 2 (μ : Measure E)) :
    dualNorm μ (q + r) ≤ dualNorm μ q + dualNorm μ r := by
  apply iSup_le
  intro t
  have hp : pairing μ (q + r) t = pairing μ q t + pairing μ r t := inner_add_left _ _ _
  rw [hp]
  exact (ENNReal.ofReal_add_le).trans (add_le_add
    (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) t)
    (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ r s)) t))

/-- **Dual norm from a Poincaré inequality** (Letwin arXiv:2607.24164v1, (2.19)): if
`Var_μ g ≤ C ∫ ‖∇g‖² dμ` for every locally Lipschitz `g ∈ L²(μ)` with `∇g ∈ L²(μ)`, then every
`q ∈ L²(μ)` with `∫ q dμ = 0` has `‖q‖_{H⁻¹(μ)} ≤ √C ‖q‖_{L²(μ)}`. -/
theorem dualNorm_le_of_variance_le (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hq : ∫ x, q x ∂(μ : Measure E) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hP :
      ∀ g : E → ℝ,
        LocallyLipschitz g →
          MemLp g 2 (μ : Measure E) →
            MemLp (gradient g) 2 (μ : Measure E) →
              ProbabilityTheory.variance g (μ : Measure E) ≤
                C * ∫ x, ‖gradient g x‖ ^ 2 ∂(μ : Measure E)) :
    dualNorm μ q ≤ ENNReal.ofReal (Real.sqrt C * ‖q‖) := by
  apply iSup_le
  intro t
  apply ENNReal.ofReal_le_ofReal
  set T : Lp ℝ 2 (μ : Measure E) := t.memLp.toLp t.fn
  have hmq : L2.mean μ q = 0 := by rw [L2.mean_eq_integral]; exact hq
  have hcq : L2.center μ q = q := by simp [L2.center, hmq]
  have hinner : pairing μ q t = ⟪q, L2.center μ T⟫ := by
    have h := L2.inner_center_center μ q T
    rw [hcq, hmq, zero_mul, sub_zero] at h
    exact h.symm
  have hvar : ‖L2.center μ T‖ ^ 2 ≤ C := by
    rw [← L2.coe_variance, L2.variance_toLp,
      Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _)]
    have hE := (unit_gradient_norm_iff μ t.gradLp).mp t.energy
    have hV := hP t.fn t.locallyLipschitz t.memLp t.gradLp
    nlinarith [(integral_nonneg fun x => sq_nonneg ‖gradient t.fn x‖ :
        0 ≤ ∫ x, ‖gradient t.fn x‖ ^ 2 ∂(μ : Measure E))]
  have hT : ‖L2.center μ T‖ ≤ Real.sqrt C := Real.le_sqrt_of_sq_le hvar
  rw [hinner]
  calc
    ⟪q, L2.center μ T⟫ ≤ ‖q‖ * ‖L2.center μ T‖ := real_inner_le_norm _ _
    _ ≤ ‖q‖ * Real.sqrt C := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ = Real.sqrt C * ‖q‖ := mul_comm _ _

end Bounds

end FunctionalInequalities.Energy.Dual

end
