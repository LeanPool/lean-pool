/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Symmetry
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RestrictedCZInterpolation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCertificate

/-!
# Riesz Second All Exponents Paper

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
noncomputable section

namespace CKN.Foundation.Euclidean

@[expose]
def dualTruncSet (u : Vec3 → ℝ) (R : ℝ) : Set Vec3 :=
  Metric.closedBall 0 R ∩ {x | |u x| ≤ R}

@[expose]
def dualTruncField (u : Vec3 → ℝ) (p R : ℝ) : Vec3 → ℝ :=
  (dualTruncSet u R).indicator (fun x => |u x| ^ (p - 2) * u x)

private lemma measurable_abs_of_measurable {u : Vec3 → ℝ} (hu : Measurable u) :
    Measurable (fun x => |u x|) := by
  convert measurable_norm.comp hu using 1
  ext x
  exact (Real.norm_eq_abs (u x)).symm

private lemma dualTruncSet_measurable {u : Vec3 → ℝ} {R : ℝ}
    (hu : Measurable u) : MeasurableSet (dualTruncSet u R) := by
  apply measurableSet_closedBall.inter
  exact measurableSet_Iic.preimage (measurable_abs_of_measurable hu)

private lemma dualTruncField_memLp {u : Vec3 → ℝ} {p R : ℝ}
    (hu : Measurable u) (hp : 2 ≤ p) (r : ℝ≥0∞) :
    MemLp (dualTruncField u p R) r volume := by
  let A := dualTruncSet u R
  let b : Vec3 → ℝ := fun x => |u x| ^ (p - 2) * u x
  have hAmeas : MeasurableSet A := dualTruncSet_measurable hu
  have hAsub : A ⊆ Metric.closedBall (0 : Vec3) R := by
    intro x hx
    exact hx.1
  have hball : IsCompact (Metric.closedBall (0 : Vec3) R) :=
    isCompact_closedBall _ _
  have hAfinite : volume A < ∞ :=
    (measure_mono hAsub).trans_lt hball.measure_lt_top
  let : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr hAfinite.ne
  have hbmeas : Measurable b := by
    dsimp [b]
    exact (Real.continuous_rpow_const (by linarith only [hp])).measurable.comp
      (measurable_abs_of_measurable hu) |>.mul hu
  have hbBound : ∀ᵐ x ∂(volume.restrict A), ‖b x‖ ≤ R ^ (p - 1) := by
    filter_upwards [ae_restrict_mem hAmeas] with x hx
    change |(|u x| ^ (p - 2) * u x)| ≤ R ^ (p - 1)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |u x| ^ (p - 2) * |u x| = |u x| ^ (p - 1) := by
        have hexp : p - 1 = (p - 2) + 1 := by ring
        rw [hexp, ← Real.rpow_add_one' (abs_nonneg _) (by linarith only [hp])]
      _ ≤ R ^ (p - 1) :=
        Real.rpow_le_rpow (abs_nonneg _) hx.2 (by linarith only [hp])
  have hbLp : MemLp b r (volume.restrict A) :=
    MemLp.of_bound hbmeas.aestronglyMeasurable (R ^ (p - 1)) hbBound
  rw [dualTruncField, memLp_indicator_iff_restrict hAmeas]
  simpa only [A, b] using hbLp

private lemma dualTrunc_pairing_power {a p : ℝ} (hp : 2 ≤ p) :
    a * (|a| ^ (p - 2) * a) = |a| ^ p := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero]
    rw [Real.zero_rpow (by linarith only [hp] : p ≠ 0)]
    simp
  · have habs : 0 < |a| := abs_pos.mpr ha
    have hsq : a * a = |a| ^ (2 : ℕ) := by
      rw [sq_abs]
      ring
    calc
      a * (|a| ^ (p - 2) * a) = |a| ^ (p - 2) * (a * a) := by ring
      _ = |a| ^ (p - 2) * |a| ^ (2 : ℝ) := by rw [Real.rpow_two, hsq]
      _ = |a| ^ p := by
        rw [← Real.rpow_add habs]
        congr 1
        ring

private lemma dualTrunc_abs {a p : ℝ} (hp : 2 ≤ p) :
    |(|a| ^ (p - 2) * a)| = |a| ^ (p - 1) := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero]
    rw [Real.zero_rpow (by linarith only [hp] : p - 1 ≠ 0)]
    simp
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hexp : p - 1 = (p - 2) + 1 := by ring
    rw [hexp, ← Real.rpow_add_one' (abs_nonneg _) (by linarith only [hp])]

private lemma dualTruncField_rpow_integral {u : Vec3 → ℝ} {p q R : ℝ}
    (hu : Measurable u) (hp : 2 ≤ p) (hq : 0 < q)
    (hqp : q * (p - 1) = p) :
    ∫ x, |dualTruncField u p R x| ^ q =
      ∫ x in dualTruncSet u R, |u x| ^ p := by
  let A := dualTruncSet u R
  have hpoint : ∀ x, |dualTruncField u p R x| ^ q =
      A.indicator (fun y => |u y| ^ p) x := by
    intro x
    by_cases hx : x ∈ A
    · change |(dualTruncSet u R).indicator
          (fun y => |u y| ^ (p - 2) * u y) x| ^ q = _
      rw [Set.indicator_of_mem hx]
      rw [Set.indicator_of_mem hx]
      rw [dualTrunc_abs hp]
      calc
        (|u x| ^ (p - 1)) ^ q = |u x| ^ ((p - 1) * q) :=
          (Real.rpow_mul (abs_nonneg (u x)) (p - 1) q).symm
        _ = |u x| ^ (q * (p - 1)) := by rw [mul_comm]
        _ = |u x| ^ p := by rw [hqp]
    · change |(dualTruncSet u R).indicator
          (fun y => |u y| ^ (p - 2) * u y) x| ^ q = _
      rw [Set.indicator_of_notMem hx]
      rw [Set.indicator_of_notMem hx]
      simp [Real.zero_rpow, ne_of_gt hq]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_indicator (dualTruncSet_measurable hu)]

private theorem lpNorm_bound_of_eLpNorm_paper
    {f g : Vec3 → ℝ} {p : ℝ} {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hbound : eLpNorm g (ENNReal.ofReal p) volume ≤
      K * eLpNorm f (ENNReal.ofReal p) volume) :
    lpNorm g (ENNReal.ofReal p) volume ≤
      K.toReal * lpNorm f (ENNReal.ofReal p) volume := by
  have hfiniteG : eLpNorm g (ENNReal.ofReal p) volume < ∞ := by
    exact hbound.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) hf)
  have hfiniteF : eLpNorm f (ENNReal.ofReal p) volume ≠ ∞ := hf.ne
  rw [lpNorm, lpNorm]
  rw [← ENNReal.toReal_mul]
  exact (ENNReal.toReal_le_toReal hfiniteG.ne
    (ENNReal.mul_ne_top hK hfiniteF)).2 hbound

private theorem lpNorm_eq_integral_norm_rpow_ofReal
    {f : Vec3 → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    lpNorm f (ENNReal.ofReal p) volume =
      (∫ x, ‖f x‖ ^ p) ^ (1 / p) := by
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  rw [lpNorm, MemLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top hf]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le, one_div,
    ENNReal.toReal_ofReal_eq_iff, ge_iff_le]
  positivity

private theorem dualTrunc_energy_bound
    {i j : Fin 3} {p q : ℝ} (hL2 : RieszSecondL2Input i j)
    (hweak : ∀ g, Measurable g → Integrable g volume →
      MemLp g (2 : ℝ≥0∞) volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 g x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE g x) / ENNReal.ofReal l)
    (hp1 : 1 < p) (hp2 : 2 < p) (hq1 : 1 < q) (hq2 : q < 2)
    (hholder : p.HolderConjugate q) (hqp : q * (p - 1) = p)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hf2 : MemLp f (2 : ℝ≥0∞) volume) {R : ℝ} :
    ∫ x in dualTruncSet (rieszSecondL2RawOperator hL2 f) R,
        |rieszSecondL2RawOperator hL2 f x| ^ p ≤
      ((rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q) ^
        (1 / q : ℝ) * lpNorm f (ENNReal.ofReal p) volume) ^ p := by
  let u : Vec3 → ℝ := rieszSecondL2RawOperator hL2 f
  let A : Set Vec3 := dualTruncSet u R
  let v : Vec3 → ℝ := dualTruncField u p R
  have hu : Measurable u := by
    exact rieszSecondL2RawOperator_measurable hL2 hf2
  have hvq : MemLp v (ENNReal.ofReal q) volume := by
    exact dualTruncField_memLp hu (by linarith only [hp2]) _
  have hv2 : MemLp v (2 : ℝ≥0∞) volume := by
    exact dualTruncField_memLp hu (by linarith only [hp2]) _
  have hqfact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq1.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := hqfact
  have hA₁ : 0 ≤ rieszSecondWeakTypeConstant := by
    unfold rieszSecondWeakTypeConstant
    have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
    positivity
  have hraw := CKN.Core.Endgame.raw_rieszSecond_memLp_and_bound_of_weak
    hL2 hweak
    hA₁ hq1 hq2 hvq hv2
  let Kq : ℝ := rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q ^ (1 / q)
  have hKq_nonneg : 0 ≤ Kq := by
    dsimp [Kq, rieszSecondInterpolationConstant]
    positivity
  have hTvbound :
      lpNorm (rieszSecondL2RawOperator hL2 v) (ENNReal.ofReal q) volume ≤
        Kq * lpNorm v (ENNReal.ofReal q) volume := by
    have h := CKN.Core.Endgame.raw_rieszSecond_toLp_bound_of_weak
      hL2 hweak
      hA₁ hq1 hq2 hvq hv2 hraw.1
    simpa only [Kq, Lp.norm_toLp, lpNorm] using h
  have hAmeas : MeasurableSet A := by
    exact dualTruncSet_measurable hu
  have hfield : (fun x => u x * v x) = A.indicator (fun x => |u x| ^ p) := by
    funext x
    by_cases hx : x ∈ A
    · simp [v, dualTruncField, A, hx, dualTrunc_pairing_power (by linarith only [hp2])]
    · simp [v, dualTruncField, A, hx]
  have hsymm := rieszSecondL2RawOperator_integral_mul_commute hL2 hf2 hv2
  have henergy_eq :
      (∫ x in A, |u x| ^ p) = ∫ x, f x * rieszSecondL2RawOperator hL2 v x := by
    calc
      (∫ x in A, |u x| ^ p) = ∫ x, A.indicator (fun x => |u x| ^ p) x :=
        (integral_indicator hAmeas).symm
      _ = ∫ x, u x * v x := by rw [← hfield]
      _ = ∫ x, f x * rieszSecondL2RawOperator hL2 v x := by
        simpa only [u] using hsymm
  have henergy_nonneg : 0 ≤ ∫ x in A, |u x| ^ p :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hTvq : MemLp (rieszSecondL2RawOperator hL2 v) (ENNReal.ofReal q) volume := hraw.1
  have hfFormula := lpNorm_eq_integral_norm_rpow_ofReal (lt_trans zero_lt_one hp1) hf
  have hTvFormula := lpNorm_eq_integral_norm_rpow_ofReal (lt_trans zero_lt_one hq1) hTvq
  have hvFormula := lpNorm_eq_integral_norm_rpow_ofReal (lt_trans zero_lt_one hq1) hvq
  have hvFormula' : lpNorm v (ENNReal.ofReal q) volume =
      (∫ x in A, |u x| ^ p) ^ (1 / q) := by
    calc
      lpNorm v (ENNReal.ofReal q) volume = (∫ x, ‖v x‖ ^ q) ^ (1 / q) := hvFormula
      _ = (∫ x, |v x| ^ q) ^ (1 / q) := by
        congr 2
      _ = (∫ x in A, |u x| ^ p) ^ (1 / q) := by
        rw [dualTruncField_rpow_integral hu (by linarith only [hp2])
          (lt_trans zero_lt_one hq1) hqp]
  have hholderInt := integral_mul_norm_le_Lp_mul_Lq hholder hf hTvq
  have henergy_holder :
      (∫ x in A, |u x| ^ p) ≤
        lpNorm f (ENNReal.ofReal p) volume *
          lpNorm (rieszSecondL2RawOperator hL2 v) (ENNReal.ofReal q) volume := by
    calc
      (∫ x in A, |u x| ^ p) = |∫ x, f x * rieszSecondL2RawOperator hL2 v x| := by
        calc
          _ = |∫ x in A, |u x| ^ p| := (abs_of_nonneg henergy_nonneg).symm
          _ = |∫ x, f x * rieszSecondL2RawOperator hL2 v x| := congrArg abs henergy_eq
      _ ≤ ∫ x, |f x * rieszSecondL2RawOperator hL2 v x| := abs_integral_le_integral_abs
      _ = ∫ x, ‖f x‖ * ‖rieszSecondL2RawOperator hL2 v x‖ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ lpNorm f (ENNReal.ofReal p) volume *
          lpNorm (rieszSecondL2RawOperator hL2 v) (ENNReal.ofReal q) volume := by
        simpa only [hfFormula, hTvFormula] using hholderInt
  have henergy_bound :
      (∫ x in A, |u x| ^ p) ≤
        (Kq * lpNorm f (ENNReal.ofReal p) volume) *
          (∫ x in A, |u x| ^ p) ^ (1 / q) := by
    calc
      (∫ x in A, |u x| ^ p) ≤
          lpNorm f (ENNReal.ofReal p) volume *
            lpNorm (rieszSecondL2RawOperator hL2 v) (ENNReal.ofReal q) volume :=
        henergy_holder
      _ ≤ lpNorm f (ENNReal.ofReal p) volume *
          (Kq * lpNorm v (ENNReal.ofReal q) volume) :=
        mul_le_mul_of_nonneg_left hTvbound lpNorm_nonneg
      _ = (Kq * lpNorm f (ENNReal.ofReal p) volume) *
          (∫ x in A, |u x| ^ p) ^ (1 / q) := by rw [hvFormula']; ring
  have hBnonneg : 0 ≤ Kq * lpNorm f (ENNReal.ofReal p) volume :=
    mul_nonneg hKq_nonneg lpNorm_nonneg
  have hE : 0 ≤ ∫ x in A, |u x| ^ p := henergy_nonneg
  by_cases hEzero : ∫ x in A, |u x| ^ p = 0
  · have hnonnegPow : 0 ≤
        (Kq * lpNorm f (ENNReal.ofReal p) volume) ^ p := Real.rpow_nonneg hBnonneg _
    simpa only [u, A, hEzero] using hnonnegPow
  · have hEpos : 0 < ∫ x in A, |u x| ^ p := lt_of_le_of_ne hE (Ne.symm hEzero)
    have hEpowpos : 0 < (∫ x in A, |u x| ^ p) ^ (1 / q) :=
      Real.rpow_pos_of_pos hEpos _
    have hdivide :
        (∫ x in A, |u x| ^ p) / (∫ x in A, |u x| ^ p) ^ (1 / q) ≤
          Kq * lpNorm f (ENNReal.ofReal p) volume :=
      (div_le_iff₀ hEpowpos).2 henergy_bound
    have hexp : 1 - 1 / q = 1 / p := by
      have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
      have hqne : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
      field_simp
      nlinarith only [hqp]
    have hratio :
        (∫ x in A, |u x| ^ p) / (∫ x in A, |u x| ^ p) ^ (1 / q) =
          (∫ x in A, |u x| ^ p) ^ (1 - 1 / q) := by
      calc
        _ = (∫ x in A, |u x| ^ p) ^ 1 /
              (∫ x in A, |u x| ^ p) ^ (1 / q) := by simp
        _ = (∫ x in A, |u x| ^ p) ^ (1 - 1 / q) :=
          (Real.rpow_sub hEpos 1 (1 / q)).symm
    rw [hratio, hexp] at hdivide
    have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hE (1 / p)) hdivide
      (le_of_lt (lt_trans zero_lt_one hp1))
    have hpower_eq :
        ((∫ x in A, |u x| ^ p) ^ (1 / p)) ^ p = ∫ x in A, |u x| ^ p := by
      rw [← Real.rpow_mul hE (1 / p) p]
      have hmul : (1 / p) * p = 1 := by field_simp [ne_of_gt (lt_trans zero_lt_one hp1)]
      rw [hmul, Real.rpow_one]
    simpa only [u, A, Kq, hpower_eq] using hpower

@[expose]
def dualTruncENNSet (u : Vec3 → ℝ) (n : ℕ) : Set Vec3 :=
  dualTruncSet u ((n : ℝ) + 1)

@[expose]
def dualTruncENNPower (u : Vec3 → ℝ) (p : ℝ) (n : ℕ) : Vec3 → ℝ≥0∞ :=
  (dualTruncENNSet u n).indicator (fun x => absE u x ^ p)

private theorem raw_rieszSecond_memLp_of_duality
    {i j : Fin 3} {p q : ℝ} (hL2 : RieszSecondL2Input i j)
    (hweak : ∀ g, Measurable g → Integrable g volume →
      MemLp g (2 : ℝ≥0∞) volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 g x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE g x) / ENNReal.ofReal l)
    (hp1 : 1 < p) (hp2 : 2 < p) (hq1 : 1 < q) (hq2 : q < 2)
    (hholder : p.HolderConjugate q) (hqp : q * (p - 1) = p)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hf2 : MemLp f (2 : ℝ≥0∞) volume) :
    MemLp (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal p) volume ∧
      lpNorm (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal p) volume ≤
        (rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q ^ (1 / q)) *
          lpNorm f (ENNReal.ofReal p) volume := by
  let u : Vec3 → ℝ := rieszSecondL2RawOperator hL2 f
  have hu : Measurable u := rieszSecondL2RawOperator_measurable hL2 hf2
  have hTf := (rieszSecondL2RawOperator_ae_eq hL2 hf2).trans
    (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 (hf2.toLp f))
  have hu2 : MemLp u (2 : ℝ≥0∞) volume := by
    simpa only [u] using
      (memLp_congr_ae hTf |>.2 (Lp.memLp (rieszSecondL2Extension hL2 (hf2.toLp f))))
  let Kq : ℝ := rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q ^ (1 / q)
  let B : ℝ := Kq * lpNorm f (ENNReal.ofReal p) volume
  have hA₁ : 0 ≤ rieszSecondWeakTypeConstant := by
    unfold rieszSecondWeakTypeConstant
    have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
    positivity
  have hKqnonneg : 0 ≤ Kq := by
    dsimp [Kq, rieszSecondInterpolationConstant]
    positivity
  have hBnonneg : 0 ≤ B := mul_nonneg hKqnonneg lpNorm_nonneg
  have hFmeas : Measurable (fun x => absE u x ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_absE hu)
  have hAmeas : ∀ n, MeasurableSet (dualTruncENNSet u n) := by
    intro n
    exact dualTruncSet_measurable hu
  have hAmono : ∀ n, dualTruncENNSet u n ⊆ dualTruncENNSet u (n + 1) := by
    intro n x hx
    have hnat : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    have hrad : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      linarith only [hnat]
    exact ⟨Metric.closedBall_subset_closedBall hrad hx.1, le_trans hx.2 hrad⟩
  have hpoint : ∀ x, (⨆ n : ℕ, dualTruncENNPower u p n x) = absE u x ^ p := by
    intro x
    apply le_antisymm
    · apply iSup_le
      intro n
      by_cases hx : x ∈ dualTruncENNSet u n
      · simp [dualTruncENNPower, hx]
      · simp [dualTruncENNPower, hx]
    · obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ |u x|)
      have hxmem : x ∈ dualTruncENNSet u n := by
        constructor
        · change dist x (0 : Vec3) ≤ (n : ℝ) + 1
          apply le_of_lt
          calc
            dist x 0 = ‖x‖ := by simp
            _ < (n : ℝ) + 1 := by
              calc
                ‖x‖ ≤ max ‖x‖ |u x| := le_max_left _ _
                _ < (n : ℝ) := hn
                _ ≤ (n : ℝ) + 1 := by exact le_add_of_nonneg_right (by norm_num)
        · change |u x| ≤ (n : ℝ) + 1
          apply le_of_lt
          calc
            |u x| ≤ max ‖x‖ |u x| := le_max_right _ _
            _ < (n : ℝ) := hn
            _ ≤ (n : ℝ) + 1 := by exact le_add_of_nonneg_right (by norm_num)
      exact le_iSup_of_le n (by simp [dualTruncENNPower, hxmem])
  have hmono : ∀ n, ∀ᵐ x ∂volume,
      dualTruncENNPower u p n x ≤ dualTruncENNPower u p (n + 1) x := by
    intro n
    filter_upwards [] with x
    by_cases hx : x ∈ dualTruncENNSet u n
    · have hx' := hAmono n hx
      simp [dualTruncENNPower, hx, hx']
    · simp [dualTruncENNPower, hx]
  have hlinbound : ∀ n,
      ∫⁻ x, dualTruncENNPower u p n x ≤ ENNReal.ofReal (B ^ p) := by
    intro n
    let A := dualTruncENNSet u n
    let v : Vec3 → ℝ := dualTruncField u p ((n : ℝ) + 1)
    have hv2 : MemLp v (2 : ℝ≥0∞) volume :=
      dualTruncField_memLp hu (by linarith only [hp2]) _
    have hAmeas' : MeasurableSet A := hAmeas n
    have hfield : (fun x => u x * v x) = A.indicator (fun x => |u x| ^ p) := by
      funext x
      by_cases hx : x ∈ A
      · have hx' : x ∈ dualTruncSet u ((n : ℝ) + 1) := by
          simpa only [A, dualTruncENNSet] using hx
        change u x * (dualTruncSet u ((n : ℝ) + 1)).indicator
            (fun y => |u y| ^ (p - 2) * u y) x =
          (dualTruncSet u ((n : ℝ) + 1)).indicator (fun y => |u y| ^ p) x
        rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx']
        exact dualTrunc_pairing_power (by linarith only [hp2])
      · have hx' : x ∉ dualTruncSet u ((n : ℝ) + 1) := by
          simpa only [A, dualTruncENNSet] using hx
        change u x * (dualTruncSet u ((n : ℝ) + 1)).indicator
            (fun y => |u y| ^ (p - 2) * u y) x =
          (dualTruncSet u ((n : ℝ) + 1)).indicator (fun y => |u y| ^ p) x
        rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx']
        simp
    have hprod : Integrable (fun x => u x * v x) volume := hu2.integrable_mul hv2
    have hind : Integrable (A.indicator (fun x => |u x| ^ p)) volume :=
      hprod.congr (Filter.Eventually.of_forall fun x => congrFun hfield x)
    have hpowOn : IntegrableOn (fun x => |u x| ^ p) A volume :=
      (integrable_indicator_iff hAmeas').1 hind
    have hconvert : ENNReal.ofReal (∫ x in A, |u x| ^ p) =
        ∫⁻ x in A, absE u x ^ p := by
      rw [ofReal_integral_eq_lintegral_ofReal hpowOn
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)]
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [absE, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (u x))
        (le_of_lt (lt_trans zero_lt_one hp1))]
    calc
      ∫⁻ x, dualTruncENNPower u p n x = ∫⁻ x in A, absE u x ^ p := by
        rw [dualTruncENNPower, lintegral_indicator hAmeas']
      _ = ENNReal.ofReal (∫ x in A, |u x| ^ p) := hconvert.symm
      _ ≤ ENNReal.ofReal (B ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        have hE := dualTrunc_energy_bound (R := (n : ℝ) + 1)
          hL2 hweak hp1 hp2 hq1 hq2 hholder hqp hf hf2
        have hE' : (∫ x in A, |u x| ^ p) ≤ B ^ p := by
          simpa [u, A, B, Kq, dualTruncENNSet] using hE
        exact hE'
  have hglobal : ∫⁻ x, absE u x ^ p ≤ ENNReal.ofReal (B ^ p) := by
    calc
      ∫⁻ x, absE u x ^ p = ∫⁻ x, ⨆ n : ℕ, dualTruncENNPower u p n x := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        exact (hpoint x).symm
      _ = ⨆ n : ℕ, ∫⁻ x, dualTruncENNPower u p n x :=
        lintegral_iSup_ae (fun n => (hFmeas.indicator (hAmeas n))) hmono
      _ ≤ ENNReal.ofReal (B ^ p) := iSup_le hlinbound
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hfinite : ∫⁻ x, absE u x ^ p < ∞ :=
    lt_of_le_of_lt hglobal ENNReal.ofReal_lt_top
  have hfinite' :
      ∫⁻ x, ‖u x‖ₑ ^ (ENNReal.ofReal p).toReal ∂volume < ∞ := by
    simpa only [absE, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp0.le] using hfinite
  have hmem : MemLp u (ENNReal.ofReal p) volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hu.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg
      (one_div_nonneg.mpr ENNReal.toReal_nonneg) hfinite'.ne
  have hroot : (ENNReal.ofReal (B ^ p)) ^ (1 / p) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hBnonneg hp0.le, ← ENNReal.rpow_mul]
    rw [mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hnorm : eLpNorm u (ENNReal.ofReal p) volume ≤ ENNReal.ofReal B := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hu.aestronglyMeasurable]
    calc
      (∫⁻ x, ‖u x‖ₑ ^ (ENNReal.ofReal p).toReal ∂volume) ^ (1 / (ENNReal.ofReal p).toReal) ≤
          (ENNReal.ofReal (B ^ p)) ^ (1 / p) := by
        simpa [absE, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp0.le] using
          ENNReal.rpow_le_rpow hglobal
            (one_div_nonneg.mpr (ENNReal.toReal_nonneg : 0 ≤ (ENNReal.ofReal p).toReal))
      _ = ENNReal.ofReal B := hroot
  have hnormlp : lpNorm u (ENNReal.ofReal p) volume ≤ B := by
    rw [lpNorm]
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal hBnonneg] using hreal
  exact ⟨hmem, by simpa only [u, B, Kq] using hnormlp⟩

private lemma norm_toLp_neg {p : ℝ≥0∞} {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    ‖(hf.neg).toLp (-f)‖ = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_neg]

@[expose]
def negativeRawExtensionInput {i j : Fin 3} {p : ℝ≥0∞} {C : ℝ}
    [Fact (1 ≤ p)] (hL2 : RieszSecondL2Input i j)
    (houtput : ∀ {f : Vec3 → ℝ}, MemLp f p volume →
      MemLp f (2 : ℝ≥0∞) volume →
      MemLp (-rieszSecondL2RawOperator hL2 f) p volume)
    (hbound : ∀ {f : Vec3 → ℝ} (hf : MemLp f p volume)
      (hf2 : MemLp f (2 : ℝ≥0∞) volume),
      ‖(houtput hf hf2).toLp (-rieszSecondL2RawOperator hL2 f)‖ ≤
        C * ‖hf.toLp f‖) : LpExtensionInput p C := by
  refine
    { T := fun f => -rieszSecondL2RawOperator hL2 f
      measurable := ?_
      output_mem := houtput
      congr_ae := ?_
      add_ae := ?_
      smul_ae := ?_
      bound := hbound }
  · intro f hf
    exact (rieszSecondL2RawOperator_measurable hL2 hf).neg
  · intro f g hf hg hfg
    exact (CKN.Core.Endgame.raw_rieszSecond_congr_ae hL2 hf hg hfg).neg
  · intro f g hf hg
    have h := CKN.Core.Endgame.raw_rieszSecond_add_ae hL2 hf hg
    simpa only [Pi.neg_apply, neg_add] using h.neg
  · intro c f hf
    have h := CKN.Core.Endgame.raw_rieszSecond_smul_ae hL2 c hf
    simpa only [smul_neg] using h.neg

private theorem negativeRawExtensionCore_producer {i j : Fin 3}
    {p : ℝ≥0∞} {C : ℝ} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hL2 : RieszSecondL2Input i j) (hC : 0 ≤ C)
    (hinput : LpExtensionInput p C)
    (hidentify : ∀ {g : Vec3 → ℝ}, MemLp g p volume →
      MemLp g (2 : ℝ≥0∞) volume →
      hinput.T g =ᵐ[volume] -rieszSecondL2RawOperator hL2 g) :
    ∃ T : Lp ℝ p (volume : Measure Vec3) →L[ℝ]
        Lp ℝ p (volume : Measure Vec3),
      ‖T‖ ≤ C ∧ ∀ (g : Vec3 → ℝ) (hg : MemLp g p volume),
        MemLp g (2 : ℝ≥0∞) volume →
      (fun x => T (hg.toLp g) x) =ᵐ[volume]
          (fun x => -rieszSecondL2RawOperator hL2 g x) := by
  let T := lpExtensionCore hp hinput
  refine ⟨T, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound T hC
    intro v
    exact lpExtensionCore_norm_le hp hinput v
  · intro g hg hg2
    calc
      (fun x => T (hg.toLp g) x) =ᵐ[volume]
          lpExtensionRepresentative (p := p) hp hinput g :=
        (lpExtensionRepresentative_ae_eq_core hp hinput hg).symm
      _ =ᵐ[volume] -rieszSecondL2RawOperator hL2 g :=
        (lpExtensionRepresentative_ae_eq_T hp hinput hg hg2).trans
          (hidentify hg hg2)
/-- The concrete double Riesz transform has a bounded completed extension for
every finite exponent strictly above one, agreeing with the negative raw L²
operator on the common Lᵖ and L² domain. -/
theorem riesz_second_all_exponents (s : ℝ) (hs : 1 < s) :
    letI : Fact (1 ≤ ENNReal.ofReal s) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hs.le⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin 3,
      ∃ T : Lp ℝ (ENNReal.ofReal s) (volume : Measure Vec3) →L[ℝ]
          Lp ℝ (ENNReal.ofReal s) (volume : Measure Vec3),
        ‖T‖ ≤ C ∧ ∀ (g : Vec3 → ℝ)
          (hg : MemLp g (ENNReal.ofReal s) volume),
          MemLp g 2 volume →
          (fun x => T (hg.toLp g) x) =ᵐ[volume]
            (fun x => -(rieszSecondL2RawOperator (rieszSecondL2Input i j) g x)) := by
  let : Fact (1 ≤ ENNReal.ofReal s) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hs.le⟩
  have hA₁ : 0 ≤ rieszSecondWeakTypeConstant := by
    unfold rieszSecondWeakTypeConstant
    have hC₂ : 0 ≤ rieszSecondKernelC₂ := rieszSecondKernelC₂_nonneg
    positivity
  rcases lt_trichotomy s 2 with hslt | hseq | hslt
  · let C : ℝ := rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 s ^ (1 / s)
    have hC : 0 ≤ C := by
      dsimp [C, rieszSecondInterpolationConstant]
      positivity
    refine ⟨C, hC, ?_⟩
    intro i j
    let hL2 : RieszSecondL2Input i j := rieszSecondL2Input i j
    let hweak := fun f hf hfi hf2 l hl => rieszSecondL2_weak_type i j f hf hfi hf2 l hl
    have houtput : ∀ {f : Vec3 → ℝ}, MemLp f (ENNReal.ofReal s) volume →
        MemLp f 2 volume →
        MemLp (-rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal s) volume := by
      intro f hf hf2
      exact (CKN.Core.Endgame.raw_rieszSecond_memLp_and_bound_of_weak
        hL2 hweak hA₁ hs hslt hf hf2).1.neg
    have hbound : ∀ {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal s) volume)
        (hf2 : MemLp f 2 volume),
        ‖(houtput hf hf2).toLp (-rieszSecondL2RawOperator hL2 f)‖ ≤
          C * ‖hf.toLp f‖ := by
      intro f hf hf2
      have hraw := CKN.Core.Endgame.raw_rieszSecond_memLp_and_bound_of_weak
        hL2 hweak hA₁ hs hslt hf hf2
      have hrawbound := CKN.Core.Endgame.raw_rieszSecond_toLp_bound_of_weak
        hL2 hweak hA₁ hs hslt hf hf2 hraw.1
      have hproof : houtput hf hf2 = hraw.1.neg := Subsingleton.elim _ _
      rw [hproof]
      calc
        ‖(hraw.1.neg).toLp (-rieszSecondL2RawOperator hL2 f)‖ =
            ‖hraw.1.toLp (rieszSecondL2RawOperator hL2 f)‖ := norm_toLp_neg hraw.1
        _ ≤ (rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 s ^ (1 / s)) *
              ‖hf.toLp f‖ := hrawbound
        _ = C * ‖hf.toLp f‖ := by rfl
    let hinput := negativeRawExtensionInput hL2 houtput hbound
    have hidentify : ∀ {f : Vec3 → ℝ}, MemLp f (ENNReal.ofReal s) volume →
        MemLp f 2 volume →
        hinput.T f =ᵐ[volume] -rieszSecondL2RawOperator hL2 f := by
      intro f hf hf2
      rfl
    exact negativeRawExtensionCore_producer ENNReal.ofReal_ne_top hL2 hC hinput hidentify
  · subst s
    let C : ℝ := 1
    have hC : 0 ≤ C := by norm_num [C]
    refine ⟨C, hC, ?_⟩
    intro i j
    let hL2 : RieszSecondL2Input i j := rieszSecondL2Input i j
    let hweak := fun f hf hfi hf2 l hl => rieszSecondL2_weak_type i j f hf hfi hf2 l hl
    let p : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ)
    have hpEq : p = (2 : ℝ≥0∞) := by norm_num [p]
    have houtput : ∀ {f : Vec3 → ℝ}, MemLp f p volume → MemLp f 2 volume →
        MemLp (-rieszSecondL2RawOperator hL2 f) p volume := by
      intro f hf hf2
      have hTf := (rieszSecondL2RawOperator_ae_eq hL2 hf2).trans
        (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 (hf2.toLp f))
      have hraw : MemLp (rieszSecondL2RawOperator hL2 f) 2 volume :=
        memLp_congr_ae hTf |>.2 (Lp.memLp (rieszSecondL2Extension hL2 (hf2.toLp f)))
      have hrawp : MemLp (rieszSecondL2RawOperator hL2 f) p volume := by
        simpa only [hpEq] using hraw
      exact hrawp.neg
    have hbound : ∀ {f : Vec3 → ℝ} (hf : MemLp f p volume)
        (hf2 : MemLp f 2 volume),
        ‖(houtput hf hf2).toLp (-rieszSecondL2RawOperator hL2 f)‖ ≤ C * ‖hf.toLp f‖ := by
      intro f hf hf2
      have hTf := (rieszSecondL2RawOperator_ae_eq hL2 hf2).trans
        (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 (hf2.toLp f))
      have hraw : MemLp (rieszSecondL2RawOperator hL2 f) 2 volume :=
        memLp_congr_ae hTf |>.2 (Lp.memLp (rieszSecondL2Extension hL2 (hf2.toLp f)))
      have hrawp : MemLp (rieszSecondL2RawOperator hL2 f) p volume := by
        simpa only [hpEq] using hraw
      have hproof : houtput hf hf2 = hrawp.neg := Subsingleton.elim _ _
      rw [hproof]
      have hrawL2 : hraw.toLp (rieszSecondL2RawOperator hL2 f) =
          rieszSecondL2Extension hL2 (hf2.toLp f) := by
        apply Lp.ext
        exact hraw.coeFn_toLp.trans hTf
      have hnorm := rieszSecondL2Extension_norm_le hL2 (hf2.toLp f)
      have hrawBound2 : lpNorm (rieszSecondL2RawOperator hL2 f) 2 volume ≤
          lpNorm f 2 volume := by
        calc
          lpNorm (rieszSecondL2RawOperator hL2 f) 2 volume =
              ‖hraw.toLp (rieszSecondL2RawOperator hL2 f)‖ := by
                rw [Lp.norm_toLp]
                rfl
          _ = ‖rieszSecondL2Extension hL2 (hf2.toLp f)‖ := by rw [hrawL2]
          _ ≤ ‖hf2.toLp f‖ := hnorm
          _ = lpNorm f 2 volume := by
            rw [Lp.norm_toLp]
            rfl
      have hrawBoundP : lpNorm (rieszSecondL2RawOperator hL2 f) p volume ≤
          lpNorm f p volume := by simpa only [hpEq] using hrawBound2
      calc
        ‖(hrawp.neg).toLp (-rieszSecondL2RawOperator hL2 f)‖ =
            ‖hrawp.toLp (rieszSecondL2RawOperator hL2 f)‖ := norm_toLp_neg hrawp
        _ = lpNorm (rieszSecondL2RawOperator hL2 f) p volume := by
          rw [Lp.norm_toLp]
          rfl
        _ ≤ lpNorm f p volume := hrawBoundP
        _ = ‖hf.toLp f‖ := by
          rw [Lp.norm_toLp]
          rfl
        _ = C * ‖hf.toLp f‖ := by simp [C]
    let hinput := negativeRawExtensionInput hL2 houtput hbound
    have hidentify : ∀ {f : Vec3 → ℝ}, MemLp f p volume → MemLp f 2 volume →
        hinput.T f =ᵐ[volume] -rieszSecondL2RawOperator hL2 f := by
      intro f hf hf2
      rfl
    have hp : p ≠ ∞ := by simp [p]
    exact negativeRawExtensionCore_producer hp hL2 hC hinput hidentify
  · have hs' : 2 < s := hslt
    let q : ℝ := Real.conjExponent s
    have hsden : 0 < s - 1 := by linarith only [hs, hs']
    have hq1 : 1 < q := by
      dsimp [q, Real.conjExponent]
      rw [lt_div_iff₀ hsden]
      linarith only [hsden]
    have hq2 : q < 2 := by
      dsimp [q, Real.conjExponent]
      rw [div_lt_iff₀ hsden]
      linarith only [hs']
    have hholder : s.HolderConjugate q := Real.HolderConjugate.conjExponent hs
    have hqp : q * (s - 1) = s := by
      dsimp [q, Real.conjExponent]
      field_simp [ne_of_gt hsden]
    let C : ℝ := rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q ^ (1 / q)
    have hC : 0 ≤ C := by
      dsimp [C, rieszSecondInterpolationConstant]
      positivity
    refine ⟨C, hC, ?_⟩
    intro i j
    let hL2 : RieszSecondL2Input i j := rieszSecondL2Input i j
    let hweak := fun f hf hfi hf2 l hl => rieszSecondL2_weak_type i j f hf hfi hf2 l hl
    have houtput : ∀ {f : Vec3 → ℝ}, MemLp f (ENNReal.ofReal s) volume →
        MemLp f 2 volume →
        MemLp (-rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal s) volume := by
      intro f hf hf2
      exact (raw_rieszSecond_memLp_of_duality hL2 hweak hs hs' hq1 hq2
        hholder hqp hf hf2).1.neg
    have hbound : ∀ {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal s) volume)
        (hf2 : MemLp f 2 volume),
        ‖(houtput hf hf2).toLp (-rieszSecondL2RawOperator hL2 f)‖ ≤
          C * ‖hf.toLp f‖ := by
      intro f hf hf2
      have hraw := raw_rieszSecond_memLp_of_duality hL2 hweak hs hs' hq1 hq2
        hholder hqp hf hf2
      have hproof : houtput hf hf2 = hraw.1.neg := Subsingleton.elim _ _
      rw [hproof]
      calc
        ‖(hraw.1.neg).toLp (-rieszSecondL2RawOperator hL2 f)‖ =
            ‖hraw.1.toLp (rieszSecondL2RawOperator hL2 f)‖ := norm_toLp_neg hraw.1
        _ = lpNorm (rieszSecondL2RawOperator hL2 f) (ENNReal.ofReal s) volume := by
          rw [Lp.norm_toLp, lpNorm]
        _ ≤ (rieszSecondInterpolationConstant rieszSecondWeakTypeConstant 1 q ^
              (1 / q)) * lpNorm f (ENNReal.ofReal s) volume := hraw.2
        _ = C * ‖hf.toLp f‖ := by
          rw [Lp.norm_toLp]
          rfl
    let hinput := negativeRawExtensionInput hL2 houtput hbound
    have hidentify : ∀ {f : Vec3 → ℝ}, MemLp f (ENNReal.ofReal s) volume →
        MemLp f 2 volume →
        hinput.T f =ᵐ[volume] -rieszSecondL2RawOperator hL2 f := by
      intro f hf hf2
      rfl
    exact negativeRawExtensionCore_producer ENNReal.ofReal_ne_top hL2 hC hinput hidentify

end CKN.Foundation.Euclidean
