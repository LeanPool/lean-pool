/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.LocalEllipticity
public import LeanPool.HighContrastHomogenization.Analytic.WeightedEnergy
public import LeanPool.HighContrastHomogenization.Analytic.WeakPairing

/-!
# High-contrast homogenization: Analytic.ClassHonesty

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coefficient-Sobolev classes have finite weighted energy

`MemH1a`, `MemH1a0` and `MemH1sLoc` — the spaces `H¹_a(V)`, `H¹_{a,0}(V)` and
`H¹_{s,loc}(ℝ^d)` of `s.introduction` — are approximability
conditions: each carries a sequence of smooth functions whose `H¹_s` distance to
the pair tends to `0`.  Eventual finiteness of that distance together with
finiteness of the energy of one smooth approximant gives finiteness of the
weighted energy of the weak gradient itself.

The module first collects the finiteness facts for the *unweighted* energy of a
continuous field — on a bounded set, on an arbitrary set when the field has
compact support, and across the triangle inequality in both directions — and
then feeds them through the two-sided energy comparison to the three classes.

The domain hypotheses differ between the classes, and the difference is real.
`H¹_{a,0}(V)` needs no hypothesis on `V`, its approximants being compactly
supported inside `V`.  `H¹_a(V)` needs `V` bounded: its approximants are
globally smooth but not compactly supported, so nothing bounds their gradients
on an unbounded `V`, and without a hypothesis on `V` the conclusion is false.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A continuous field has finite unweighted energy on a bounded set. -/
theorem lintegral_ofReal_vecNormSq_ne_top_of_isBounded {V : Set (Vec d)}
    (hV : Bornology.IsBounded V) {G : Vec d → Vec d} (hG : Continuous G) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume) ≠ ⊤ := by
  have hcl : IsCompact (closure V) := hV.isCompact_closure
  have hcont : Continuous fun x => vecNormSq (G x) := by
    simp only [vecNormSq, vecDot]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hG).mul ((continuous_apply i).comp hG)
  obtain ⟨C, hC⟩ := hcl.exists_bound_of_continuousOn hcont.continuousOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * volume V) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV.measure_lt_top.ne
  · rw [← setLIntegral_const V (ENNReal.ofReal C)]
    refine lintegral_mono_ae ?_
    have hcls : ∀ᵐ x ∂(volume.restrict (closure V) : Measure (Vec d)),
        x ∈ closure V := ae_restrict_mem isClosed_closure.measurableSet
    have hmem : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)), x ∈ closure V :=
      hcls.filter_mono
        (ae_mono (Measure.restrict_mono subset_closure le_rfl))
    filter_upwards [hmem] with x hx
    exact ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx))

/-- A continuous field with compact support has finite unweighted energy on
every set. -/
theorem lintegral_ofReal_vecNormSq_ne_top_of_hasCompactSupport {V : Set (Vec d)}
    {G : Vec d → Vec d} (hG : Continuous G) (hGs : HasCompactSupport G) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume) ≠ ⊤ := by
  classical
  have hK : IsCompact (tsupport G) := hGs
  have hcont : Continuous fun x => vecNormSq (G x) := by
    simp only [vecNormSq, vecDot]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hG).mul ((continuous_apply i).comp hG)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hpt : ∀ x, ENNReal.ofReal (vecNormSq (G x)) ≤
      (tsupport G).indicator (fun _ => ENNReal.ofReal C) x := by
    intro x
    by_cases hx : x ∈ tsupport G
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx))
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp [vecNormSq, vecDot]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * volume (tsupport G)) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne
  · calc (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume)
        ≤ ∫⁻ x, ENNReal.ofReal (vecNormSq (G x)) ∂volume :=
          setLIntegral_le_lintegral V _
      _ ≤ ∫⁻ x, (tsupport G).indicator (fun _ => ENNReal.ofReal C) x ∂volume :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * volume (tsupport G) := by
          rw [lintegral_indicator (isClosed_tsupport G).measurableSet,
            setLIntegral_const]

/-- The triangle step: if `G` has finite unweighted energy and `G - H` has
finite unweighted energy, then so does `H`. -/
theorem lintegral_ofReal_vecNormSq_ne_top_of_sub {V : Set (Vec d)}
    {G H : Vec d → Vec d}
    (hGmeas : AEMeasurable (fun x => ENNReal.ofReal (vecNormSq (G x)))
      (volume.restrict V))
    (hG : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume) ≠ ⊤)
    (hD : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x - H x)) ∂volume) ≠ ⊤) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (H x)) ∂volume) ≠ ⊤ := by
  have hpt : ∀ x : Vec d, ENNReal.ofReal (vecNormSq (H x)) ≤
      2 * ENNReal.ofReal (vecNormSq (G x)) +
        2 * ENNReal.ofReal (vecNormSq (G x - H x)) := by
    intro x
    have hid : G x - (G x - H x) = H x := by funext i; simp
    have hle : vecNormSq (H x) ≤
        2 * vecNormSq (G x) + 2 * vecNormSq (G x - H x) := by
      have h := vecNormSq_sub_le (G x) (G x - H x)
      rw [hid] at h
      linarith only [h]
    have hnn1 : (0 : ℝ) ≤ 2 * vecNormSq (G x) := by
      linarith only [vecNormSq_nonneg (G x)]
    have hnn2 : (0 : ℝ) ≤ 2 * vecNormSq (G x - H x) := by
      linarith only [vecNormSq_nonneg (G x - H x)]
    calc ENNReal.ofReal (vecNormSq (H x))
        ≤ ENNReal.ofReal (2 * vecNormSq (G x) + 2 * vecNormSq (G x - H x)) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (2 * vecNormSq (G x)) +
            ENNReal.ofReal (2 * vecNormSq (G x - H x)) :=
          ENNReal.ofReal_add hnn1 hnn2
      _ = 2 * ENNReal.ofReal (vecNormSq (G x)) +
            2 * ENNReal.ofReal (vecNormSq (G x - H x)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left' (hGmeas.const_mul 2),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) hG, ENNReal.mul_ne_top (by norm_num) hD⟩

/-- The mirror triangle step: if `H` has finite unweighted energy and `G - H`
has finite unweighted energy, then so does `G`. -/
theorem lintegral_ofReal_vecNormSq_ne_top_of_add {V : Set (Vec d)}
    {G H : Vec d → Vec d}
    (hHmeas : AEMeasurable (fun x => ENNReal.ofReal (vecNormSq (H x)))
      (volume.restrict V))
    (hH : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (H x)) ∂volume) ≠ ⊤)
    (hD : (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x - H x)) ∂volume) ≠ ⊤) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume) ≠ ⊤ := by
  have hpt : ∀ x : Vec d, ENNReal.ofReal (vecNormSq (G x)) ≤
      2 * ENNReal.ofReal (vecNormSq (H x)) +
        2 * ENNReal.ofReal (vecNormSq (G x - H x)) := by
    intro x
    have hid : H x + (G x - H x) = G x := by funext i; simp
    have hle : vecNormSq (G x) ≤
        2 * vecNormSq (H x) + 2 * vecNormSq (G x - H x) := by
      have h := vecNormSq_add_le (H x) (G x - H x)
      rw [hid] at h
      linarith only [h]
    have hnn1 : (0 : ℝ) ≤ 2 * vecNormSq (H x) := by
      linarith only [vecNormSq_nonneg (H x)]
    have hnn2 : (0 : ℝ) ≤ 2 * vecNormSq (G x - H x) := by
      linarith only [vecNormSq_nonneg (G x - H x)]
    calc ENNReal.ofReal (vecNormSq (G x))
        ≤ ENNReal.ofReal (2 * vecNormSq (H x) + 2 * vecNormSq (G x - H x)) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (2 * vecNormSq (H x)) +
            ENNReal.ofReal (2 * vecNormSq (G x - H x)) :=
          ENNReal.ofReal_add hnn1 hnn2
      _ = 2 * ENNReal.ofReal (vecNormSq (H x)) +
            2 * ENNReal.ofReal (vecNormSq (G x - H x)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left' (hHmeas.const_mul 2),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) hH, ENNReal.mul_ne_top (by norm_num) hD⟩

/-- An essentially bounded field has finite unweighted energy on a bounded
set. -/
theorem lintegral_ofReal_vecNormSq_ne_top_of_ae_bounded {V : Set (Vec d)}
    (hVb : Bornology.IsBounded V) {G : Vec d → Vec d} {L : ℝ}
    (hG : ∀ᵐ x ∂(volume.restrict V : Measure (Vec d)), vecNormSq (G x) ≤ L) :
    (∫⁻ x in V, ENNReal.ofReal (vecNormSq (G x)) ∂volume) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal L * volume V) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVb.measure_lt_top.ne
  · rw [← setLIntegral_const V (ENNReal.ofReal L)]
    refine lintegral_mono_ae ?_
    filter_upwards [hG] with x hx
    exact ENNReal.ofReal_le_ofReal hx

/-- The essential bound of the Dirichlet clause is stated through the Euclidean
norm; this is its squared form. -/
theorem vecNormSq_le_sq_of_sqrt_le {x : Vec d} {L : ℝ}
    (h : Real.sqrt (vecNormSq x) ≤ L) : vecNormSq x ≤ L ^ 2 := by
  calc vecNormSq x = Real.sqrt (vecNormSq x) ^ 2 :=
        (Real.sq_sqrt (vecNormSq_nonneg x)).symm
    _ ≤ L ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- Along a sequence whose `H¹_s` distance to the pair tends to `0`, some
approximant has finite `H¹_s` distance. -/
theorem exists_sEnergyOn_sub_ne_top {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {v : ℕ → Vec d → ℝ}
    (htend : _root_.Filter.Tendsto
      (fun n => h1sNormSqOn b V (fun x => v n x - u x)
        (fun x => smoothGrad (v n) x - Du x)) _root_.Filter.atTop (nhds 0)) :
    ∃ n : ℕ, sEnergyOn b V (fun x => smoothGrad (v n) x - Du x) ≠ ⊤ := by
  obtain ⟨n, hn⟩ :=
    (htend.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)).exists
  refine ⟨n, ne_top_of_lt (lt_of_le_of_lt ?_ hn)⟩
  simp only [h1sNormSqOn]
  exact le_add_self

/-- **The `H¹_a(V)` class is honest on a bounded `V`**: its weak gradient has
finite weighted energy.

Hypotheses used, in full: the coefficient class hypothesis `0 < lam`, `hell`;
and `V` bounded.  Boundedness of `V` is genuinely needed: the approximants of
`MemH1a` are globally smooth but not compactly supported, so nothing bounds
their gradients on an unbounded `V`. -/
theorem sEnergyOn_ne_top_of_memH1a {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V) {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) :
    sEnergyOn b V Du ≠ ⊤ := by
  obtain ⟨-, -, v, hv, htend, -⟩ := hu
  obtain ⟨n, hn⟩ := exists_sEnergyOn_sub_ne_top htend
  have hgc : Continuous (smoothGrad (v n)) := continuous_smoothGrad (hv n)
  refine (sEnergyOn_ne_top_iff hlam hell Du).2 ?_
  refine lintegral_ofReal_vecNormSq_ne_top_of_sub
    (G := smoothGrad (v n)) (H := Du) ?_
    (lintegral_ofReal_vecNormSq_ne_top_of_isBounded hVb hgc)
    ((sEnergyOn_ne_top_iff hlam hell _).1 hn)
  refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
  simp only [vecNormSq, vecDot]
  exact Finset.measurable_sum _ fun i _ =>
    (((continuous_apply i).comp hgc).measurable).mul
      (((continuous_apply i).comp hgc).measurable)

/-- A compactly supported smooth approximant is in particular a globally smooth
one: `H¹_{a,0}(V) ⊆ H¹_a(V)`. -/
theorem memH1a_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) : MemH1a b V u Du := by
  obtain ⟨hmeas, hw, v, hv, h1, h2⟩ := hu
  exact ⟨hmeas, hw, v, fun n => (hv n).contDiff, h1, h2⟩

/-- **The `H¹_{a,0}(V)` class is honest on an arbitrary `V`**: the approximants
are compactly supported inside `V`, so no boundedness of `V` is needed. -/
theorem sEnergyOn_ne_top_of_memH1a0 {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a0 b V u Du) :
    sEnergyOn b V Du ≠ ⊤ := by
  obtain ⟨-, -, v, hv, htend, -⟩ := hu
  obtain ⟨n, hn⟩ := exists_sEnergyOn_sub_ne_top htend
  have hgc : Continuous (smoothGrad (v n)) := continuous_smoothGrad (hv n).contDiff
  have hgs : HasCompactSupport (smoothGrad (v n)) := by
    refine HasCompactSupport.intro (hv n).hasCompactSupport ?_
    intro x hx
    exact smoothGrad_eq_zero_of_notMem_tsupport hx
  refine (sEnergyOn_ne_top_iff hlam hell Du).2 ?_
  refine lintegral_ofReal_vecNormSq_ne_top_of_sub
    (G := smoothGrad (v n)) (H := Du) ?_
    (lintegral_ofReal_vecNormSq_ne_top_of_hasCompactSupport hgc hgs)
    ((sEnergyOn_ne_top_iff hlam hell _).1 hn)
  refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
  simp only [vecNormSq, vecDot]
  exact Finset.measurable_sum _ fun i _ =>
    (((continuous_apply i).comp hgc).measurable).mul
      (((continuous_apply i).comp hgc).measurable)

/-- Centered Euclidean balls are bounded. -/
theorem isBounded_euclideanBall (d : ℕ) {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (euclideanBall d R) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, fun x hx => ?_⟩
  have hx' : vecNormSq x < R ^ 2 := by
    simpa [euclideanBall, euclideanBallAt] using hx
  refine Metric.mem_closedBall.2 ?_
  rw [dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg hR.le).2 fun i => ?_
  have hi : x i ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x i
  have : x i ^ 2 ≤ R ^ 2 := le_of_lt (lt_of_le_of_lt hi hx')
  rw [Real.norm_eq_abs]
  nlinarith only [abs_nonneg (x i), sq_abs (x i), this, hR.le]

/-- **The `H¹_{s,loc}(ℝ^d)` class is honest**: on every centered Euclidean ball,
the weak gradient has finite weighted energy, with the ball's own ellipticity
constants. -/
theorem sEnergyOn_ne_top_of_memH1sLoc {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d} (hv : MemH1sLoc b v Dv) {R : ℝ}
    (hR : 0 < R) :
    sEnergyOn b (euclideanBall d R) Dv ≠ ⊤ := by
  obtain ⟨lam, Lam, hlam, -, hell⟩ :=
    hb.exists_ae_isEllipticMatrix_euclideanBall hR
  obtain ⟨-, w, hw, htend⟩ := hv.2 R hR
  obtain ⟨n, hn⟩ := exists_sEnergyOn_sub_ne_top htend
  have hgc : Continuous (smoothGrad (w n)) := continuous_smoothGrad (hw n)
  refine (sEnergyOn_ne_top_iff_restrict (Lam := Lam) hlam hell Dv).2 ?_
  refine lintegral_ofReal_vecNormSq_ne_top_of_sub
    (G := smoothGrad (w n)) (H := Dv) ?_
    (lintegral_ofReal_vecNormSq_ne_top_of_isBounded
      (isBounded_euclideanBall d hR) hgc)
    ((sEnergyOn_ne_top_iff_restrict (Lam := Lam) hlam hell _).1 hn)
  refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
  simp only [vecNormSq, vecDot]
  exact Finset.measurable_sum _ fun i _ =>
    (((continuous_apply i).comp hgc).measurable).mul
      (((continuous_apply i).comp hgc).measurable)

end

end HighContrast
end HCPolySupport
