/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ModelWord
public import LeanPool.GraphMinor.Surface.TopologyStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The upper half of the model surface as a disc

The sphere with holes around the points `3 i` of the real axis is cut along the graph of the height
function `hgt`:
its upper half consists of the points above the graph, together with the point at infinity. The
Cayley map turns the
unit disc into the closed upper half plane, and pushing up by the height gives the map `upE` from
the unit disc onto
the upper half. It is continuous and injective (`continuousOn_upE`, `injOn_upE`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

open scoped OnePoint

/-- The point of the plane with coordinates `x`, `y`. -/
noncomputable def pt (x y : ℝ) : EuclideanPlane := !₂[x, y]

@[simp] theorem pt_zero (x y : ℝ) : (pt x y) 0 = x := by simp [pt]
@[simp] theorem pt_one (x y : ℝ) : (pt x y) 1 = y := by simp [pt]

theorem pt_ext (u : EuclideanPlane) : pt (u 0) (u 1) = u := by
  ext i
  fin_cases i <;> simp

theorem continuous_pt : Continuous fun p : ℝ × ℝ => pt p.1 p.2 := by
  unfold pt
  apply continuous_induced_rng.mpr
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero]
    fun_prop
  · simp only [Fin.mk_one, Fin.isValue, Function.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    fun_prop

theorem norm_pt_sq (x y : ℝ) : ‖pt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

theorem dist_pt_sq (x y x' y' : ℝ) : dist (pt x y) (pt x' y') ^ 2 = (x - x') ^ 2 + (y - y') ^ 2
  := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem modelCentre_eq (i : ℕ) : modelCentre i = pt (3 * i) 0 := rfl

theorem modelMirror_pt (x y : ℝ) : modelMirror (pt x y) = pt x (-y) := by
  simp [modelMirror, pt]

/-- The height of the upper half circles above the real axis. -/
noncomputable def hgt (n : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range n, √(1 - (x - 3 * i) ^ 2)

theorem continuous_hgt (n : ℕ) : Continuous (hgt n) := by
  unfold hgt
  fun_prop

theorem hgt_nonneg (n : ℕ) (x : ℝ) : 0 ≤ hgt n x := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem hgt_ge (n : ℕ) (x : ℝ) {i : ℕ} (hi : i < n) : √(1 - (x - 3 * i) ^ 2) ≤ hgt n x :=
  Finset.single_le_sum (f := fun i : ℕ => √(1 - (x - 3 * i) ^ 2)) (fun _ _ => Real.sqrt_nonneg _)
    (Finset.mem_range.mpr hi)

theorem sqrt_eq_zero_of_far {x : ℝ} {i : ℕ} (h : 1 ≤ |x - 3 * i|) : √(1 - (x - 3 * i) ^ 2) = 0 := by
  refine Real.sqrt_eq_zero_of_nonpos ?_
  have := sq_abs (x - 3 * i)
  nlinarith

/-- Near the centre `k` only one term of the height is left. -/
theorem hgt_eq {n k : ℕ} (hk : k < n) {x : ℝ} (hx : |x - 3 * k| ≤ 1) : hgt n x = √(1 -
  (x - 3 * k) ^ 2) := by
  unfold hgt
  refine Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk) fun i _ hi
    => sqrt_eq_zero_of_far ?_
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  rcases lt_or_gt_of_ne hi with h | h
  · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [le_abs]
    left
    linarith
  · have : (k : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [le_abs]
    right
    linarith

/-- The height vanishes between the circles. -/
theorem hgt_eq_zero {n : ℕ} {x : ℝ} (h : ∀ i < n, 1 ≤ |x - 3 * i|) : hgt n x = 0 := by
  unfold hgt
  exact Finset.sum_eq_zero fun i hi => sqrt_eq_zero_of_far (h i (Finset.mem_range.mp hi))

/-- The Cayley map from the unit disc to the upper half plane. -/
noncomputable def cay (z : ℂ) : ℂ := Complex.I * (1 + z) / (1 - z)

/-- The inverse of the Cayley map. -/
noncomputable def cayI (w : ℂ) : ℂ := (w - Complex.I) / (w + Complex.I)

theorem cayI_cay {z : ℂ} (hz : z ≠ 1) : cayI (cay z) = z := by
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : cay z + Complex.I = 2 * Complex.I / (1 - z) := by
    unfold cay
    field_simp
    ring
  have h3 : cay z - Complex.I = 2 * Complex.I * z / (1 - z) := by
    unfold cay
    field_simp
    ring
  unfold cayI
  rw [h2, h3]
  field_simp

theorem cay_cayI {w : ℂ} (hw : w + Complex.I ≠ 0) : cayI w ≠ 1 ∧ cay (cayI w) = w := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h1 : 1 - cayI w = 2 * Complex.I / (w + Complex.I) := by
    unfold cayI
    field_simp
    ring
  have h3 : 1 - cayI w ≠ 0 := by
    rw [h1]
    exact div_ne_zero (mul_ne_zero h2 hI) hw
  refine ⟨fun h => h3 (by rw [h, sub_self]), ?_⟩
  have h4 : 1 + cayI w = 2 * w / (w + Complex.I) := by
    unfold cayI
    field_simp
    ring
  unfold cay
  rw [h1, h4]
  field_simp

theorem normSq_sub_I_add_I (w : ℂ) :
    Complex.normSq (w + Complex.I) - Complex.normSq (w - Complex.I) = 4 * w.im := by
  simp [Complex.normSq_apply]
  ring

theorem add_I_ne {w : ℂ} (hw : 0 ≤ w.im) : w + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cay_add_I_ne {z : ℂ} (hz : z ≠ 1) : cay z + Complex.I ≠ 0 := by
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have h2 : cay z + Complex.I = 2 * Complex.I / (1 - z) := by
    unfold cay
    field_simp
    ring
  rw [h2]
  exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) h1

theorem norm_cayI_le_iff {w : ℂ} (hw : w + Complex.I ≠ 0) : ‖cayI w‖ ≤ 1 ↔ 0 ≤ w.im := by
  have h0 : 0 < ‖w + Complex.I‖ := norm_pos_iff.mpr hw
  have e := normSq_sub_I_add_I w
  simp only [Complex.normSq_eq_norm_sq] at e
  unfold cayI
  rw [norm_div, div_le_one h0]
  constructor
  · intro h
    have : ‖w - Complex.I‖ ^ 2 ≤ ‖w + Complex.I‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith
  · intro h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0.le two_ne_zero).mp (by linarith)

theorem norm_cayI_eq_iff {w : ℂ} (hw : w + Complex.I ≠ 0) : ‖cayI w‖ = 1 ↔ w.im = 0 := by
  have h0 : 0 < ‖w + Complex.I‖ := norm_pos_iff.mpr hw
  have e := normSq_sub_I_add_I w
  simp only [Complex.normSq_eq_norm_sq] at e
  unfold cayI
  rw [norm_div, div_eq_one_iff_eq h0.ne']
  constructor
  · intro h
    rw [h] at e
    linarith
  · intro h
    have : ‖w - Complex.I‖ ^ 2 = ‖w + Complex.I‖ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) h0.le two_ne_zero).mp this

/-- The map from the unit disc onto the upper half of the model surface. -/
noncomputable def upE (n : ℕ) (z : ℂ) : OnePoint EuclideanPlane :=
  open Classical in if z = 1 then ∞ else ((pt (cay z).re ((cay z).im + hgt n
    (cay z).re) : EuclideanPlane) : OnePoint EuclideanPlane)

theorem upE_one (n : ℕ) : upE n 1 = ∞ := by simp [upE]

theorem upE_ne {n : ℕ} {z : ℂ} (hz : z ≠ 1) :
    upE n z = ((pt (cay z).re ((cay z).im + hgt n (cay z).re) : EuclideanPlane) : OnePoint
      EuclideanPlane) := by
  simp [upE, hz]

theorem cay_im_nonneg {z : ℂ} (hz : z ≠ 1) (hb : ‖z‖ ≤ 1) : 0 ≤ (cay z).im := by
  have h := cay_add_I_ne hz
  rw [← norm_cayI_le_iff h, cayI_cay hz]
  exact hb

theorem injOn_upE (n : ℕ) : InjOn (upE n) (closedBall 0 1) := by
  intro z _ z' _ he
  by_cases h : z = 1 <;> by_cases h' : z' = 1
  · rw [h, h']
  · rw [h, upE_one, upE_ne h'] at he
    exact absurd he (OnePoint.infty_ne_coe _)
  · rw [h', upE_one, upE_ne h] at he
    exact absurd he (OnePoint.coe_ne_infty _)
  · rw [upE_ne h, upE_ne h'] at he
    have e := OnePoint.coe_injective he
    have e1 := congrFun (congrArg (fun u : EuclideanPlane => (u : Fin 2 → ℝ)) e) 0
    have e2 := congrFun (congrArg (fun u : EuclideanPlane => (u : Fin 2 → ℝ)) e) 1
    simp only [pt_zero, pt_one] at e1 e2
    have e3 : cay z = cay z' := by
      apply Complex.ext e1
      rw [e1] at e2
      linarith
    rw [← cayI_cay h, ← cayI_cay h', e3]

theorem continuousOn_upE (n : ℕ) : ContinuousOn (upE n) (closedBall 0 1) := by
  intro z hz
  by_cases h : z = 1
  · subst h
    have hval : upE n 1 = ∞ := upE_one n
    rw [ContinuousWithinAt, hval]
    let P : ℂ → EuclideanPlane := fun z => pt (cay z).re ((cay z).im + hgt n (cay z).re)
    have key : Tendsto (fun z => ‖P z‖) (𝓝[closedBall 0 1 \ {1}] 1) atTop := by
      refine tendsto_atTop.mpr fun R => ?_
      have hδ : 0 < 1 / (|R| + 2) := by positivity
      have hmem : ball (1 : ℂ) (1 / (|R| + 2)) ∈ 𝓝[closedBall 0 1 \ {1}] (1 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ)
      filter_upwards [hmem, self_mem_nhdsWithin] with z hz hz'
      have hne : z ≠ 1 := hz'.2
      have hb : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz'.1
      have h1 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
      have h2 : ‖1 - z‖ < 1 / (|R| + 2) := by
        rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
        exact hz
      have h3 : 1 / (|R| + 2) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        linarith [abs_nonneg R]
      have h4 : 1 ≤ ‖1 + z‖ := by
        have : ‖(2 : ℂ)‖ ≤ ‖1 + z‖ + ‖1 - z‖ := by
          have e : (2 : ℂ) = (1 + z) + (1 - z) := by ring
          rw [e]
          exact norm_add_le _ _
        simp at this
        linarith
      have h5 : ‖cay z‖ = ‖1 + z‖ / ‖1 - z‖ := by
        simp [cay]
      have h6 : |R| + 2 ≤ ‖cay z‖ := by
        rw [h5, le_div_iff₀ h1]
        have : (|R| + 2) * ‖1 - z‖ < 1 := by
          rw [lt_div_iff₀ (by positivity)] at h2
          linarith
        linarith
      have h7 : ‖cay z‖ ^ 2 ≤ ‖P z‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, norm_pt_sq]
        nlinarith [hgt_nonneg n (cay z).re, cay_im_nonneg hne hb]
      have h8 : ‖cay z‖ ≤ ‖P z‖ := (pow_le_pow_iff_left₀ (norm_nonneg _)
        (norm_nonneg _) two_ne_zero).mp h7
      linarith [le_abs_self R]
    have h1 : Tendsto P (𝓝[closedBall 0 1 \ {1}] 1) (coclosedCompact EuclideanPlane) := by
      rw [coclosedCompact_eq_cocompact]
      rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
      exact tendsto_comap_iff.mpr key
    have h2 : Tendsto (upE n) (𝓝[closedBall 0 1 \ {1}] 1) (𝓝 ∞) := by
      refine (OnePoint.tendsto_coe_infty.comp h1).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (upE_ne hz.2).symm
    have h3 : closedBall (0 : ℂ) 1 = insert 1 (closedBall 0 1 \ {1}) := by
      ext w
      by_cases hw : w = 1
      · subst hw
        simp
      · simp
    rw [h3, nhdsWithin_insert]
    refine Tendsto.sup ?_ h2
    rw [tendsto_pure_left]
    intro s hs
    rw [hval]
    exact mem_of_mem_nhds hs
  · have h1 : ContinuousAt cay z := by
      unfold cay
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (sub_ne_zero.mpr (Ne.symm h))
    have h2 : ContinuousAt (fun z : ℂ => ((pt (cay z).re ((cay z).im + hgt n
      (cay z).re) : EuclideanPlane) :
        OnePoint EuclideanPlane)) z := by
      refine OnePoint.continuous_coe.continuousAt.comp ?_
      refine continuous_pt.continuousAt.comp (f := fun z => ((cay z).re,
        (cay z).im + hgt n (cay z).re)) ?_
      have hr : ContinuousAt (fun z => (cay z).re) z := Complex.continuous_re.continuousAt.comp h1
      have hi : ContinuousAt (fun z => (cay z).im) z := Complex.continuous_im.continuousAt.comp h1
      exact hr.prodMk (hi.add ((continuous_hgt n).continuousAt.comp hr))
    refine (h2.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ne.mem_nhds h] with w hw
    exact (upE_ne hw).symm

/-- A point above the height function is a value of `upE`. -/
theorem exists_upE {n : ℕ} {x y : ℝ} (h : hgt n x ≤ y) :
    ∃ z ∈ closedBall (0 : ℂ) 1, upE n z = ((pt x y : EuclideanPlane) : OnePoint EuclideanPlane)
      := by
  let w : ℂ := ⟨x, y - hgt n x⟩
  have hw : 0 ≤ w.im := sub_nonneg.mpr h
  have h1 := add_I_ne hw
  obtain ⟨h2, h3⟩ := cay_cayI h1
  refine ⟨cayI w, mem_closedBall_zero_iff.mpr ((norm_cayI_le_iff h1).mpr hw), ?_⟩
  rw [upE_ne h2, h3]
  simp [w]

/-- The values of `upE` other than infinity lie above the height function. -/
theorem upE_above {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) :
    hgt n (cay z).re ≤ (cay z).im + hgt n (cay z).re := by
  linarith [cay_im_nonneg hne hz]

/-- The angle of the point `s` of the real axis on the unit circle. -/
noncomputable def angT (s : ℝ) : ℝ := Real.pi + 2 * Real.arctan s

theorem angT_mem (s : ℝ) : 0 < angT s ∧ angT s < 2 * Real.pi := by
  have h1 := Real.arctan_lt_pi_div_two s
  have h2 := Real.neg_pi_div_two_lt_arctan s
  unfold angT
  constructor <;> linarith

theorem continuous_angT : Continuous angT := by
  unfold angT
  fun_prop

theorem strictMono_angT : StrictMono angT := fun a b h => by
  have := Real.arctan_strictMono h
  unfold angT
  linarith

/-- The unit circle minus `1` and the real axis. -/
theorem cay_cis (s : ℝ) : cis' (angT s) ≠ 1 ∧ cay (cis' (angT s)) = (s : ℂ) := by
  have h1 : cis' (angT s) = cayI (s : ℂ) := by
    set φ := Real.arctan s with hφ
    have hc : 0 < Real.cos φ := Real.cos_arctan_pos s
    have ht : Real.tan φ = s := Real.tan_arctan s
    have hs : s = Real.sin φ / Real.cos φ := by rw [← ht, Real.tan_eq_sin_div_cos]
    have hne : ((Real.cos φ : ℂ)) ≠ 0 := by exact_mod_cast hc.ne'
    have hne2 : (s : ℂ) + Complex.I ≠ 0 := add_I_ne (by simp)
    have e1 : cis' (angT s) = - (Complex.exp (φ * Complex.I)) ^ 2 := by
      simp only [cis', angT, ← hφ]
      push_cast
      rw [← Complex.exp_nat_mul, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      push_cast
      ring_nf
    have e2 : Complex.exp (φ * Complex.I) = Real.cos φ + Real.sin φ * Complex.I := by
      rw [Complex.exp_mul_I]
      push_cast
      ring_nf
    unfold cayI
    rw [eq_div_iff hne2, e1, e2]
    have e3 : (s : ℂ) = Real.sin φ / Real.cos φ := by rw [hs]; push_cast; rfl
    have hsc : (Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq φ
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    generalize (Real.sin φ : ℂ) = si at *
    generalize (Real.cos φ : ℂ) = c at *
    have key : -(c + si * Complex.I) ^ 2 * (si + c * Complex.I) = si - c * Complex.I := by
      linear_combination (si - c * Complex.I) * hsc +
        (-2 * c ^ 2 * si - si ^ 3 - c * si ^ 2 * Complex.I) * hI
    have e4 : (s : ℂ) + Complex.I = (si + c * Complex.I) / c := by
      rw [e3]
      field_simp
    have e5 : (s : ℂ) - Complex.I = (si - c * Complex.I) / c := by
      rw [e3]
      field_simp
    rw [e4, e5, ← key]
    field_simp
  have h2 := cay_cayI (w := (s : ℂ)) (add_I_ne (by simp))
  rw [h1]
  exact h2

end GraphMinor.Surface
