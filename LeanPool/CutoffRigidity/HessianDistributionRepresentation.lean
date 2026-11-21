/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorLocalization
public import LeanPool.CutoffRigidity.DenseRieszRepresentation

/-! # Actual L² representations of bounded second-derivative distributions

Compact smooth test functions form a genuine dense submodule of actual
Lebesgue L². Mollified Hessian estimates and L² approximation bound the
second-derivative distribution; actual Riesz representation then constructs
its L² representative. No weak regularity is assumed in this construction.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual C³ compact functions satisfy twice-coordinate IBP under Lebesgue measure. -/
theorem compact_twice_coordinate_ibp {f ψ : E → ℝ}
    (hf : ContDiff ℝ 3 f) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin d) :
    (∫ x, f x * coordinateDerivative j (coordinateDerivative i ψ) x) =
      ∫ x, coordinateDerivative j (coordinateDerivative i f) x * ψ x := by
  let V : E → ℝ := fun _ => 0
  have hV : ContDiff ℝ 2 V := contDiff_const
  have hμ : gibbsMeasure volume V = volume := by simp [gibbsMeasure, V]
  have hD0 (a : Fin d) (x : E) : coordinateDerivative a V x = 0 := by simp [coordinateDerivative, V]
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have h1 := compact_directional_gibbs_ibp hV (hψ.of_le (by norm_num))
    (c1_coordinateDerivative_of_c2 hf2 i) hψc j
  have h2 := compact_directional_gibbs_ibp hV
    (c1_coordinateDerivative_of_c2 hψ2 j) (hf.of_le (by norm_num))
    (hψc.fderiv_apply ℝ (EuclideanSpace.single j 1)) i
  simp only [coordinateWeightedAdjoint, hD0, mul_zero, sub_zero, hμ] at h1 h2
  simp_rw [coordinateDerivative_commute hψ2 i j] at h2
  rw [h2, neg_neg] at h1
  simpa only [mul_comm] using h1.symm

/-- Actual second derivatives of compact C³ functions lie in Lebesgue L². -/
theorem compact_second_coordinate_memLp {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) (i j : Fin d) :
    MemLp (coordinateDerivative j (coordinateDerivative i f)) 2 volume := by
  have hdi : ContDiff ℝ 2 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hc := (c1_coordinateDerivative_of_c2 hdi j).continuous
  exact hc.memLp_of_hasCompactSupport
    ((hfc.fderiv_apply ℝ (EuclideanSpace.single i 1)).fderiv_apply ℝ (EuclideanSpace.single j 1))

/-- A component's genuine L² norm is bounded by the full actual Hessian energy. -/
theorem compact_second_coordinate_norm_sq_le {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) (i j : Fin d) :
    ‖(compact_second_coordinate_memLp hf hfc i j).toLp
      (coordinateDerivative j (coordinateDerivative i f))‖ ^ 2 ≤
      ∫ x, ∑ a : Fin d, ∑ b : Fin d, (coordinateDerivative b (coordinateDerivative a f) x) ^ 2 := by
  rw [norm_toLp_sq]
  have hsum : Integrable (fun x => ∑ a : Fin d, ∑ b : Fin d,
      (coordinateDerivative b (coordinateDerivative a f) x) ^ 2) volume := by
    apply integrable_finsetSum
    intro a ha
    apply integrable_finsetSum
    intro b hb
    exact (compact_second_coordinate_memLp hf hfc a b).integrable_sq
  apply integral_mono (compact_second_coordinate_memLp hf hfc i j).integrable_sq hsum
  intro x
  calc
    _ ≤ ∑ b : Fin d, (coordinateDerivative b (coordinateDerivative i f) x) ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
      (f := fun a : Fin d => ∑ b : Fin d, (coordinateDerivative b (coordinateDerivative a f) x) ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)

/-- The actual quantitative mollifier estimate gives genuine L² convergence. -/
theorem mollified_toL2_tendsto_of_translation_bound {w : E → ℝ}
    (hwm : Measurable w) (hw : MemLp w 2 volume) (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (w (x + h) - w x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    Tendsto (fun n =>
      (bumpMollification_memLp_of_translation_bound (euclideanMollifierBump (differenceStep n)
        (differenceStep_pos n))
        hwm hw C hC htrans).toLp
          (bumpMollification (euclideanMollifierBump (differenceStep n) (differenceStep_pos n)) w))
      atTop (𝓝 (hw.toLp w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (n : ℕ) := bumpMollification_L2_dist_le_of_translation_bound
    (euclideanMollifierBump (differenceStep n) (differenceStep_pos n)) hwm hw C hC htrans
  have hlim : Tendsto (fun n => differenceStep n * C) atTop (𝓝 0) := by
    simpa using differenceStep_tendsto_zero.mul_const C
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

/-- Actual distributional second derivatives are bounded on compact C³ tests
by the proved mollified Hessian estimate and actual L² mollifier convergence. -/
theorem bounded_second_derivative_distribution
    {w F : E → ℝ} (hwm : Measurable w) (hw : MemLp w 2 volume) (hwc : HasCompactSupport w)
    (hFm : Measurable F) (hF : MemLp F 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (w (x + h) - w x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    |∫ x, w x * coordinateDerivative j (coordinateDerivative i ψ) x| ≤
      ‖hF.toLp F‖ * ‖(hψ.continuous.memLp_of_hasCompactSupport hψc : MemLp ψ 2 volume).toLp ψ‖ := by
  let φ (n : ℕ) : ContDiffBump (0 : E) := euclideanMollifierBump (differenceStep n)
    (differenceStep_pos n)
  let wn (n : ℕ) := bumpMollification (φ n) w
  have hwn (n : ℕ) : ContDiff ℝ 3 (wn n) :=
    (bumpMollification_contDiff (φ n) (hw.locallyIntegrable (by norm_num))).of_le (by norm_num)
  have hwnc (n : ℕ) : HasCompactSupport (wn n) := bumpMollification_hasCompactSupport (φ n) hwc
  have hwnLp (n : ℕ) : MemLp (wn n) 2 volume :=
    bumpMollification_memLp_of_translation_bound (φ n) hwm hw C hC htrans
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hDψLp := compact_second_coordinate_memLp hψ hψc i j
  have hDwnNorm (n : ℕ) : ‖(compact_second_coordinate_memLp (hwn n) (hwnc n) i j).toLp
      (coordinateDerivative j (coordinateDerivative i (wn n)))‖ ≤ ‖hF.toLp F‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    apply (compact_second_coordinate_norm_sq_le (hwn n) (hwnc n) i j).trans
    rw [norm_toLp_sq]
    exact mollified_distributional_hessian_energy_le (hw.locallyIntegrable
      (by norm_num)) hwc hFm hF heq (φ n)
  have hb (n : ℕ) : |∫ x, wn n x * coordinateDerivative j (coordinateDerivative i ψ) x| ≤
      ‖hF.toLp F‖ * ‖hψLp.toLp ψ‖ := by
    rw [compact_twice_coordinate_ibp (hwn n) hψ hψc i j,
      ← real_inner_toLp (compact_second_coordinate_memLp (hwn n) (hwnc n) i j) hψLp]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hDwnNorm n) (norm_nonneg
      _))
  have hconv := mollified_toL2_tendsto_of_translation_bound hwm hw C hC htrans
  have hscalar : Tendsto (fun n => ∫ x, wn n x * coordinateDerivative j (coordinateDerivative i ψ)
    x)
      atTop (𝓝 (∫ x, w x * coordinateDerivative j (coordinateDerivative i ψ) x)) := by
    have hh : Tendsto (fun n => inner ℝ ((hwnLp n).toLp (wn n)) (hDψLp.toLp _)) atTop
        (𝓝 (inner ℝ (hw.toLp w) (hDψLp.toLp _))) :=
      hconv.inner (tendsto_const_nhds (x := hDψLp.toLp _))
    simpa only [real_inner_toLp] using hh
  exact le_of_tendsto hscalar.abs (Filter.Eventually.of_forall hb)

/-- Actual Lebesgue L² classes with compact C³ test representatives. -/
@[expose] noncomputable def compactEuclideanTestSpace : Submodule ℝ (E →₂[volume] ℝ) where
  carrier := {u | ∃ ψ : E → ℝ, ContDiff ℝ 3 ψ ∧ HasCompactSupport ψ ∧ ψ =ᵐ[volume] u}
  zero_mem' := ⟨fun _ => 0, contDiff_const, by simp [HasCompactSupport], (Lp.coeFn_zero _ _ _).symm⟩
  add_mem' := by
    rintro u v ⟨f, hf, hfc, haef⟩ ⟨g, hg, hgc, haeg⟩
    refine ⟨fun x => f x + g x, hf.add hg, ?_, ?_⟩
    · simpa only [Pi.add_def] using hfc.add hgc
    · filter_upwards [haef, haeg, Lp.coeFn_add u v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  smul_mem' := by
    rintro r u ⟨f, hf, hfc, haef⟩
    refine ⟨fun x => r * f x, contDiff_const.mul hf, ?_, ?_⟩
    · exact hfc.comp_left (g := fun t : ℝ => r * t) (by simp)
    · filter_upwards [haef, Lp.coeFn_smul r u] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- Density is the actual smooth compact approximation theorem in L². -/
theorem compactEuclideanTestSpace_dense : Dense (compactEuclideanTestSpace (d
  := d) : Set (E →₂[volume] ℝ)) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure E)) (F := ℝ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono
  rintro u ⟨f, hae, hfc, hf⟩
  exact ⟨f, hf.of_le (by norm_num), hfc, hae.symm⟩

/-- Full support provides unique actual continuous test representatives. -/
@[expose] noncomputable def compactEuclideanTestRep (u : compactEuclideanTestSpace (d
  := d)) : E → ℝ :=
  Classical.choose u.property

theorem compactEuclideanTestRep_spec (u : compactEuclideanTestSpace (d := d)) :
    ContDiff ℝ 3 (compactEuclideanTestRep u) ∧ HasCompactSupport (compactEuclideanTestRep u) ∧
      compactEuclideanTestRep u =ᵐ[volume] (u : E →₂[volume] ℝ) := Classical.choose_spec u.property

theorem compactEuclideanTestRep_unique {ψ : E → ℝ} (u : compactEuclideanTestSpace (d := d))
    (hψ : Continuous ψ) (hae : ψ =ᵐ[volume] (u : E →₂[volume] ℝ)) : ψ = compactEuclideanTestRep u :=
  Measure.eq_of_ae_eq (hae.trans (compactEuclideanTestRep_spec u).2.2.symm)
    hψ (compactEuclideanTestRep_spec u).1.continuous

/-- The unique compact test representative is linear as an actual function. -/
@[expose] noncomputable def compactEuclideanTestRepLinear :
    compactEuclideanTestSpace (d := d) →ₗ[ℝ] (E → ℝ) where
  toFun := compactEuclideanTestRep
  map_add' := by
    intro u v
    apply Eq.symm
    apply compactEuclideanTestRep_unique (u + v)
    · exact (compactEuclideanTestRep_spec u).1.continuous.add (compactEuclideanTestRep_spec
      v).1.continuous
    · filter_upwards [(compactEuclideanTestRep_spec u).2.2, (compactEuclideanTestRep_spec v).2.2,
        Lp.coeFn_add (u : E →₂[volume] ℝ) v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  map_smul' := by
    intro r u
    apply Eq.symm
    apply compactEuclideanTestRep_unique (r • u)
    · exact continuous_const.mul (compactEuclideanTestRep_spec u).1.continuous
    · filter_upwards [(compactEuclideanTestRep_spec u).2.2,
        Lp.coeFn_smul r (u : E →₂[volume] ℝ)] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- The actual test representative determines the same L² element. -/
theorem compactEuclideanTestRep_toLp (u : compactEuclideanTestSpace (d := d)) :
    ((compactEuclideanTestRep_spec u).1.continuous.memLp_of_hasCompactSupport
      (compactEuclideanTestRep_spec u).2.1 : MemLp (compactEuclideanTestRep u) 2 volume).toLp
        (compactEuclideanTestRep u) = (u : E →₂[volume] ℝ) := by
  apply Lp.ext
  filter_upwards [((compactEuclideanTestRep_spec u).1.continuous.memLp_of_hasCompactSupport
      (compactEuclideanTestRep_spec u).2.1 : MemLp (compactEuclideanTestRep u) 2 volume).coeFn_toLp,
    (compactEuclideanTestRep_spec u).2.2] with x hx hy
  exact hx.trans hy

/-- Actual mixed second derivatives are additive at C³ regularity. -/
theorem second_coordinateDerivative_add {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (i j : Fin d) :
    coordinateDerivative j (coordinateDerivative i (fun x => f x + g x)) =
      fun x => coordinateDerivative j (coordinateDerivative i f) x + coordinateDerivative j
        (coordinateDerivative i g) x := by
  rw [coordinateDerivative_add_classical (hf.differentiable (by norm_num)) (hg.differentiable
    (by norm_num))]
  exact coordinateDerivative_add_classical
    ((c1_coordinateDerivative_of_c2 (hf.of_le (by norm_num)) i).differentiable (by norm_num))
    ((c1_coordinateDerivative_of_c2 (hg.of_le (by norm_num)) i).differentiable (by norm_num)) j

/-- Actual mixed second derivatives are scalar linear at C³ regularity. -/
theorem second_coordinateDerivative_smul {f : E → ℝ} (hf : ContDiff ℝ 3 f) (r : ℝ) (i j : Fin d) :
    coordinateDerivative j (coordinateDerivative i (fun x => r * f x)) =
      fun x => r * coordinateDerivative j (coordinateDerivative i f) x := by
  rw [coordinateDerivative_smul_classical (hf.differentiable (by norm_num)) r]
  exact coordinateDerivative_smul_classical
    ((c1_coordinateDerivative_of_c2 (hf.of_le (by norm_num)) i).differentiable (by norm_num)) r j

/-- The actual second-derivative distribution as a linear functional on the
genuine dense L² test submodule. -/
@[expose] noncomputable def secondDerivativeTestFunctional {w : E → ℝ} (hw : MemLp w 2 volume)
    (i j : Fin d) : compactEuclideanTestSpace (d := d) →ₗ[ℝ] ℝ where
  toFun u := ∫ x, w x * coordinateDerivative j (coordinateDerivative i (compactEuclideanTestRep u))
    x
  map_add' := by
    intro u v
    have hr := (compactEuclideanTestRepLinear (d := d)).map_add u v
    change compactEuclideanTestRep (u + v) = fun x => compactEuclideanTestRep u x +
      compactEuclideanTestRep v x at hr
    rw [hr, second_coordinateDerivative_add (compactEuclideanTestRep_spec u).1
      (compactEuclideanTestRep_spec v).1]
    simp_rw [mul_add]
    exact integral_add (hw.integrable_mul (compact_second_coordinate_memLp
      (compactEuclideanTestRep_spec u).1 (compactEuclideanTestRep_spec u).2.1 i j))
      (hw.integrable_mul (compact_second_coordinate_memLp
      (compactEuclideanTestRep_spec v).1 (compactEuclideanTestRep_spec v).2.1 i j))
  map_smul' := by
    intro r u
    have hr := (compactEuclideanTestRepLinear (d := d)).map_smul r u
    change compactEuclideanTestRep (r • u) = fun x => r * compactEuclideanTestRep u x at hr
    rw [hr, second_coordinateDerivative_smul (compactEuclideanTestRep_spec u).1 r]
    simp_rw [mul_left_comm (w _)]
    exact integral_const_mul r _

/-- Actual weak second derivatives are represented in genuine Lebesgue L²,
constructed from the actual distributional Laplacian and proved estimates. -/
theorem exists_L2_second_derivative_of_distributional_laplacian
    {w F : E → ℝ} (hwm : Measurable w) (hw : MemLp w 2 volume) (hwc : HasCompactSupport w)
    (hFm : Measurable F) (hF : MemLp F 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (w (x + h) - w x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, w x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x) (i j : Fin d) :
    ∃ H : E →₂[volume] ℝ, ‖H‖ ≤ ‖hF.toLp F‖ ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∫ x, w x * coordinateDerivative j (coordinateDerivative i ψ) x) = ∫ x, H x * ψ x := by
  have hb (v : compactEuclideanTestSpace (d := d)) : |secondDerivativeTestFunctional hw i j v| ≤
      ‖hF.toLp F‖ * ‖(v : E →₂[volume] ℝ)‖ := by
    have hh := bounded_second_derivative_distribution hwm hw hwc hFm hF C hC htrans heq
      (compactEuclideanTestRep_spec v).1 (compactEuclideanTestRep_spec v).2.1 i j
    rw [compactEuclideanTestRep_toLp v] at hh
    exact hh
  obtain ⟨H, hH, hpair⟩ := exists_riesz_of_dense_submodule_bound
    (compactEuclideanTestSpace (d := d)) compactEuclideanTestSpace_dense
    (secondDerivativeTestFunctional hw i j) ‖hF.toLp F‖ (norm_nonneg _) hb
  refine ⟨H, hH, ?_⟩
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  let v : compactEuclideanTestSpace (d := d) := ⟨hψLp.toLp ψ, ψ, hψ, hψc, hψLp.coeFn_toLp.symm⟩
  have hr : ψ = compactEuclideanTestRep v := compactEuclideanTestRep_unique v hψ.continuous
    hψLp.coeFn_toLp.symm
  have hp := hpair v
  change (∫ x, w x * coordinateDerivative j (coordinateDerivative i (compactEuclideanTestRep v)) x)
    =
    inner ℝ H (hψLp.toLp ψ) at hp
  rw [← hr] at hp
  apply hp.trans
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψLp.coeFn_toLp] with x hx
  rw [hx, Real.inner_apply]

end CutoffRigidity
