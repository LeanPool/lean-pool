/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.WeakContL3Support
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4

/-!
# Norming estimates for weak continuity in `L^3`
- shared internal estimates used to upgrade the all-time `L²` representative.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩


noncomputable section

namespace ESS

/-- The canonical inclusion from `L²` to `L^{3/2}` on a finite-measure spatial domain. -/
@[expose] noncomputable def weakContL3L2ToLThreeHalvesLinear
    (μ : Measure Vec3) [IsFiniteMeasure μ] :
    Lp L2Vec3 2 μ →ₗ[ℝ]
      Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ)) μ where
  toFun f := (Lp.memLp f).mono_exponent
    (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num) |>.toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add f g,
      ((Lp.memLp (f + g)).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).coeFn_toLp,
      ((Lp.memLp f).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).coeFn_toLp,
      ((Lp.memLp g).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).coeFn_toLp,
      Lp.coeFn_add
        (((Lp.memLp f).mono_exponent
          (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp f)
        (((Lp.memLp g).mono_exponent
          (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp g)]
      with x hfg hsum hf hg hplus
    change (f + g) x = f x + g x at hfg
    change (((Lp.memLp (f + g)).mono_exponent
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp (f + g)) x =
      ((((Lp.memLp f).mono_exponent
          (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp f +
        ((Lp.memLp g).mono_exponent
          (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp g) :
        Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ)) μ) x
    rw [hsum, hfg, hplus]
    simp only [Pi.add_apply]
    rw [hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c f,
      ((Lp.memLp (c • f)).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).coeFn_toLp,
      ((Lp.memLp f).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).coeFn_toLp,
      Lp.coeFn_smul c (((Lp.memLp f).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp f)]
      with x hcf hsmul hf hsmulOut
    change (c • f) x = c • f x at hcf
    change (((Lp.memLp (c • f)).mono_exponent
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp (c • f)) x =
      (c • ((Lp.memLp f).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp f) x
    rw [hsmul, hcf, hsmulOut]
    simp only [Pi.smul_apply]
    rw [hf]

theorem weakContL3L2ToLThreeHalves_bound
    (μ : Measure Vec3) [IsFiniteMeasure μ]
    (f : Lp L2Vec3 2 μ) :
    ‖weakContL3L2ToLThreeHalvesLinear μ f‖ ≤
      (μ Set.univ ^ (1 / 6 : ℝ)).toReal * ‖f‖ := by
  change ‖((Lp.memLp f).mono_exponent
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)).toLp f‖ ≤
      (μ Set.univ ^ (1 / 6 : ℝ)).toReal * ‖f‖
  rw [Lp.norm_toLp]
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞)) (by norm_num)
    (Lp.aestronglyMeasurable f)
  have hexp : 1 / ENNReal.toReal (ENNReal.ofReal (3 / 2 : ℝ)) -
      1 / ENNReal.toReal (2 : ℝ≥0∞) = 1 / 6 := by norm_num
  rw [hexp] at hcompare
  have hfinite : μ Set.univ ^ (1 / 6 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)
  have hmulTop : eLpNorm f 2 μ * μ Set.univ ^ (1 / 6 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hfinite.ne
  calc
    ENNReal.toReal (eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ) ≤
        ENNReal.toReal (eLpNorm f 2 μ * μ Set.univ ^ (1 / 6 : ℝ)) :=
          ENNReal.toReal_mono hmulTop hcompare
    _ = (ENNReal.toReal (eLpNorm f 2 μ)) *
        (ENNReal.toReal (μ Set.univ ^ (1 / 6 : ℝ))) := by
          rw [ENNReal.toReal_mul]
    _ = (μ Set.univ ^ (1 / 6 : ℝ)).toReal * ‖f‖ := by
          rw [Lp.norm_def]
          ring

/-- The continuous inclusion of spatial `L²` into `L^{3/2}` on a finite measure set. -/
@[expose] noncomputable def weakContL3L2ToLThreeHalves
    (μ : Measure Vec3) [IsFiniteMeasure μ] :
    Lp L2Vec3 2 μ →L[ℝ]
      Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
  (weakContL3L2ToLThreeHalvesLinear μ).mkContinuous
    (μ Set.univ ^ (1 / 6 : ℝ)).toReal
    (weakContL3L2ToLThreeHalves_bound μ)

/-- A pairing estimate on a dense family extends to every `L²` test. -/
theorem weakContL3_pairing_bound_of_dense
    (μ : Measure Vec3) [IsFiniteMeasure μ]
    (ψ : ℕ → Lp L2Vec3 2 μ) (hψ : DenseRange ψ)
    (v : Lp L2Vec3 2 μ) (C : ℝ)
    (hbound : ∀ n, |inner ℝ v (ψ n)| ≤
      C * ‖weakContL3L2ToLThreeHalves μ (ψ n)‖) :
    ∀ x, |inner ℝ v x| ≤ C * ‖weakContL3L2ToLThreeHalves μ x‖ := by
  have hleft : Continuous (fun x : Lp L2Vec3 2 μ => |inner ℝ v x|) :=
    continuous_abs.comp (innerSL ℝ v).continuous
  have hright : Continuous (fun x : Lp L2Vec3 2 μ =>
      C * ‖weakContL3L2ToLThreeHalves μ x‖) :=
    continuous_const.mul (continuous_norm.comp (weakContL3L2ToLThreeHalves μ).continuous)
  have hclosed : IsClosed {x : Lp L2Vec3 2 μ |
      |inner ℝ v x| ≤ C * ‖weakContL3L2ToLThreeHalves μ x‖} :=
    isClosed_le hleft hright
  have hsub : Set.range ψ ⊆ {x : Lp L2Vec3 2 μ |
      |inner ℝ v x| ≤ C * ‖weakContL3L2ToLThreeHalves μ x‖} := by
    rintro x ⟨n, rfl⟩
    exact hbound n
  have hrange : Dense (Set.range ψ) := hψ
  have hclosure : closure (Set.range ψ) = Set.univ := hrange.closure_eq
  intro x
  have hx : x ∈ closure (Set.range ψ) := by rw [hclosure]; trivial
  exact closure_minimal hsub hclosed hx

/-- Hölder bounds the pairing of an `L³` field with an `L^{3/2}` test. -/
theorem weakContL3_inner_holder
    {μ : Measure Vec3} {f g : Vec3 → L2Vec3}
    (hf₂ : MemLp f 2 μ) (hg₂ : MemLp g 2 μ)
    (hf₃ : MemLp f 3 μ)
    (hg₃₂ : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ) :
    |inner ℝ (hf₂.toLp f) (hg₂.toLp g)| ≤
      (eLpNorm f 3 μ).toReal *
        (eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
  have hinnerInt : Integrable (fun x : Vec3 =>
      inner ℝ (hf₂.toLp f x) (hg₂.toLp g x)) μ :=
    MeasureTheory.L2.integrable_inner (hf₂.toLp f) (hg₂.toLp g)
  have hinnerEq : inner ℝ (hf₂.toLp f) (hg₂.toLp g) =
      ∫ x, inner ℝ (f x) (g x) ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
  have hinnerInt' : Integrable (fun x : Vec3 => inner ℝ (f x) (g x)) μ := by
    apply hinnerInt.congr
    filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hfx hgx
    simp [hfx, hgx]
  have hprod₁ : Integrable (fun x : Vec3 => ‖f x‖ * ‖g x‖) μ := by
    have hmem : MemLp (fun x : Vec3 => ‖f x‖ * ‖g x‖) 1 μ := by
      have hpq : ENNReal.HolderTriple
        ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal) 1 := by
        constructor
        rw [← ENNReal.coe_inv (by norm_num : (3 / 2 : NNReal) ≠ 0),
          ← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0)]
        norm_cast
        norm_num [div_eq_mul_inv]
      have hcast : ENNReal.ofReal (3 / 2 : ℝ) =
          ((3 / 2 : NNReal) : ENNReal) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
        exact congrArg (fun x : NNReal => (x : ENNReal)) (NNReal.eq (by norm_num))
      have hgNorm32 : MemLp (fun x : Vec3 => ‖g x‖)
          ((3 / 2 : NNReal) : ENNReal) μ := by
        simpa [hcast] using hg₃₂.norm
      have := @MeasureTheory.MemLp.mul Vec3 _ ℝ _ μ
        ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal) 1
        (fun x => ‖f x‖) (fun x => ‖g x‖) hgNorm32 hf₃.norm hpq
      convert this using 1
      ext x
      simp [mul_comm]
    exact (memLp_one_iff_integrable.mp hmem)
  have hnormInt : Integrable (fun x : Vec3 => ‖inner ℝ (f x) (g x)‖) μ :=
    hinnerInt'.norm
  have hnormBound : ∀ᵐ x ∂μ,
      ‖inner ℝ (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ := by
    filter_upwards [] with x
    exact norm_inner_le_norm _ _
  have hpointInt : ∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ ≤
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
    integral_mono_ae hnormInt hprod₁ hnormBound
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 3) (q := 3 / 2)
    (by constructor <;> norm_num [Real.HolderTriple]) (by simpa using hf₃) hg₃₂
  have hrootf :
      (∫ x, ‖f x‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) =
        (eLpNorm f 3 μ).toReal := by
    rw [hf₃.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num [ENNReal.toReal_ofNat]
    · positivity
  have hrootg :
      (∫ x, ‖g x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) =
        (eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
    rw [hg₃₂.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num [ENNReal.toReal_ofReal]
    · positivity
  rw [hinnerEq, ← Real.norm_eq_abs]
  calc
    ‖∫ x, inner ℝ (f x) (g x) ∂μ‖ ≤
        ∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ :=
          norm_integral_le_integral_norm (fun x => inner ℝ (f x) (g x))
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := hpointInt
    _ ≤ (∫ x, ‖f x‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
          (∫ x, ‖g x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
            convert hholder using 1
            norm_num
    _ = _ := by rw [hrootf, hrootg]

/-- Hölder controls the integrated vector pairing for arbitrary `L³` and
`L^{3/2}` fields. -/
theorem weakContL3_integral_holder
    {μ : Measure Vec3} {f g : Vec3 → L2Vec3}
    (hf₃ : MemLp f 3 μ)
    (hg₃₂ : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ ∧
      |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
        (eLpNorm f 3 μ).toReal *
          (eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
  have hpq : ENNReal.HolderTriple
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal) 1 := by
    constructor
    rw [← ENNReal.coe_inv (by norm_num : (3 / 2 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0)]
    norm_cast
    norm_num [div_eq_mul_inv]
  have hcast : ENNReal.ofReal (3 / 2 : ℝ) =
      ((3 / 2 : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    exact congrArg (fun x : NNReal => (x : ENNReal)) (NNReal.eq (by norm_num))
  have hgNorm32 : MemLp (fun x : Vec3 => ‖g x‖)
      ((3 / 2 : NNReal) : ENNReal) μ := by
    simpa [hcast] using hg₃₂.norm
  have hprodLp : MemLp (fun x : Vec3 => ‖f x‖ * ‖g x‖) 1 μ := by
    have hp := @MeasureTheory.MemLp.mul Vec3 _ ℝ _ μ
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal) 1
      (fun x => ‖f x‖) (fun x => ‖g x‖) hgNorm32 hf₃.norm hpq
    convert hp using 1
    ext x
    simp [mul_comm]
  have hprod : Integrable (fun x : Vec3 => ‖f x‖ * ‖g x‖) μ :=
    memLp_one_iff_integrable.mp hprodLp
  have hinnerMeas : AEStronglyMeasurable
      (fun x : Vec3 => inner ℝ (f x) (g x)) μ :=
    AEStronglyMeasurable.inner hf₃.aestronglyMeasurable hg₃₂.aestronglyMeasurable
  have hinnerInt : Integrable (fun x : Vec3 => inner ℝ (f x) (g x)) μ :=
    hprod.mono' hinnerMeas (Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _)
  have hinnerNorm : Integrable
      (fun x : Vec3 => ‖inner ℝ (f x) (g x)‖) μ := hinnerInt.norm
  have hpoint : ∀ᵐ x ∂μ,
      ‖inner ℝ (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ :=
    Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _
  have hpointInt : ∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ ≤
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ := integral_mono_ae hinnerNorm hprod hpoint
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 3) (q := 3 / 2)
    (by constructor <;> norm_num [Real.HolderTriple]) (by simpa using hf₃) hg₃₂
  have hrootf :
      (∫ x, ‖f x‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) =
        (eLpNorm f 3 μ).toReal := by
    rw [hf₃.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num [ENNReal.toReal_ofNat]
    · positivity
  have hrootg :
      (∫ x, ‖g x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) =
        (eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
    rw [hg₃₂.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num [ENNReal.toReal_ofReal]
    · positivity
  refine ⟨hinnerInt, ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ x, inner ℝ (f x) (g x) ∂μ‖ ≤
        ∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := hpointInt
    _ ≤ (∫ x, ‖f x‖ ^ (3 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
          (∫ x, ‖g x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) := by
            convert hholder using 1
            norm_num
    _ = _ := by rw [hrootf, hrootg]

private theorem weakContL3_cube_bound {J C : ℝ} (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (h : J ≤ C * J ^ (2 / 3 : ℝ)) : J ≤ C ^ 3 := by
  by_cases hJzero : J = 0
  · simp [hJzero, pow_nonneg hC]
  have hJpos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJzero)
  have hdiv : J / J ^ (2 / 3 : ℝ) ≤ C :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hJpos _)).2 (by simpa [mul_comm] using h)
  have hroot : J ^ (1 / 3 : ℝ) ≤ C := by
    calc
      J ^ (1 / 3 : ℝ) = J ^ (1 : ℝ) / J ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_sub hJpos]
        norm_num
      _ = J / J ^ (2 / 3 : ℝ) := by rw [Real.rpow_one]
      _ ≤ C := hdiv
  have hcube := Real.rpow_le_rpow (Real.rpow_nonneg hJ (1 / 3 : ℝ)) hroot
    (by norm_num : 0 ≤ (3 : ℝ))
  have hleft : (J ^ (1 / 3 : ℝ)) ^ (3 : ℝ) = J := by
    rw [← Real.rpow_mul (le_of_lt hJpos)]
    norm_num
  have hright : C ^ (3 : ℝ) = C ^ 3 := by
    exact Real.rpow_natCast C 3
  rw [hleft, hright] at hcube
  exact hcube

/-- A uniform bound against `L²` tests controls the `L³` norm of the field. -/
theorem weakContL3_norming_bound
    {μ : Measure Vec3} [IsFiniteMeasure μ]
    (v : Lp L2Vec3 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ w : Lp L2Vec3 2 μ,
      |inner ℝ v w| ≤ C * ‖weakContL3L2ToLThreeHalves μ w‖) :
    MemLp (fun x : Vec3 => v x) 3 μ ∧
      eLpNorm (fun x : Vec3 => v x) 3 μ ≤ ENNReal.ofReal C := by
  classical
  let q : ℕ → Vec3 → L2Vec3 := fun n x =>
    min (‖v x‖) ((n + 1 : ℕ) : ℝ) • v x
  have hqcontinuous (n : ℕ) : Continuous (fun z : L2Vec3 =>
      min (‖z‖) ((n + 1 : ℕ) : ℝ) • z) := by
    fun_prop
  have hqmeas (n : ℕ) : AEStronglyMeasurable (q n) μ :=
    (hqcontinuous n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)
  have hqnorm (n : ℕ) (x : Vec3) :
      ‖q n x‖ = min (‖v x‖) ((n + 1 : ℕ) : ℝ) * ‖v x‖ := by
    change ‖min (‖v x‖) ((n + 1 : ℕ) : ℝ) • v x‖ = _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_min (norm_nonneg _) (by positivity))]
  have hqbound (n : ℕ) (x : Vec3) :
      ‖q n x‖ ≤ ((n + 1 : ℕ) : ℝ) * ‖v x‖ := by
    rw [hqnorm]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
  have hq₂ (n : ℕ) : MemLp (q n) 2 μ :=
    (Lp.memLp v).of_le_mul (hqmeas n)
      (Filter.Eventually.of_forall (hqbound n))
  have hq₃₂ (n : ℕ) : MemLp (q n) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    (hq₂ n).mono_exponent (by norm_num)
  have hmap (n : ℕ) :
      weakContL3L2ToLThreeHalves μ ((hq₂ n).toLp (q n)) =
        (hq₃₂ n).toLp (q n) := by
    apply Lp.ext
    filter_upwards [
      ((Lp.memLp ((hq₂ n).toLp (q n))).mono_exponent
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞))
        (by norm_num)).coeFn_toLp,
      (hq₃₂ n).coeFn_toLp,
      (hq₂ n).coeFn_toLp] with x h₁ h₂ h₃
    exact h₁.trans (h₃.trans h₂.symm)
  have hmapnorm (n : ℕ) :
      ‖weakContL3L2ToLThreeHalves μ ((hq₂ n).toLp (q n))‖ =
        (eLpNorm (q n) (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
    rw [hmap n, Lp.norm_toLp]
  let J : ℕ → ℝ := fun n =>
    ∫ x, min (‖v x‖) ((n + 1 : ℕ) : ℝ) * ‖v x‖ ^ 2 ∂μ
  have hJintegrable (n : ℕ) : Integrable
      (fun x : Vec3 => min (‖v x‖) ((n + 1 : ℕ) : ℝ) * ‖v x‖ ^ 2) μ := by
    have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) v ((hq₂ n).toLp (q n))
    apply hi.congr
    filter_upwards [(hq₂ n).coeFn_toLp] with x hx
    rw [hx]
    simp only [q, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hJnonneg (n : ℕ) : 0 ≤ J n := by
    dsimp [J]
    apply integral_nonneg
    intro x
    exact mul_nonneg (le_min (norm_nonneg _) (by positivity)) (sq_nonneg _)
  have hqpow (n : ℕ) (x : Vec3) :
      ‖q n x‖ ^ (3 / 2 : ℝ) ≤
        min (‖v x‖) ((n + 1 : ℕ) : ℝ) * ‖v x‖ ^ 2 := by
    rw [hqnorm]
    let r : ℝ := ‖v x‖
    let N : ℝ := ((n + 1 : ℕ) : ℝ)
    have hr : 0 ≤ r := by positivity
    have hN : 0 ≤ N := by positivity
    change (min r N * r) ^ (3 / 2 : ℝ) ≤ min r N * r ^ 2
    by_cases hrN : r ≤ N
    · rw [min_eq_left hrN]
      have hsqrt : √(r ^ 2) = r := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
      rw [show r * r = r ^ 2 by ring,
        Real.rpow_div_two_eq_sqrt 3 (sq_nonneg r), hsqrt]
      exact le_of_eq ((Real.rpow_natCast r 3).trans
        (by ring : r ^ (3 : ℕ) = r * r ^ (2 : ℕ)))
    · have hNr : N ≤ r := le_of_not_ge hrN
      rw [min_eq_right hNr]
      rw [Real.rpow_div_two_eq_sqrt 3 (mul_nonneg hN hr)]
      have hNrSq : N * r ≤ r ^ 2 := calc
          N * r ≤ r * r := mul_le_mul_of_nonneg_right hNr hr
          _ = r ^ 2 := by ring
      have hsqrtle : √(N * r) ≤ r := Real.sqrt_le_iff.mpr ⟨hr, hNrSq⟩
      calc
        (√(N * r)) ^ (3 : ℝ) = (√(N * r)) ^ 3 := Real.rpow_natCast _ 3
        _ = (√(N * r)) ^ 2 * √(N * r) := by ring
        _ = (N * r) * √(N * r) := by rw [Real.sq_sqrt (mul_nonneg hN hr)]
        _ ≤ (N * r) * r := mul_le_mul_of_nonneg_left hsqrtle (mul_nonneg hN hr)
        _ = N * r ^ 2 := by ring
  have hqpowIntegrable (n : ℕ) :
      Integrable (fun x : Vec3 => ‖q n x‖ ^ (3 / 2 : ℝ)) μ := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using
      (hq₃₂ n).integrable_norm_rpow (by norm_num) (by norm_num)
  have hJbound (n : ℕ) : J n ≤ C ^ 3 := by
    have hpair := hbound ((hq₂ n).toLp (q n))
    have hinnerEq : inner ℝ v ((hq₂ n).toLp (q n)) = J n := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hq₂ n).coeFn_toLp] with x hx
      rw [hx]
      simp [q, real_inner_smul_right]
    rw [hinnerEq, abs_of_nonneg (hJnonneg n), hmapnorm n] at hpair
    have hqintegral := integral_mono_ae (hqpowIntegrable n) (hJintegrable n)
      (Filter.Eventually.of_forall (hqpow n))
    have hqintegral_nonneg : 0 ≤ ∫ x, ‖q n x‖ ^ (3 / 2 : ℝ) ∂μ := by
      apply integral_nonneg
      intro x
      positivity
    have hroot :
        (∫ x, ‖q n x‖ ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) =
          (eLpNorm (q n) (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal := by
      rw [(hq₃₂ n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      rw [ENNReal.toReal_ofReal]
      · norm_num [ENNReal.toReal_ofReal]
      · positivity
    have htestnorm :
        (eLpNorm (q n) (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal ≤ J n ^ (2 / 3 : ℝ) := by
      rw [← hroot]
      exact Real.rpow_le_rpow hqintegral_nonneg hqintegral (by norm_num)
    exact weakContL3_cube_bound (hJnonneg n) hC
      (hpair.trans (mul_le_mul_of_nonneg_left htestnorm hC))
  let F : ℕ → Vec3 → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (min (‖v x‖) ((n + 1 : ℕ) : ℝ) * ‖v x‖ ^ 2)
  have hFmeas (n : ℕ) : AEMeasurable (F n) μ := by
    have hcont : Continuous (fun z : L2Vec3 =>
        ENNReal.ofReal (min (‖z‖) ((n + 1 : ℕ) : ℝ) * ‖z‖ ^ 2)) := by
      exact ENNReal.continuous_ofReal.comp
        ((continuous_norm.min continuous_const).mul (continuous_norm.pow 2))
    exact (hcont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)).aemeasurable
  have hFmono : Monotone F := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    have hN : ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact mul_le_mul_of_nonneg_right (min_le_min_left _ hN) (sq_nonneg _)
  have hFsup (x : Vec3) : (⨆ n, F n x) = ‖v x‖ₑ ^ (3 : ℝ) := by
    let r : ℝ := ‖v x‖
    have hr : 0 ≤ r := by positivity
    have hnorm : ENNReal.ofReal r = ‖v x‖ₑ := by
      dsimp [r]
      rw [← ofReal_norm]
    have htarget : ENNReal.ofReal (r ^ 3) = ‖v x‖ₑ ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast r 3,
        ← ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), hnorm]
      norm_num
    apply le_antisymm
    · apply iSup_le
      intro n
      calc
          F n x = ENNReal.ofReal
            (min r ((n + 1 : ℕ) : ℝ) * r ^ 2) := by rfl
        _ ≤ ENNReal.ofReal (r ^ 3) := by
          apply ENNReal.ofReal_le_ofReal
          calc
            min r ((n + 1 : ℕ) : ℝ) * r ^ 2 ≤ r * r ^ 2 :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg r)
            _ = r ^ 3 := by ring
        _ = ‖v x‖ₑ ^ (3 : ℝ) := htarget
    · obtain ⟨n, hn⟩ := exists_nat_gt r
      have hrN : r ≤ ((n + 1 : ℕ) : ℝ) := by
        have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ n
        exact hn.le.trans hnle
      rw [← htarget]
      apply le_iSup_of_le n
      change ENNReal.ofReal (r ^ 3) ≤
        ENNReal.ofReal (min r ((n + 1 : ℕ) : ℝ) * r ^ 2)
      rw [min_eq_left hrN]
      apply ENNReal.ofReal_le_ofReal
      rw [show r * r ^ 2 = r ^ 3 by ring]
  have hlintegral :
      (∫⁻ x, ‖v x‖ₑ ^ (3 : ℝ) ∂μ) ≤ ENNReal.ofReal (C ^ 3) := by
    calc
      (∫⁻ x, ‖v x‖ₑ ^ (3 : ℝ) ∂μ) = ∫⁻ x, ⨆ n, F n x ∂μ := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hFsup x).symm
      _ = ⨆ n, ∫⁻ x, F n x ∂μ :=
        lintegral_iSup' hFmeas (Filter.Eventually.of_forall fun x n m hnm =>
          hFmono hnm x)
      _ ≤ ENNReal.ofReal (C ^ 3) := by
        apply iSup_le
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hJintegrable n)]
        · exact ENNReal.ofReal_le_ofReal (hJbound n)
        · filter_upwards [] with x
          exact mul_nonneg (le_min (norm_nonneg _) (by positivity)) (sq_nonneg _)
  have hnormpow := eLpNorm_three_pow_eq_lintegral
    (μ := μ) (f := fun x => v x) (Lp.aestronglyMeasurable v)
  have hnormpowBound :
      eLpNorm (fun x : Vec3 => v x) 3 μ ^ (3 : ℝ) ≤
        (ENNReal.ofReal C) ^ (3 : ℝ) := by
    rw [hnormpow]
    calc
      (∫⁻ x, ‖v x‖ₑ ^ (3 : ℝ) ∂μ) ≤ ENNReal.ofReal (C ^ 3) := hlintegral
      _ = (ENNReal.ofReal C) ^ (3 : ℝ) := by
        calc
          ENNReal.ofReal (C ^ 3) = ENNReal.ofReal C ^ (3 : ℕ) :=
            ENNReal.ofReal_pow hC 3
          _ = ENNReal.ofReal C ^ (3 : ℝ) :=
            (ENNReal.rpow_natCast (ENNReal.ofReal C) 3).symm
  have hnormBound : eLpNorm (fun x : Vec3 => v x) 3 μ ≤ ENNReal.ofReal C :=
    (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (3 : ℝ))).mp hnormpowBound
  have hfinite : eLpNorm (fun x : Vec3 => v x) 3 μ < ⊤ :=
    lt_of_le_of_lt hnormBound (ENNReal.ofReal_lt_top)
  exact ⟨(memLp_iff).2 hfinite, hnormBound⟩



end ESS
