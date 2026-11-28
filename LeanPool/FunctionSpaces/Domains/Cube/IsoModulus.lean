/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.IsoDifferences
public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The isotropic modulus of smoothness on the cube

The **isotropic modulus** on the cube `Q = [0, 1]^d` is the modulus on the set `Q` of
`Rd.modulusOn` (`Cube.isoModulus`),

`ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}`   (`Cube.isoModulus_eq_iSup`),

with steps `h ∈ ℝ^d` of every direction and sign and the region `{x ∈ Q : x + rh ∈ Q}`
(`Cube.isoRegion`), which is the set of the points `x` with `x, x + h, …, x + rh ∈ Q`
(`Cube.isoRegion_inter_cubeSet`). It increases in `t`, is subadditive, is bounded by
`2^r ‖f‖_p`, and depends only on the class of `f` in `L_p(Q)`, as every modulus on a set.
Translations that stay in the cube keep `L_p` norms and null sets (`Cube.eLpNorm_comp_add_le`,
`Cube.ae_comp_add_of_ae`).

Steps along a coordinate are isotropic steps, so the moduli in the coordinates are bounded by
the isotropic modulus (`Cube.coordModulus_le_isoModulus`) and `ω_cube ≤ d ω_iso`
(`Cube.cubeModulus_le_isoModulus`). Jackson's inequalities with the coordinate moduli therefore
hold with the isotropic modulus as well. The converse comparison, for the approximants, is the
inverse inequality of `FunctionSpaces.Domains.Cube.IsoInverse`.
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff)
open scoped ENNReal

namespace Cube

open Interval

variable {d : ℕ}

/-! ### The cube as a set, and translations inside it -/

/-- The **cube** `Q = [0, 1]^d` as a subset of `ℝ^d`. -/
def cubeSet (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1

/-- The cube is measurable. -/
theorem measurableSet_cubeSet (d : ℕ) : MeasurableSet (cubeSet d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The cube measure is Lebesgue measure restricted to the cube (Mathlib's
`Measure.restrict_pi_pi`). -/
theorem cubeVol_eq_restrict (d : ℕ) : cubeVol d = volume.restrict (cubeSet d) := by
  rw [cubeSet, volume_pi, Measure.restrict_pi_pi]

/-- The cube measure restricted to two sets that agree on the cube. -/
theorem cubeVol_restrict_congr {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ∩ cubeSet d = B ∩ cubeSet d) :
    (cubeVol d).restrict A = (cubeVol d).restrict B := by
  rw [cubeVol_eq_restrict, Measure.restrict_restrict hA, Measure.restrict_restrict hB, hAB]

/-- **Translation inside the cube**: if `x + v ∈ R' ∩ Q` for all `x ∈ R ∩ Q`, then
`‖G(· + v)‖_{L_p(R ∩ Q)} ≤ ‖G‖_{L_p(R' ∩ Q)}`, by the translation invariance of Lebesgue measure
(Mathlib's `measurePreserving_add_right`). -/
theorem eLpNorm_comp_add_le {G : (Fin d → ℝ) → ℂ} (hG : Measurable G) (p : ℝ≥0∞)
    {R R' : Set (Fin d → ℝ)} (hR : MeasurableSet R) (hR' : MeasurableSet R') (v : Fin d → ℝ)
    (hsub : ∀ x ∈ R ∩ cubeSet d, x + v ∈ R' ∩ cubeSet d) :
    eLpNorm (fun x => G (x + v)) p ((cubeVol d).restrict R) ≤
      eLpNorm G p ((cubeVol d).restrict R') := by
  have hC' : MeasurableSet (R' ∩ cubeSet d) := hR'.inter (measurableSet_cubeSet d)
  have hmp : MeasurePreserving (· + v) (volume.restrict ((· + v) ⁻¹' (R' ∩ cubeSet d)))
      (volume.restrict (R' ∩ cubeSet d)) :=
    (measurePreserving_add_right volume v).restrict_preimage hC'
  rw [cubeVol_eq_restrict, Measure.restrict_restrict hR, Measure.restrict_restrict hR']
  calc eLpNorm (fun x => G (x + v)) p (volume.restrict (R ∩ cubeSet d))
      ≤ eLpNorm (fun x => G (x + v)) p (volume.restrict ((· + v) ⁻¹' (R' ∩ cubeSet d))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx => hsub x hx) le_rfl)
    _ = eLpNorm G p (volume.restrict (R' ∩ cubeSet d)) :=
        eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmp

/-- **Translation inside the cube preserves almost everywhere equality**: if `f = g` almost
everywhere on the cube and `x + v ∈ Q` for `x ∈ R ∩ Q`, then `f(x + v) = g(x + v)` for almost
every `x ∈ R ∩ Q`. -/
theorem ae_comp_add_of_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[cubeVol d] g)
    {R : Set (Fin d → ℝ)} (hR : MeasurableSet R) (v : Fin d → ℝ)
    (hsub : ∀ x ∈ R ∩ cubeSet d, x + v ∈ cubeSet d) :
    ∀ᵐ x ∂(cubeVol d).restrict R, f (x + v) = g (x + v) := by
  rw [cubeVol_eq_restrict] at hfg ⊢
  rw [Measure.restrict_restrict hR]
  have hmp : MeasurePreserving (· + v) (volume.restrict ((· + v) ⁻¹' cubeSet d))
      (volume.restrict (cubeSet d)) :=
    (measurePreserving_add_right volume v).restrict_preimage (measurableSet_cubeSet d)
  have h1 : (fun x => f (x + v)) =ᵐ[volume.restrict ((· + v) ⁻¹' cubeSet d)]
      fun x => g (x + v) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hfg
  exact ae_restrict_of_ae_restrict_of_subset (fun x hx => hsub x hx) h1

/-- **Convexity of intervals**: if `a, a + R b ∈ [0, 1]` and `0 ≤ n ≤ R`, then
`a + n b ∈ [0, 1]`. -/
theorem add_mul_mem_Icc {a b R n : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hR : a + R * b ∈ Icc (0 : ℝ) 1)
    (hn : 0 ≤ n) (hnR : n ≤ R) : a + n * b ∈ Icc (0 : ℝ) 1 := by
  rcases le_total 0 b with hb | hb
  · have h1 := mul_le_mul_of_nonneg_right hnR hb
    have h2 := mul_nonneg hn hb
    constructor <;> linarith [ha.1, ha.2, hR.1, hR.2]
  · have h1 := mul_le_mul_of_nonpos_right hnR hb
    have h2 := mul_nonpos_of_nonneg_of_nonpos hn hb
    constructor <;> linarith [ha.1, ha.2, hR.1, hR.2]

/-! ### The isotropic modulus -/

/-- The **region of the isotropic difference** of order `r` and step `h`: the points `x` with
`x + rh ∈ [0, 1]^d`. Together with `x ∈ Q` (the cube measure lives on `Q`) all points `x + kh`,
`k ≤ r`, lie in `Q`. -/
def isoRegion (r : ℕ) (h : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i + r * h i ∈ Icc (0 : ℝ) 1}

/-- The isotropic region is measurable. -/
theorem measurableSet_isoRegion (r : ℕ) (h : Fin d → ℝ) : MeasurableSet (isoRegion r h) := by
  have : isoRegion r h = ⋂ i, (fun x : Fin d → ℝ => x i + r * h i) ⁻¹' Icc 0 1 := by
    ext x
    simp [isoRegion]
  rw [this]
  exact MeasurableSet.iInter fun i => ((measurable_pi_apply i).add_const _) measurableSet_Icc

/-- For `x` in the isotropic region of the cube and `0 ≤ n ≤ r`, `x + nh` lies in the cube. -/
theorem add_smul_mem_cubeSet {r : ℕ} {h x : Fin d → ℝ} (hx : x ∈ isoRegion r h ∩ cubeSet d)
    {n : ℝ} (hn : 0 ≤ n) (hnr : n ≤ r) : x + n • h ∈ cubeSet d := by
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_mul_mem_Icc (hx.2 i (mem_univ i)) (hx.1 i) hn hnr

/-- **The isotropic region on the cube is a step set**: `{x ∈ Q : x + rh ∈ Q}` is the set `Q_{rh}`
of the points `x` with `x, x + h, …, x + rh ∈ Q` (`Rd.stepSet`). -/
theorem isoRegion_inter_cubeSet (r : ℕ) (h : Fin d → ℝ) :
    isoRegion r h ∩ cubeSet d = Rd.stepSet (cubeSet d) r h := by
  ext x
  constructor
  · intro hx l hl
    exact add_smul_mem_cubeSet hx (Nat.cast_nonneg l) (by exact_mod_cast hl)
  · intro hx
    refine ⟨fun i => ?_, by simpa using hx 0 (Nat.zero_le r)⟩
    simpa using hx r le_rfl i (mem_univ i)

/-- The isotropic difference on the cube is the restricted difference on the set `Q`:
`‖Δ_h^r f‖_{L_p(Q_{rh})} = ‖Δ_h^r(f, ·, Q)‖_p`. -/
theorem eLpNorm_higherDiff_isoRegion_eq (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ)
    (h : Fin d → ℝ) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) =
      eLpNorm ((Rd.stepSet (cubeSet d) r h).indicator ((fwdDiff h)^[r] f)) p volume := by
  rw [cubeVol_eq_restrict, Measure.restrict_restrict (measurableSet_isoRegion r h),
    isoRegion_inter_cubeSet, eLpNorm_indicator_eq_eLpNorm_restrict
      (Rd.measurableSet_stepSet (measurableSet_cubeSet d) r h).nullMeasurableSet]
  rfl

/-- The **isotropic modulus of smoothness** on the cube, the modulus on the set `Q` of
`Rd.modulusOn`: `ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r(f, ·, Q)‖_p`. -/
noncomputable def isoModulus (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) : ℝ≥0∞ :=
  Rd.modulusOn volume (cubeSet d) r p f t

/-- **The isotropic modulus through the isotropic regions**:
`ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}`. -/
theorem isoModulus_eq_iSup (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) :
    isoModulus r p f t = ⨆ (h : Fin d → ℝ) (_ : ‖h‖ ≤ t),
      eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) := by
  simp only [eLpNorm_higherDiff_isoRegion_eq]
  rfl

/-- `‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ ω_r(f, t)_p` for `‖h‖_∞ ≤ t`. -/
theorem eLpNorm_higherDiff_le_isoModulus {r : ℕ} {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℂ} {t : ℝ}
    {h : Fin d → ℝ} (hh : ‖h‖ ≤ t) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      isoModulus r p f t := by
  rw [eLpNorm_higherDiff_isoRegion_eq]
  exact Rd.eLpNorm_indicator_higherDiff_le_modulusOn hh

/-- The isotropic modulus increases in `t`. -/
theorem isoModulus_mono (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) :
    Monotone (isoModulus r p f) :=
  Rd.modulusOn_mono _ r p f

/-- The isotropic modulus is subadditive. -/
theorem isoModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : (Fin d → ℝ) → ℂ) (t : ℝ) :
    isoModulus r p (f + g) t ≤ isoModulus r p f t + isoModulus r p g t :=
  Rd.modulusOn_add_le hp _ r f g t

/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_{L_p(Q)}` for the isotropic modulus (`Rd.modulusOn_le`). -/
theorem isoModulus_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (t : ℝ) : isoModulus r p f t ≤ 2 ^ r * eLpNorm f p (cubeVol d) := by
  have h := Rd.modulusOn_le (μ := volume) hf.aestronglyMeasurable (measurableSet_cubeSet d) hp
    r t
  rwa [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_cubeSet d).nullMeasurableSet,
    ← cubeVol_eq_restrict]
    at h

/-- **`‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ 2^r ‖f‖_{L_p(Q)}`**, the bound of `Cube.isoModulus_le` at
`t = ‖h‖_∞`. -/
theorem eLpNorm_higherDiff_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (h : Fin d → ℝ) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      2 ^ r * eLpNorm f p (cubeVol d) :=
  (eLpNorm_higherDiff_le_isoModulus le_rfl).trans (isoModulus_le hf hp r ‖h‖)

/-- **The isotropic modulus depends only on the class in `L_p(Q)`** (`Rd.modulusOn_congr_ae`,
with Mathlib's `ae_eq_restrict_iff_indicator_ae_eq`). -/
theorem isoModulus_congr_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[cubeVol d] g) (r : ℕ)
    (p : ℝ≥0∞) (t : ℝ) : isoModulus r p f t = isoModulus r p g t := by
  rw [cubeVol_eq_restrict, ae_eq_restrict_iff_indicator_ae_eq (measurableSet_cubeSet d)] at hfg
  exact Rd.modulusOn_congr_ae hfg r p t

/-! ### Coordinate moduli and the isotropic modulus -/

/-- The region of a coordinate difference is the isotropic region of the step `s e_i`, on the
cube. -/
theorem diffRegion_eq_isoRegion (r : ℕ) {s : ℝ} (hs : 0 ≤ s) (i : Fin d) :
    diffRegion d r s i = (cubeVol d).restrict (isoRegion r (Pi.single i s)) := by
  refine cubeVol_restrict_congr (measurable_pi_apply i measurableSet_Icc)
    (measurableSet_isoRegion r _) ?_
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, isoRegion, cubeSet, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨hxi, hx⟩
    refine ⟨fun c => ?_, hx⟩
    by_cases hc : c = i
    · subst hc
      simp only [Pi.single_eq_same]
      constructor <;> nlinarith [hxi.1, hxi.2, mul_nonneg (Nat.cast_nonneg r) hs]
    · simpa [hc] using hx c
  · rintro ⟨hiso, hx⟩
    refine ⟨?_, hx⟩
    have h := hiso i
    simp only [Pi.single_eq_same] at h
    exact ⟨(hx i).1, by linarith [h.2]⟩

/-- **Coordinate moduli are bounded by the isotropic modulus**: steps `s e_i`, `0 ≤ s ≤ t`, are
isotropic steps with `‖s e_i‖_∞ = s`. -/
theorem coordModulus_le_isoModulus (r : ℕ) (p : ℝ≥0∞) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (t : ℝ) : coordModulus r p i f t ≤ isoModulus r p f t := by
  classical
  refine iSup₂_le fun s hs => ?_
  have hnorm : ‖(Pi.single i s : Fin d → ℝ)‖ ≤ t := by
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  rw [← higherDiff_single, diffRegion_eq_isoRegion r hs.1 i]
  exact eLpNorm_higherDiff_le_isoModulus hnorm

/-- **The modulus on the cube is bounded by the isotropic modulus**: `ω_cube ≤ d ω_iso`. -/
theorem cubeModulus_le_isoModulus (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) :
    cubeModulus r p f t ≤ d * isoModulus r p f t := by
  calc cubeModulus r p f t ≤ ∑ _i : Fin d, isoModulus r p f t :=
        Finset.sum_le_sum fun i _ => coordModulus_le_isoModulus r p i f t
    _ = d * isoModulus r p f t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The isotropic modulus on `L_p(Q)` at dyadic scales -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The isotropic modulus of an element of `L_p(Q)` at the dyadic scale `2^(-k)`. -/
noncomputable def lpIsoModulus (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) : ℝ≥0∞ :=
  isoModulus r p (f : (Fin d → ℝ) → ℂ) (1 / 2 ^ k)

/-- The isotropic modulus on `L_p(Q)` is subadditive. -/
theorem lpIsoModulus_add_le (r : ℕ) (f g : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpIsoModulus p r (f + g) k ≤ lpIsoModulus p r f k + lpIsoModulus p r g k := by
  rw [lpIsoModulus, isoModulus_congr_ae (Lp.coeFn_add f g)]
  exact isoModulus_add_le Fact.out r _ _ _

/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_p` in `L_p(Q)`, for the isotropic modulus. -/
theorem lpIsoModulus_le (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpIsoModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact isoModulus_le (Lp.stronglyMeasurable f).measurable Fact.out r _

omit [Fact (1 ≤ p)] in
/-- The isotropic modulus at the dyadic scales decreases with the level. -/
theorem lpIsoModulus_anti (r : ℕ) (f : Lp ℂ p (cubeVol d)) : Antitone (lpIsoModulus p r f) :=
  fun _ _ hjk => isoModulus_mono r p _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))

omit [Fact (1 ≤ p)] in
/-- `ω_cube(f, 2^(-k)) ≤ d ω_iso(f, 2^(-k))` in `L_p(Q)`. -/
theorem lpCubeModulus_le_lpIsoModulus (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpCubeModulus p r f k ≤ d * lpIsoModulus p r f k :=
  cubeModulus_le_isoModulus r p _ _

end Cube
