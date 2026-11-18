/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.Triangular.Auto.TriangularHT
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Carleson's theorem for continuous 1-periodic functions, deduced from the triangular bound. -/

@[expose] public section
namespace Triangular.Auto

open MeasureTheory Filter Topology Set

open scoped ContDiff ENNReal NNReal Convolution

noncomputable section

section Weight

/-- The bump in the first input, equal to one on `[-1, 1]` and supported in `(-2, 2)`. -/
def carlesonBump₀ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump in the other inputs, equal to one on `[-8, 8]` and supported in `(-9, 9)`. -/
def carlesonBump₁ : ContDiffBump (0 : ℝ) := ⟨8, 9, by norm_num, by norm_num⟩

lemma carlesonBump_eq_zero (b : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : b.rOut ≤ |x|) : b x = 0 :=
  b.zero_of_le_dist (by simpa [Real.dist_eq] using hx)

lemma carlesonBump_eq_one (b : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : |x| ≤ b.rIn) : b x = 1 :=
  b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hx)

/-- A bounded measurable function on the line vanishing outside a compact interval is integrable. -/
lemma integrable_of_norm_le_of_vanish {E : Type*} [NormedAddCommGroup E] {h : ℝ → E} {A B : ℝ}
    (hm : AEStronglyMeasurable h volume) (hB : ∀ x, ‖h x‖ ≤ B)
    (hs : ∀ x, A < |x| → h x = 0) : Integrable h := by
  have he : h = (Icc (-A) A).indicator h := by
    ext x
    by_cases hx : x ∈ Icc (-A) A
    · simp [hx]
    · rw [indicator_of_notMem hx, hs x (lt_of_not_ge fun h' => hx (abs_le.mp h'))]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact Measure.integrableOn_of_bounded (by simp [Real.volume_Icc]) hm (ae_of_all _ hB)

lemma hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {A : ℝ}
    (hf : ∀ x, A < |x| → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun x hx =>
    hf x (lt_of_not_ge fun h => hx (abs_le.mp h))

/-- The planar weight produced by the three bumps in the coordinates `(t, u)`. -/
def carlesonW (t u : ℝ) : ℝ :=
  carlesonBump₀ u * carlesonBump₁ (2 * u - t) * carlesonBump₁ (t - u)

/-- The kernel weight `m(t)`. -/
def carlesonWeight (t : ℝ) : ℝ := ∫ u, carlesonW t u

/-- The value of the kernel weight near the origin. -/
def carlesonMass : ℝ := ∫ u, carlesonBump₀ u

lemma continuous_carlesonW : Continuous fun p : ℝ × ℝ => carlesonW p.1 p.2 := by
  unfold carlesonW
  have h₀ := carlesonBump₀.continuous
  have h₁ := carlesonBump₁.continuous
  fun_prop

lemma carlesonW_nonneg (t u : ℝ) : 0 ≤ carlesonW t u := by
  unfold carlesonW
  have := carlesonBump₀.nonneg (x := u)
  have := carlesonBump₁.nonneg (x := 2 * u - t)
  have := carlesonBump₁.nonneg (x := t - u)
  positivity

lemma carlesonW_le (t u : ℝ) : carlesonW t u ≤ carlesonBump₀ u := by
  unfold carlesonW
  have h₀ := carlesonBump₀.nonneg (x := u)
  have h₁ := carlesonBump₁.nonneg (x := 2 * u - t)
  have h₂ := carlesonBump₁.le_one (x := 2 * u - t)
  have h₃ := carlesonBump₁.nonneg (x := t - u)
  have h₄ := carlesonBump₁.le_one (x := t - u)
  calc carlesonBump₀ u * carlesonBump₁ (2 * u - t) * carlesonBump₁ (t - u)
      ≤ carlesonBump₀ u * 1 * 1 := by gcongr
    _ = carlesonBump₀ u := by ring

lemma carlesonW_eq_of_abs_le {t : ℝ} (ht : |t| ≤ 2) (u : ℝ) :
    carlesonW t u = carlesonBump₀ u := by
  unfold carlesonW
  by_cases hu : |u| < 2
  · rw [carlesonBump_eq_one carlesonBump₁ (x := 2 * u - t),
      carlesonBump_eq_one carlesonBump₁ (x := t - u), mul_one, mul_one]
    · change |t - u| ≤ 8
      rw [abs_le] at ht ⊢; rw [abs_lt] at hu; constructor <;> linarith
    · change |2 * u - t| ≤ 8
      rw [abs_le] at ht ⊢; rw [abs_lt] at hu; constructor <;> linarith
  · rw [carlesonBump_eq_zero carlesonBump₀ (not_lt.mp hu)]
    ring

lemma carlesonW_eq_zero {t : ℝ} (ht : 11 ≤ |t|) (u : ℝ) : carlesonW t u = 0 := by
  unfold carlesonW
  by_cases hu : |u| < 2
  · rw [carlesonBump_eq_zero carlesonBump₁ (x := t - u), mul_zero]
    change (9 : ℝ) ≤ |t - u|
    have := abs_sub_abs_le_abs_sub t u
    linarith
  · rw [carlesonBump_eq_zero carlesonBump₀ (not_lt.mp hu)]
    ring

lemma integrable_carlesonW (t : ℝ) : Integrable (carlesonW t) := by
  refine carlesonBump₀.integrable.mono'
    (continuous_carlesonW.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (carlesonW_nonneg t u)]
  exact carlesonW_le t u

lemma carlesonWeight_eq_mass {t : ℝ} (ht : |t| ≤ 2) : carlesonWeight t = carlesonMass :=
  integral_congr_ae (ae_of_all _ (carlesonW_eq_of_abs_le ht))

lemma carlesonWeight_nonneg (t : ℝ) : 0 ≤ carlesonWeight t :=
  integral_nonneg (carlesonW_nonneg t)

lemma carlesonWeight_le_mass (t : ℝ) : carlesonWeight t ≤ carlesonMass :=
  integral_mono (integrable_carlesonW t) carlesonBump₀.integrable (carlesonW_le t)

lemma carlesonWeight_eq_zero {t : ℝ} (ht : 11 ≤ |t|) : carlesonWeight t = 0 := by
  simp [carlesonWeight, carlesonW_eq_zero ht]

lemma carlesonMass_pos : 0 < carlesonMass := carlesonBump₀.integral_pos

lemma measurable_carlesonWeight : Measurable carlesonWeight :=
  (continuous_carlesonW.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable

lemma integrable_carlesonWeight : Integrable carlesonWeight :=
  integrable_of_norm_le_of_vanish (A := 11) measurable_carlesonWeight.aestronglyMeasurable
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (carlesonWeight_nonneg t)]
      exact carlesonWeight_le_mass t)
    (fun t ht => carlesonWeight_eq_zero ht.le)

end Weight

section Specialization

open Complex in
/-- First triangular input `a(x) e^{iσν(x)(x+y)} ρ₀(y + x/2)`. -/
def carlesonF₀ (a ν : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (a p.1 : ℂ) * exp ((σ * ν p.1 * (p.1 + p.2) : ℝ) * I) * (carlesonBump₀ (p.2 + p.1 / 2) : ℂ)

/-- Second triangular input `g(-y-z) ρ₁(y - z)`. -/
def carlesonF₁ (g : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := g (-p.1 - p.2) * (carlesonBump₁ (p.1 - p.2) : ℂ)

open Complex in
/-- Third triangular input `a(x) e^{iσν(x)z} ρ₁(z + x/2)`, in the variables `(z, x)`. -/
def carlesonF₂ (a ν : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (a p.2 : ℂ) * exp ((σ * ν p.2 * p.1 : ℝ) * I) * (carlesonBump₁ (p.1 + p.2 / 2) : ℂ)

lemma contDiff_ofReal_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (f p : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hf

lemma contDiff_exp_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => Complex.exp ((f p : ℂ) * Complex.I) :=
  Complex.contDiff_exp.comp ((contDiff_ofReal_comp hf).mul contDiff_const)

private lemma contDiff_modulatedInput {amplitude phase weight : ℝ × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amplitude) (hp : ContDiff ℝ ∞ phase) (hw : ContDiff ℝ ∞ weight) :
    ContDiff ℝ ∞ fun q => (amplitude q : ℂ) * Complex.exp ((phase q : ℂ) * Complex.I) *
      (weight q : ℂ) :=
  ((contDiff_ofReal_comp ha).mul (contDiff_exp_comp hp)).mul (contDiff_ofReal_comp hw)

lemma contDiff_carlesonF₀ {a ν : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hν : ContDiff ℝ ∞ ν) (σ : ℝ) :
    ContDiff ℝ ∞ (carlesonF₀ a ν σ) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₀ : ℝ → ℝ) := carlesonBump₀.contDiff (n := ⊤)
  unfold carlesonF₀
  exact contDiff_modulatedInput (by fun_prop) (by fun_prop) (by fun_prop)

lemma contDiff_carlesonF₁ {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (carlesonF₁ g) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₁ : ℝ → ℝ) := carlesonBump₁.contDiff (n := ⊤)
  unfold carlesonF₁
  refine (hg.comp (by fun_prop)).mul (contDiff_ofReal_comp ?_)
  fun_prop

lemma contDiff_carlesonF₂ {a ν : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hν : ContDiff ℝ ∞ ν) (σ : ℝ) :
    ContDiff ℝ ∞ (carlesonF₂ a ν σ) := by
  have hb : ContDiff ℝ ∞ (carlesonBump₁ : ℝ → ℝ) := carlesonBump₁.contDiff (n := ⊤)
  unfold carlesonF₂
  exact contDiff_modulatedInput (by fun_prop) (by fun_prop) (by fun_prop)

private lemma modulatedInput_eq_zero {a : ℝ → ℝ} {A : ℝ}
    (ha : ∀ x, A < |x| → a x = 0) (bump : ContDiffBump (0 : ℝ)) (phase : ℝ)
    (p : ℝ × ℝ) (hp : p ∉ Icc (-A) A ×ˢ Icc (-(A + bump.rOut)) (A + bump.rOut)) :
    (a p.1 : ℂ) * Complex.exp ((phase : ℂ) * Complex.I) * (bump (p.2 + p.1 / 2) : ℂ) = 0 := by
  by_cases first : A < |p.1|
  · simp [ha _ first]
  have second : A + bump.rOut < |p.2| := by
    by_contra h
    exact hp ⟨abs_le.mp (not_lt.mp first), abs_le.mp (not_lt.mp h)⟩
  have vanishes : bump (p.2 + p.1 / 2) = 0 := by
    apply carlesonBump_eq_zero
    have := abs_sub_abs_le_abs_sub p.2 (-(p.1 / 2))
    rw [sub_neg_eq_add, abs_neg, abs_div, abs_two] at this
    linarith [not_lt.mp first, abs_nonneg p.1]
  simp [vanishes]

lemma hasCompactSupport_carlesonF₀ {a : ℝ → ℝ} {A : ℝ} (ha : ∀ x, A < |x| → a x = 0)
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₀ a ν σ) := by
  exact HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) fun p hp =>
    modulatedInput_eq_zero ha carlesonBump₀ (σ * ν p.1 * (p.1 + p.2)) p hp

/-- The box containing the support of the second input. -/
def carlesonBox (L : ℝ) : Set (ℝ × ℝ) := Icc (-(L + 9)) (L + 9) ×ˢ Icc (-(L + 9)) (L + 9)

lemma isCompact_carlesonBox (L : ℝ) : IsCompact (carlesonBox L) := isCompact_Icc.prod isCompact_Icc

lemma carlesonF₁_eq_zero {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) {p : ℝ × ℝ}
    (hp : p ∉ carlesonBox L) : carlesonF₁ g p = 0 := by
  unfold carlesonBox at hp
  by_cases h₁ : L < |-p.1 - p.2|
  · simp [carlesonF₁, hg _ h₁]
  have h₂ : 9 ≤ |p.1 - p.2| := by
    by_contra h₂
    rw [not_lt, abs_le] at h₁
    rw [not_le, abs_lt] at h₂
    exact hp ⟨by constructor <;> linarith, by constructor <;> linarith⟩
  simp [carlesonF₁, carlesonBump_eq_zero carlesonBump₁ (x := p.1 - p.2) h₂]

lemma hasCompactSupport_carlesonF₁ {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) :
    HasCompactSupport (carlesonF₁ g) :=
  HasCompactSupport.intro (isCompact_carlesonBox L) fun _ hp => carlesonF₁_eq_zero hg hp

lemma hasCompactSupport_carlesonF₂ {a : ℝ → ℝ} {A : ℝ} (ha : ∀ x, A < |x| → a x = 0)
    (ν : ℝ → ℝ) (σ : ℝ) : HasCompactSupport (carlesonF₂ a ν σ) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(A + carlesonBump₁.rOut)) (b := A + carlesonBump₁.rOut)).prod
      (isCompact_Icc (a := -A) (b := A))) fun p hp => ?_
  exact modulatedInput_eq_zero ha carlesonBump₁ (σ * ν p.2 * p.1) p.swap fun h =>
    hp ⟨h.2, h.1⟩

/-- Coordinates `((x, t), u) ↦ ((x, y), z)` with `t = x + y + z` and `u = y + x/2`. -/
def carlesonCoord : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun q := ((q.1.1, q.2 - q.1.1 / 2), q.1.2 - q.2 - q.1.1 / 2)
  invFun q := ((q.1.1, q.1.1 + q.1.2 + q.2), q.1.2 + q.1.1 / 2)
  left_inv q := by ext <;> simp; ring
  right_inv q := by ext <;> simp; ring
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma measurePreserving_carlesonCoord : MeasurePreserving carlesonCoord := by
  have h₁ : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 - p.1 / 2)) := by
    refine (MeasurePreserving.id volume).skew_product (g := fun x u => u - x / 2) (by fun_prop)
      (ae_of_all _ fun x => ?_)
    exact (measurePreserving_sub_right volume (x / 2)).map_eq
  have h₂ : MeasurePreserving
      (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.1.2 - q.1.1 / 2), q.2 - q.1.2 - q.1.1 / 2)) := by
    refine h₁.skew_product (g := fun p t => t - p.2 - p.1 / 2) (by fun_prop)
      (ae_of_all _ fun p => ?_)
    have he : (fun t : ℝ => t - p.2 - p.1 / 2) = fun t => t - (p.2 + p.1 / 2) := by
      ext t; ring
    rw [he]
    exact (measurePreserving_sub_right volume _).map_eq
  have hA := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)
  have h₃ : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2), q.1.2)) :=
    (hA.symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ)))).comp hA)
  exact h₂.comp h₃

open Complex in
/-- The hard truncation in the coordinates `(x, t)`. -/
def carlesonH (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (p : ℝ × ℝ) : ℂ :=
  if ε < |p.2| then
    (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) * exp ((σ * ν p.1 * p.2 : ℝ) * I) / (p.2 : ℂ)
  else 0

/-- The triangular truncation integrand evaluated on the specialized inputs. -/
def carlesonTrunc (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) : (ℝ × ℝ) × ℝ → ℂ :=
  Triangular.truncatedIntegrand (carlesonF₀ a ν σ) (carlesonF₁ g) (carlesonF₂ a ν σ) ε

lemma carleson_integrand_coord (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (q : (ℝ × ℝ) × ℝ) :
    carlesonTrunc a ν g σ ε (carlesonCoord q) =
      carlesonH a ν g σ ε q.1 * (carlesonW q.1.2 q.2 : ℂ) := by
  obtain ⟨⟨x, t⟩, u⟩ := q
  rw [carlesonTrunc, Triangular.truncatedIntegrand_apply]
  change (if ε < |x + (u - x / 2) + (t - u - x / 2)| then
      carlesonF₀ a ν σ (x, u - x / 2) * carlesonF₁ g (u - x / 2, t - u - x / 2) *
        carlesonF₂ a ν σ (t - u - x / 2, x) / ((x + (u - x / 2) + (t - u - x / 2) : ℝ) : ℂ)
      else 0) = _
  rw [show x + (u - x / 2) + (t - u - x / 2) = t by ring]
  simp only [carlesonF₀, carlesonF₁, carlesonF₂, carlesonH, carlesonW]
  split_ifs
  · rw [show u - x / 2 + x / 2 = u by ring, show -(u - x / 2) - (t - u - x / 2) = x - t by ring,
      show u - x / 2 - (t - u - x / 2) = 2 * u - t by ring,
      show t - u - x / 2 + x / 2 = t - u by ring]
    have he : Complex.exp ((σ * ν x * (x + (u - x / 2)) : ℝ) * Complex.I) *
        Complex.exp ((σ * ν x * (t - u - x / 2) : ℝ) * Complex.I) =
        Complex.exp ((σ * ν x * t : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he]
    push_cast
    ring
  · simp

/-- Integrating out `u` turns the truncation into a modulated kernel in `(x, t)`. -/
lemma carleson_trunc_eq (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ)
    (hint : Integrable (carlesonTrunc a ν g σ ε)) :
    Integrable (fun p : ℝ × ℝ => carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ)) ∧
      ∫ q, carlesonTrunc a ν g σ ε q =
        ∫ p : ℝ × ℝ, carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ) := by
  have hemb := carlesonCoord.toHomeomorph.isClosedEmbedding.measurableEmbedding
  have hc : (fun q => carlesonTrunc a ν g σ ε (carlesonCoord q)) =
      fun q => carlesonH a ν g σ ε q.1 * (carlesonW q.1.2 q.2 : ℂ) :=
    funext (carleson_integrand_coord a ν g σ ε)
  have hi : Integrable (fun q : (ℝ × ℝ) × ℝ => carlesonH a ν g σ ε q.1 *
      (carlesonW q.1.2 q.2 : ℂ)) := by
    rw [← hc]
    exact (measurePreserving_carlesonCoord.integrable_comp_emb hemb).mpr hint
  have hw : ∀ p : ℝ × ℝ, ∫ u, carlesonH a ν g σ ε p * (carlesonW p.2 u : ℂ) =
      carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ) := fun p => by
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  rw [Measure.volume_eq_prod] at hi
  refine ⟨hi.integral_prod_left.congr (ae_of_all _ hw), ?_⟩
  rw [← measurePreserving_carlesonCoord.integral_comp hemb, hc, Measure.volume_eq_prod,
    integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ hw)

private lemma eLpNorm_modulatedInput {amplitude first second weight : ℝ × ℝ → ℝ}
    (ha : Measurable amplitude) (h₀ : Measurable first) (h₁ : Measurable second)
    (hw : Measurable weight) :
    eLpNorm (fun q => (amplitude q : ℂ) * Complex.exp ((first q : ℂ) * Complex.I) *
      (weight q : ℂ)) 3 volume =
    eLpNorm (fun q => (amplitude q : ℂ) * Complex.exp ((second q : ℂ) * Complex.I) *
      (weight q : ℂ)) 3 volume :=
  eLpNorm_congr_norm_ae (by fun_prop) (by fun_prop)
    (ae_of_all _ fun _ => by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I])

lemma eLpNorm_carlesonF₀ {a ν : ℝ → ℝ} (ha : Measurable a) (hν : Measurable ν) (σ : ℝ) :
    eLpNorm (carlesonF₀ a ν σ) 3 volume = eLpNorm (carlesonF₀ a ν 1) 3 volume := by
  have hb := carlesonBump₀.continuous.measurable
  unfold carlesonF₀
  exact eLpNorm_modulatedInput (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

lemma eLpNorm_carlesonF₂ {a ν : ℝ → ℝ} (ha : Measurable a) (hν : Measurable ν) (σ : ℝ) :
    eLpNorm (carlesonF₂ a ν σ) 3 volume = eLpNorm (carlesonF₂ a ν 1) 3 volume := by
  have hb := carlesonBump₁.continuous.measurable
  unfold carlesonF₂
  exact eLpNorm_modulatedInput (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The modulated sine form `∫∫ a(x)² g(x-t) m(t) sin(ν(x)t)/t`. -/
def carlesonForm (a ν : ℝ → ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
    ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ)

lemma abs_sin_mul_div_le (v t : ℝ) : |Real.sin (v * t) / t| ≤ |v| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [abs_div, div_le_iff₀ (abs_pos.mpr ht), ← abs_mul]
  exact Real.abs_sin_le_abs

lemma integrable_carlesonForm {a ν : ℝ → ℝ} {g : ℝ → ℂ} {B : ℝ}
    (ha : Measurable a) (hν : Measurable ν) (hg : Measurable g) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hi : Integrable fun x => a x ^ 2 * |ν x|) :
    Integrable fun p : ℝ × ℝ => (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
      ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) := by
  have hw := measurable_carlesonWeight
  refine ((hi.mul_prod integrable_carlesonWeight).const_mul B).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun p => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_div_assoc, abs_mul, abs_of_nonneg (carlesonWeight_nonneg _)]
  have h₁ := abs_sin_mul_div_le (ν p.1) p.2
  have h₂ := hgB (p.1 - p.2)
  have h₃ := carlesonWeight_nonneg p.2
  calc |a p.1| ^ 2 * ‖g (p.1 - p.2)‖ * (carlesonWeight p.2 * |Real.sin (ν p.1 * p.2) / p.2|)
      ≤ |a p.1| ^ 2 * B * (carlesonWeight p.2 * |ν p.1|) := by
        have : 0 ≤ B := (norm_nonneg _).trans h₂
        gcongr
    _ = B * (a p.1 ^ 2 * |ν p.1| * carlesonWeight p.2) := by rw [sq_abs]; ring

lemma exp_sub_exp_neg (θ : ℝ) :
    Complex.exp (θ * Complex.I) - Complex.exp ((-θ : ℝ) * Complex.I) =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
    Complex.sin_neg, Complex.ofReal_sin]
  ring

lemma ae_snd_ne_zero : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  exact QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
    (compl_mem_ae_iff.mpr (measure_singleton 0))

/-- The triangular theorem bounds the smooth modulated sine form. -/
theorem carleson_smooth_bound (bound : HasTriangularHilbertBound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ν : ℝ → ℝ) (g : ℝ → ℂ) (A L : ℝ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ ν → ContDiff ℝ ∞ g →
    (∀ x, A < |x| → a x = 0) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm a ν g‖ ≤ C * (eLpNorm (carlesonF₀ a ν 1) 3 volume).toReal *
      (eLpNorm (carlesonF₁ g) 3 volume).toReal * (eLpNorm (carlesonF₂ a ν 1) 3 volume).toReal := by
  obtain ⟨C, hC, hmain⟩ := bound
  refine ⟨C, hC, fun a ν g A L ha hν hg haA hgL => ?_⟩
  set e := C * (eLpNorm (carlesonF₀ a ν 1) 3 volume).toReal *
    (eLpNorm (carlesonF₁ g) 3 volume).toReal * (eLpNorm (carlesonF₂ a ν 1) 3 volume).toReal
  set w : ℝ × ℝ → ℂ := fun p => (carlesonWeight p.2 : ℂ)
  have hlim : ∀ σ : ℝ, ∃ l : ℂ, Tendsto (fun ε => ∫ p : ℝ × ℝ, carlesonH a ν g σ ε p * w p)
      (𝓝[>] 0) (𝓝 l) ∧ ‖l‖ ≤ e ∧
      ∀ ε > 0, Integrable fun p : ℝ × ℝ => carlesonH a ν g σ ε p * w p := by
    intro σ
    let S₀ := (hasCompactSupport_carlesonF₀ haA ν σ).toSchwartzMap (contDiff_carlesonF₀ ha hν σ)
    let S₁ := (hasCompactSupport_carlesonF₁ hgL).toSchwartzMap (contDiff_carlesonF₁ hg)
    let S₂ := (hasCompactSupport_carlesonF₂ haA ν σ).toSchwartzMap (contDiff_carlesonF₂ ha hν σ)
    have hint : ∀ ε > 0, Integrable (carlesonTrunc a ν g σ ε) := fun ε hε =>
      truncatedIntegrand_integrable S₀ S₁ S₂ hε
    obtain ⟨l, hl, hb⟩ := hmain S₀ S₁ S₂
    refine ⟨l, ?_, ?_, fun ε hε => (carleson_trunc_eq a ν g σ ε (hint ε hε)).1⟩
    · refine hl.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Triangular.truncatedForm_eq_integral]
      exact (carleson_trunc_eq a ν g σ ε (hint ε hε)).2
    · have hb' : ‖l‖ ≤ C * (eLpNorm (carlesonF₀ a ν σ) 3 volume).toReal *
          (eLpNorm (carlesonF₁ g) 3 volume).toReal *
          (eLpNorm (carlesonF₂ a ν σ) 3 volume).toReal := hb
      rwa [eLpNorm_carlesonF₀ ha.continuous.measurable hν.continuous.measurable,
        eLpNorm_carlesonF₂ ha.continuous.measurable hν.continuous.measurable] at hb'
  obtain ⟨l₁, h₁, hb₁, hi₁⟩ := hlim 1
  obtain ⟨l₂, h₂, hb₂, hi₂⟩ := hlim (-1)
  set f : ℝ × ℝ → ℂ := fun p => (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
    ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ)
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖g x‖ ≤ B :=
    (hg.continuous.norm.bddAbove_range_of_hasCompactSupport
      (hasCompactSupport_of_vanish hgL).norm).imp fun B hB x => hB ⟨x, rfl⟩
  have hf : Integrable f := by
    refine integrable_carlesonForm ha.continuous.measurable hν.continuous.measurable
      hg.continuous.measurable hB ?_
    refine (by fun_prop : Continuous fun x => a x ^ 2 * |ν x|).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (A := A) fun x hx => ?_)
    simp [haA x hx]
  have hdiff : ∀ ε > 0, (∫ p, carlesonH a ν g 1 ε p * w p) - ∫ p, carlesonH a ν g (-1) ε p * w p =
      ∫ p, {p : ℝ × ℝ | ε < |p.2|}.indicator (fun p => 2 * Complex.I * f p) p := by
    intro ε hε
    rw [← integral_sub (hi₁ ε hε) (hi₂ ε hε)]
    congr 1
    ext p
    simp only [carlesonH, indicator, mem_ofPred_eq, f, w, one_mul, neg_mul]
    split_ifs with h
    · rw [show ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) =
          (carlesonWeight p.2 : ℂ) * (Real.sin (ν p.1 * p.2) : ℂ) / (p.2 : ℂ) by push_cast; ring]
      linear_combination ((a p.1 : ℂ) ^ 2 * g (p.1 - p.2) / (p.2 : ℂ) *
        (carlesonWeight p.2 : ℂ)) * exp_sub_exp_neg (ν p.1 * p.2)
    · simp
  have hlim₂ : Tendsto (fun ε => ∫ p, {p : ℝ × ℝ | ε < |p.2|}.indicator
      (fun p => 2 * Complex.I * f p) p) (𝓝[>] 0) (𝓝 (∫ p, 2 * Complex.I * f p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖2 * Complex.I * f p‖)
      (Eventually.of_forall fun ε => (hf.const_mul _).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const (by fun_prop)))
      (Eventually.of_forall fun ε => ae_of_all _ fun p => norm_indicator_le_norm_self _ _)
      (hf.const_mul _).norm ?_
    filter_upwards [ae_snd_ne_zero] with p hp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (abs_pos.mpr hp))] with ε hε
    rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | ε < |p.2|} from hε)]
  have heq : 2 * Complex.I * carlesonForm a ν g = l₁ - l₂ := by
    rw [carlesonForm, ← integral_const_mul]
    refine tendsto_nhds_unique hlim₂ ((h₁.sub h₂).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hdiff ε hε
  have hn : ‖2 * Complex.I * carlesonForm a ν g‖ = 2 * ‖carlesonForm a ν g‖ := by simp
  have := norm_sub_le l₁ l₂
  rw [← heq, hn] at this
  linarith

end Specialization

section Norms

/-- An L³ bound for planar functions dominated by `|a(x)|` on a strip `|y + c x| ≤ r`. -/
lemma eLpNorm_toReal_le_of_strip {f : ℝ × ℝ → ℂ} {a : ℝ → ℝ} {r c : ℝ} (hr : 0 ≤ r)
    (ha : Measurable a) (ha₃ : Integrable fun x => |a x| ^ 3)
    (hf : ∀ p, ‖f p‖ ≤ |a p.1|) (hz : ∀ p, r < |p.2 + c * p.1| → f p = 0) :
    (eLpNorm f 3 volume).toReal ≤ (2 * r * ∫ x, |a x| ^ 3) ^ (1 / 3 : ℝ) := by
  set S := {p : ℝ × ℝ | |p.2 + c * p.1| ≤ r}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hpt : ∀ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ S.indicator (fun p => ‖a p.1‖ₑ ^ (3 : ℝ)) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp]
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hf p).trans_eq (Real.norm_eq_abs _).symm)
    · rw [hz p (lt_of_not_ge hp)]
      simp
  have hsec : ∀ x : ℝ, volume {y : ℝ | |y + c * x| ≤ r} = ENNReal.ofReal (2 * r) := by
    intro x
    have : {y : ℝ | |y + c * x| ≤ r} = Icc (-r - c * x) (r - c * x) := by
      ext y
      simp only [mem_ofPred_eq, mem_Icc, abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [this, Real.volume_Icc]
    ring_nf
  have hlin : ∫⁻ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ ENNReal.ofReal (2 * r) * ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) := by
    calc ∫⁻ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ ∫⁻ p, S.indicator (fun p => ‖a p.1‖ₑ ^ (3 : ℝ)) p :=
          lintegral_mono hpt
      _ = ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) * ENNReal.ofReal (2 * r) := by
          rw [Measure.volume_eq_prod, lintegral_prod _
            ((Measurable.indicator (by fun_prop) hS).aemeasurable)]
          congr 1
          ext x
          have : (fun y => S.indicator (fun p : ℝ × ℝ => ‖a p.1‖ₑ ^ (3 : ℝ)) (x, y)) =
              {y : ℝ | |y + c * x| ≤ r}.indicator fun _ => ‖a x‖ₑ ^ (3 : ℝ) := by
            ext y
            by_cases hy : |y + c * x| ≤ r <;> simp [S, indicator, hy]
          rw [this, lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const),
            hsec]
      _ = ENNReal.ofReal (2 * r) * ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) := by
          rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  have hI : ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) = ENNReal.ofReal (∫ x, |a x| ^ 3) := by
    rw [ofReal_integral_eq_lintegral_ofReal ha₃ (ae_of_all _ fun x => by positivity)]
    congr 1
    ext x
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
      (by norm_num)]
    norm_num
  have hnn : 0 ≤ ∫ x, |a x| ^ 3 := integral_nonneg fun x => by positivity
  by_cases hm : AEStronglyMeasurable f
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top]
    positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
  have h3 : (3 : ℝ≥0∞).toReal = 3 := by norm_num
  rw [h3, ← ENNReal.toReal_rpow]
  gcongr
  rw [hI, ← ENNReal.ofReal_mul (by positivity)] at hlin
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

lemma eLpNorm_carlesonF₁_le {g : ℝ → ℂ} {L B : ℝ} (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hg : ∀ x, L < |x| → g x = 0) :
    (eLpNorm (carlesonF₁ g) 3 volume).toReal ≤
      B * (volume (carlesonBox L)).toReal ^ (1 / 3 : ℝ) := by
  set K := carlesonBox L
  by_cases hm : AEStronglyMeasurable (carlesonF₁ g)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top]
    positivity
  have hle : eLpNorm (carlesonF₁ g) 3 volume ≤ eLpNorm (K.indicator fun _ => (B : ℂ)) 3 volume := by
    refine eLpNorm_mono hm fun p => ?_
    by_cases hp : p ∈ K
    · rw [indicator_of_mem hp, carlesonF₁, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs B, abs_of_nonneg hB, Real.norm_eq_abs,
        abs_of_nonneg carlesonBump₁.nonneg]
      exact (mul_le_of_le_one_right (norm_nonneg _) carlesonBump₁.le_one).trans (hgB _)
    · rw [carlesonF₁_eq_zero hg hp]
      simp
  have hfin : volume K ≠ (⊤ : ℝ≥0∞) := (isCompact_carlesonBox L).measure_lt_top.ne
  calc (eLpNorm (carlesonF₁ g) 3 volume).toReal
      ≤ (‖(B : ℂ)‖ₑ * volume K ^ (1 / (3 : ℝ≥0∞).toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin))
          (hle.trans (eLpNorm_indicator_const_le _ 3
            (isCompact_carlesonBox L).isClosed.measurableSet.nullMeasurableSet))
    _ = B * (volume K).toReal ^ (1 / 3 : ℝ) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
        simp [abs_of_nonneg hB]

end Norms

section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bumps of radius `2/(k+2)` used to mollify the rough data. -/
def carlesonMollifier (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (k + 2), 2 / (k + 2), by positivity, by gcongr; norm_num⟩

/-- The `k`-th mollification. -/
def carlesonMoll (k : ℕ) (h : ℝ → E) : ℝ → E :=
  (carlesonMollifier k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

lemma contDiff_carlesonMoll (k : ℕ) {h : ℝ → E} (hh : LocallyIntegrable h) :
    ContDiff ℝ ∞ (carlesonMoll k h) :=
  (carlesonMollifier k).hasCompactSupport_normed.contDiff_convolution_left _
    ((carlesonMollifier k).contDiff_normed (n := ⊤)) hh

lemma norm_carlesonMoll_le (k : ℕ) {h : ℝ → E} {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (x : ℝ) :
    ‖carlesonMoll k h x‖ ≤ B := by
  set φ := (carlesonMollifier k).normed volume
  rw [carlesonMoll, convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ t) (h (x - t))‖ ≤ ∫ t, φ t * B := by
        refine norm_integral_le_of_norm_le ((carlesonMollifier k).integrable_normed.mul_const B)
          (ae_of_all _ fun t => ?_)
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ((carlesonMollifier k).nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hB _) ((carlesonMollifier k).nonneg_normed t)
    _ = B := by rw [integral_mul_const, (carlesonMollifier k).integral_normed, one_mul]

lemma carlesonMoll_eq_zero (k : ℕ) {h : ℝ → E} {A : ℝ} (hh : ∀ x, A < |x| → h x = 0) {x : ℝ}
    (hx : A + 1 < |x|) : carlesonMoll k h x = 0 := by
  by_contra hne
  obtain ⟨s, hs, y, hy, rfl⟩ := support_convolution_subset _ (Function.mem_support.mpr hne)
  rw [(carlesonMollifier k).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  have hs' : |s| < 1 := hs.trans_le (by
    change 2 / ((k : ℝ) + 2) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hy' : |y| ≤ A := not_lt.mp fun h' => hy (hh y h')
  linarith [abs_add_le s y]

lemma ae_tendsto_carlesonMoll [CompleteSpace E] {h : ℝ → E} (hh : LocallyIntegrable h) :
    ∀ᵐ x, Tendsto (fun k => carlesonMoll k h x) atTop (𝓝 (h x)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := carlesonMollifier) (K := 2) ?_ (Eventually.of_forall fun k => ?_) hh
  · change Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  · change 2 / ((k : ℝ) + 2) ≤ 2 * (1 / ((k : ℝ) + 2))
    rw [mul_one_div]

end Mollify

section Rough

lemma ae_fst_of_ae {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P p.1 := by
  rw [Measure.volume_eq_prod]
  exact QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h

lemma ae_sub_of_ae {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P (p.1 - p.2) := by
  rw [Measure.volume_eq_prod]
  exact QuasiMeasurePreserving.ae (quasiMeasurePreserving_sub_of_right_invariant volume volume) h

/-- The triangular theorem bounds the modulated sine form for an indicator and rough data. -/
theorem carleson_rough_bound (bound : HasTriangularHilbertBound) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set ℝ) (ν : ℝ → ℝ) (g : ℝ → ℂ)
    (R V B : ℝ), MeasurableSet F → F ⊆ Icc (-R) R → Measurable ν → (∀ x, |ν x| ≤ V) →
    Measurable g → (∀ x, ‖g x‖ ≤ B) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm (F.indicator 1) ν g‖ ≤ K * B * (volume F).toReal ^ (2 / 3 : ℝ) := by
  obtain ⟨C, hC, hsm⟩ := carleson_smooth_bound bound
  set Vb := (volume (carlesonBox (L + 1))).toReal
  refine ⟨C * 4 ^ (1 / 3 : ℝ) * Vb ^ (1 / 3 : ℝ) * 18 ^ (1 / 3 : ℝ), by positivity, ?_⟩
  intro F ν g R V B hF hFR hν hνV hg hgB hgL
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0)
  set a : ℝ → ℝ := F.indicator 1
  set ν' : ℝ → ℝ := (Icc (-R) R).indicator ν
  have hRF : ∀ x, R < |x| → x ∉ F := fun x hx hxF =>
    (not_le.mpr hx) (abs_le.mpr (hFR hxF))
  have ha_m : Measurable a := measurable_const.indicator hF
  have hν'_m : Measurable ν' := hν.indicator measurableSet_Icc
  have ha_b : ∀ x, ‖a x‖ ≤ 1 := fun x => by by_cases hx : x ∈ F <;> simp [a, hx]
  have ha_z : ∀ x, R < |x| → a x = 0 := fun x hx => indicator_of_notMem (hRF x hx) _
  have hν'_b : ∀ x, ‖ν' x‖ ≤ V := fun x => by
    by_cases hx : x ∈ Icc (-R) R
    · simpa [ν', hx] using hνV x
    · simpa [ν', hx] using (abs_nonneg _).trans (hνV x)
  have hν'_z : ∀ x, R < |x| → ν' x = 0 := fun x hx =>
    indicator_of_notMem (show x ∉ Icc (-R) R from fun h => (not_le.mpr hx) (abs_le.mpr h)) _
  have ha_i := integrable_of_norm_le_of_vanish ha_m.aestronglyMeasurable ha_b ha_z
  have hν'_i := integrable_of_norm_le_of_vanish hν'_m.aestronglyMeasurable hν'_b hν'_z
  have hg_i := integrable_of_norm_le_of_vanish hg.aestronglyMeasurable hgB hgL
  set ak := fun k => carlesonMoll k a
  set νk := fun k => carlesonMoll k ν'
  set gk := fun k => carlesonMoll k g
  have hak_s : ∀ k, ContDiff ℝ ∞ (ak k) := fun k => contDiff_carlesonMoll k ha_i.locallyIntegrable
  have hνk_s : ∀ k, ContDiff ℝ ∞ (νk k) := fun k =>
    contDiff_carlesonMoll k hν'_i.locallyIntegrable
  have hgk_s : ∀ k, ContDiff ℝ ∞ (gk k) := fun k => contDiff_carlesonMoll k hg_i.locallyIntegrable
  have hak_b : ∀ k x, ‖ak k x‖ ≤ 1 := fun k => norm_carlesonMoll_le k ha_b
  have hνk_b : ∀ k x, ‖νk k x‖ ≤ V := fun k => norm_carlesonMoll_le k hν'_b
  have hgk_b : ∀ k x, ‖gk k x‖ ≤ B := fun k => norm_carlesonMoll_le k hgB
  have hak_z : ∀ k x, R + 1 < |x| → ak k x = 0 := fun k x => carlesonMoll_eq_zero k ha_z
  have hgk_z : ∀ k x, L + 1 < |x| → gk k x = 0 := fun k x => carlesonMoll_eq_zero k hgL
  have hak_3 : ∀ k, Integrable fun x => |ak k x| ^ 3 := fun k =>
    ((hak_s k).continuous.abs.pow 3).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (A := R + 1) fun x hx => by simp [hak_z k x hx])
  set I := fun k => ∫ x, |ak k x| ^ 3
  set v := (volume F).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hI : Tendsto I atTop (𝓝 v) := by
    have hva : v = ∫ x, |a x| ^ 3 := by
      have : (fun x => |a x| ^ 3) = F.indicator 1 := by
        ext x
        by_cases hx : x ∈ F <;> simp [a, hx]
      rw [this, integral_indicator_one hF]
      rfl
    rw [hva]
    refine tendsto_integral_of_dominated_convergence ((Icc (-(R + 1)) (R + 1)).indicator 1)
      (fun k => (hak_3 k).aestronglyMeasurable)
      ((integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])))
      (fun k => ae_of_all _ fun x => ?_) ?_
    · by_cases hx : x ∈ Icc (-(R + 1)) (R + 1)
      · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_one₀ (abs_nonneg _) (hak_b k x)
      · rw [hak_z k x (lt_of_not_ge fun h => hx (abs_le.mp h))]
        simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ae_tendsto_carlesonMoll ha_i.locallyIntegrable] with x hx
      exact ((continuous_abs.tendsto _).comp hx).pow 3
  have hk : ∀ k, ‖carlesonForm (ak k) (νk k) (gk k)‖ ≤
      C * (2 * 2 * I k) ^ (1 / 3 : ℝ) * (B * Vb ^ (1 / 3 : ℝ)) *
        (2 * 9 * I k) ^ (1 / 3 : ℝ) := by
    intro k
    refine (hsm (ak k) (νk k) (gk k) (R + 1) (L + 1) (hak_s k) (hνk_s k) (hgk_s k) (hak_z k)
      (hgk_z k)).trans ?_
    have h₀ : (eLpNorm (carlesonF₀ (ak k) (νk k) 1) 3 volume).toReal ≤
        (2 * 2 * I k) ^ (1 / 3 : ℝ) := by
      refine eLpNorm_toReal_le_of_strip (c := 1 / 2) (by norm_num) (hak_s k).continuous.measurable
        (hak_3 k) (fun p => ?_) (fun p hp => ?_)
      · simp only [carlesonF₀, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
          Real.norm_eq_abs, mul_one, abs_of_nonneg carlesonBump₀.nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) carlesonBump₀.le_one
      · rw [carlesonF₀, carlesonBump_eq_zero carlesonBump₀ (x := p.2 + p.1 / 2)
          (by change (2 : ℝ) ≤ _; rw [show p.2 + p.1 / 2 = p.2 + 1 / 2 * p.1 by ring]; exact hp.le)]
        simp
    have h₁ := eLpNorm_carlesonF₁_le hB (hgk_b k) (hgk_z k)
    have h₂ : (eLpNorm (carlesonF₂ (ak k) (νk k) 1) 3 volume).toReal ≤
        (2 * 9 * I k) ^ (1 / 3 : ℝ) := by
      rw [Measure.volume_eq_prod, ← eLpNorm_comp_measurePreserving
        (contDiff_carlesonF₂ (hak_s k) (hνk_s k) 1).continuous.aestronglyMeasurable
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))]
      refine eLpNorm_toReal_le_of_strip (c := 1 / 2) (by norm_num) (hak_s k).continuous.measurable
        (hak_3 k) (fun p => ?_) (fun p hp => ?_)
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, carlesonF₂, norm_mul,
          Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, mul_one,
          abs_of_nonneg carlesonBump₁.nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) carlesonBump₁.le_one
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, carlesonF₂]
        rw [carlesonBump_eq_zero carlesonBump₁ (x := p.2 + p.1 / 2)
          (by change (9 : ℝ) ≤ _; rw [show p.2 + p.1 / 2 = p.2 + 1 / 2 * p.1 by ring]; exact hp.le)]
        simp
    have e₀ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₀ (ak k) (νk k) 1) 3 volume)
    have e₁ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₁ (gk k)) 3 volume)
    have e₂ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₂ (ak k) (νk k) 1) 3 volume)
    gcongr
  have hw := measurable_carlesonWeight
  have hform : Tendsto (fun k => carlesonForm (ak k) (νk k) (gk k)) atTop
      (𝓝 (carlesonForm a ν' g)) := by
    set bd : ℝ × ℝ → ℝ := fun p =>
      (Icc (-(R + 1)) (R + 1)).indicator (fun _ => B * V) p.1 * carlesonWeight p.2
    have hbd : Integrable bd := ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (C := B * V) (by simp [Real.volume_Icc]))).mul_prod
        integrable_carlesonWeight
    refine tendsto_integral_of_dominated_convergence bd (fun k => Measurable.aestronglyMeasurable
      (by
        have := (hak_s k).continuous.measurable
        have := (hνk_s k).continuous.measurable
        have := (hgk_s k).continuous.measurable
        fun_prop)) hbd (fun k => ae_of_all _ fun p => ?_) ?_
    · simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_div_assoc, abs_mul, abs_of_nonneg (carlesonWeight_nonneg _)]
      by_cases hx : p.1 ∈ Icc (-(R + 1)) (R + 1)
      · simp only [bd, indicator_of_mem hx]
        have h₁ := abs_sin_mul_div_le (νk k p.1) p.2
        have h₂ := hgk_b k (p.1 - p.2)
        have h₃ := carlesonWeight_nonneg p.2
        have h₄ : |ak k p.1| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hak_b k p.1)
        have h₅ : |νk k p.1| ≤ V := hνk_b k p.1
        calc |ak k p.1| ^ 2 * ‖gk k (p.1 - p.2)‖ *
              (carlesonWeight p.2 * |Real.sin (νk k p.1 * p.2) / p.2|)
            ≤ 1 * B * (carlesonWeight p.2 * V) := by
              gcongr
              exact h₁.trans h₅
          _ = B * V * carlesonWeight p.2 := by ring
      · rw [hak_z k p.1 (lt_of_not_ge fun h => hx (abs_le.mp h))]
        simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hB
          ((abs_nonneg _).trans (hνV 0))) _) (carlesonWeight_nonneg _)
    · filter_upwards [ae_fst_of_ae (ae_tendsto_carlesonMoll ha_i.locallyIntegrable),
        ae_fst_of_ae (ae_tendsto_carlesonMoll hν'_i.locallyIntegrable),
        ae_sub_of_ae (ae_tendsto_carlesonMoll hg_i.locallyIntegrable)] with p h₁ h₂ h₃
      refine ((((Complex.continuous_ofReal.tendsto _).comp h₁).pow 2).mul h₃).mul
        ((Complex.continuous_ofReal.tendsto _).comp ?_)
      exact (tendsto_const_nhds.mul ((Real.continuous_sin.tendsto _).comp
        (h₂.mul_const p.2))).div_const p.2
  have hform' : carlesonForm a ν' g = carlesonForm a ν g := by
    unfold carlesonForm
    congr 1
    ext p
    by_cases hx : p.1 ∈ F
    · simp [ν', indicator_of_mem (hFR hx)]
    · simp [a, hx]
  have hR := ((tendsto_const_nhds (x := C)).mul (((hI.const_mul (2 * 2)).rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))))).mul (tendsto_const_nhds (x := B * Vb ^ (1 / 3 : ℝ)))
    |>.mul ((hI.const_mul (2 * 9)).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3)))
  have hlim := le_of_tendsto_of_tendsto' hform.norm hR hk
  rw [hform'] at hlim
  refine hlim.trans_eq ?_
  have hv₃ : v ^ (1 / 3 : ℝ) * v ^ (1 / 3 : ℝ) = v ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add' hv (by norm_num)]
    norm_num
  rw [Real.mul_rpow (by norm_num) hv, Real.mul_rpow (by norm_num) hv, ← hv₃]
  norm_num
  ring

end Rough

section Fourier

open Real

lemma fourierCoeffOn_one_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn zero_lt_one f n =
      ∫ t in (0 : ℝ)..1, f t * Complex.exp (-(2 * π * Complex.I * n * t)) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_one, div_one, one_smul, smul_eq_mul,
    Int.cast_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mul_comm]
  ring_nf

lemma fourierPartialSum_eq_exponential (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        fourierCoeffOn zero_lt_one f n * Complex.exp (2 * π * Complex.I * n * x) := by
  unfold fourierPartialSum
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]

/-- The Dirichlet kernel. -/
def dirichletKernel (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (2 * π * Complex.I * n * s)

lemma dirichletKernel_periodic (N : ℕ) : Function.Periodic (dirichletKernel N) 1 := by
  intro s
  unfold dirichletKernel
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (2 * π * Complex.I * n * ((s + 1 : ℝ) : ℂ)) =
      2 * π * Complex.I * n * s + n * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma continuous_dirichletKernel (N : ℕ) : Continuous (dirichletKernel N) := by
  unfold dirichletKernel
  fun_prop

lemma fourierPartialSum_eq_integral {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), f (x - s) * dirichletKernel N s := by
  have h₁ : fourierPartialSum f N x = ∫ t in (0 : ℝ)..1, f t * dirichletKernel N (x - t) := by
    simp only [fourierPartialSum_eq_exponential, fourierCoeffOn_one_eq_integral, dirichletKernel]
    simp_rw [← intervalIntegral.integral_mul_const, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum fun n _ => by
      apply Continuous.intervalIntegrable
      fun_prop]
    refine Finset.sum_congr rfl fun n _ => intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hper : Function.Periodic (fun t => f t * dirichletKernel N (x - t)) 1 := by
    intro t
    simp only
    rw [hp t, show x - (t + 1) = x - t - 1 by ring, ← dirichletKernel_periodic N (x - t - 1),
      sub_add_cancel]
  have h₂ := hper.intervalIntegral_add_eq 0 (x - 1 / 2)
  rw [zero_add] at h₂
  have h₃ : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), f (x - s) * dirichletKernel N s) =
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), (fun t => f t * dirichletKernel N (x - t)) (x - s) := by
    simp
  rw [h₁, h₂, h₃, intervalIntegral.integral_comp_sub_left
    (fun t => f t * dirichletKernel N (x - t)) x]
  congr 1; ring

lemma Icc_succ_eq (N : ℕ) :
    Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
      insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert]
  push_cast
  omega

/-- The closed form `D_N(s) sin(πs) = sin((2N+1)πs)` of the Dirichlet kernel. -/
lemma dirichletKernel_mul_sin (N : ℕ) (s : ℝ) :
    dirichletKernel N s * (Real.sin (π * s) : ℂ) = (Real.sin ((2 * N + 1) * π * s) : ℂ) := by
  set u := Complex.exp ((π * s : ℝ) * Complex.I)
  set v := Complex.exp ((-(π * s) : ℝ) * Complex.I)
  have huv : u * v = 1 := by
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, add_neg_cancel, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero]
  have hu : ∀ m : ℕ, Complex.exp ((m * (π * s) : ℝ) * Complex.I) = u ^ m := fun m => by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hv : ∀ m : ℕ, Complex.exp ((-(m * (π * s)) : ℝ) * Complex.I) = v ^ m := fun m => by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : ∀ N : ℕ, dirichletKernel N s * (u - v) = u ^ (2 * N + 1) - v ^ (2 * N + 1) := by
    intro N
    induction N with
    | zero => simp [dirichletKernel]
    | succ N ih =>
      have hD : dirichletKernel (N + 1) s =
          v ^ (2 * N + 2) + (u ^ (2 * N + 2) + dirichletKernel N s) := by
        rw [dirichletKernel, Icc_succ_eq, Finset.sum_insert (by simp; omega),
          Finset.sum_insert (by simp), ← hu, ← hv]
        congr 1
        · congr 1
          push_cast
          ring
        · congr 2
          push_cast
          ring
      rw [hD]
      linear_combination ih + (v ^ (2 * N + 1) - u ^ (2 * N + 1)) * huv
  have h₁ := exp_sub_exp_neg (π * s)
  have h₂ := exp_sub_exp_neg ((2 * N + 1 : ℕ) * (π * s))
  rw [hu, hv] at h₂
  have h₃ := key N
  rw [h₁, h₂] at h₃
  have h2I : (2 * Complex.I) ≠ 0 := by simp
  apply mul_left_cancel₀ h2I
  rw [show ((2 * N + 1) * π * s : ℝ) = ((2 * N + 1 : ℕ) : ℝ) * (π * s) by push_cast; ring]
  linear_combination h₃

lemma fourierCoeffOn_one_exp (k n : ℤ) :
    fourierCoeffOn zero_lt_one (fun x : ℝ => Complex.exp (2 * π * Complex.I * k * x)) n =
      if n = k then 1 else 0 := by
  have agreement :
      fourierCoeffOn zero_lt_one (fun x : ℝ => Complex.exp (2 * π * Complex.I * k * x)) n =
        fourierCoeff (T := 1) (fourier k) n := by
    rw [fourierCoeffOn_one_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, div_one, one_smul, fourier_coe_apply, Complex.ofReal_one, smul_eq_mul,
      Int.cast_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_comm]
    congr 2
    ring
  rw [agreement, fourierCoeff_fourier]
  simp [Pi.single_apply]

lemma fourierPartialSum_exp {k : ℤ} {N : ℕ} (hk : k.natAbs ≤ N) (x : ℝ) :
    fourierPartialSum (fun x => Complex.exp (2 * π * Complex.I * k * x)) N x =
      Complex.exp (2 * π * Complex.I * k * x) := by
  rw [fourierPartialSum_eq_exponential]
  simp_rw [fourierCoeffOn_one_exp, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', ite_eq_left (by simp only [Finset.mem_Icc]; omega)]

lemma fourierPartialSum_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (N : ℕ)
    (x : ℝ) : fourierPartialSum (fun t => f t + g t) N x =
      fourierPartialSum f N x + fourierPartialSum g N x := by
  simp only [fourierPartialSum_eq_exponential, fourierCoeffOn_one_eq_integral]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← add_mul, ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [add_mul]

lemma fourierPartialSum_smul (c : ℂ) (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSum (fun t => c * f t) N x = c * fourierPartialSum f N x := by
  simp only [fourierPartialSum_eq_exponential, fourierCoeffOn_one_eq_integral]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  ring

/-- Continuous functions on the circle whose Fourier partial sums eventually reproduce them. -/
def trigSubmodule : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {F | ∃ K : ℕ, ∀ N ≥ K, ∀ x : ℝ,
    fourierPartialSum (fun t => F (t : AddCircle (1 : ℝ))) N x = F x}
  zero_mem' := ⟨0, fun N _ x => by
    simp [fourierPartialSum_eq_exponential, fourierCoeffOn_one_eq_integral]⟩
  add_mem' := by
    rintro F G ⟨K₁, h₁⟩ ⟨K₂, h₂⟩
    refine ⟨max K₁ K₂, fun N hN x => ?_⟩
    have hF : Continuous fun t : ℝ => F t := F.continuous.comp continuous_quotient_mk'
    have hG : Continuous fun t : ℝ => G t := G.continuous.comp continuous_quotient_mk'
    simp only [ContinuousMap.add_apply]
    rw [fourierPartialSum_add hF hG, h₁ N (le_of_max_le_left hN), h₂ N (le_of_max_le_right hN)]
  smul_mem' := by
    rintro c F ⟨K, h⟩
    refine ⟨K, fun N hN x => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [fourierPartialSum_smul, h N hN]

lemma fourier_mem_trigSubmodule (k : ℤ) : fourier k ∈ trigSubmodule := by
  refine ⟨k.natAbs, fun N hN x => ?_⟩
  have he : ∀ t : ℝ, fourier k (t : AddCircle (1 : ℝ)) = Complex.exp (2 * π * Complex.I * k * t) :=
    fun t => by rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  simp_rw [he]
  exact fourierPartialSum_exp hN x

/-- Continuous 1-periodic functions are uniform limits of trigonometric polynomials. -/
lemma exists_trig_approx {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ P : ℝ → ℂ, Continuous P ∧ Function.Periodic P 1 ∧
      (∃ K : ℕ, ∀ N ≥ K, ∀ x, fourierPartialSum P N x = P x) ∧ ∀ x, ‖f x - P x‖ < δ := by
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hf⟩
  have hF : F ∈ (Submodule.span ℂ (range fourier)).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hF
  obtain ⟨Q, hQ, hd⟩ := hF δ hδ
  have hQ' : Q ∈ trigSubmodule :=
    Submodule.span_le.mpr (range_subset_iff.mpr fourier_mem_trigSubmodule) hQ
  refine ⟨fun t => Q t, Q.continuous.comp continuous_quotient_mk', fun t => ?_, hQ', fun x => ?_⟩
  · simp only [AddCircle.coe_add_period]
  · rw [← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist (f := F) (g := Q) (x : AddCircle (1 : ℝ))).trans_lt hd

end Fourier

section Kernel

open Real

lemma inv_sin_sub_inv_le {y : ℝ} (hy : 0 < y) (hy' : y ≤ π / 2) :
    0 ≤ 1 / Real.sin y - 1 / y ∧ 1 / Real.sin y - 1 / y ≤ 1 := by
  have hs₁ : 2 / π * y ≤ Real.sin y := Real.mul_le_sin hy.le hy'
  have hπ := Real.pi_pos
  have hπ₄ := Real.pi_le_four
  have hs₀ : 0 < Real.sin y := lt_of_lt_of_le (by positivity) hs₁
  have hs₂ : Real.sin y ≤ y := Real.sin_le hy.le
  have hs₃ : y - y ^ 3 / 6 ≤ Real.sin y := Real.sin_ge_sub_cube hy.le
  refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le hs₀ hs₂), ?_⟩
  rw [div_sub_div _ _ hs₀.ne' hy.ne', div_le_one (by positivity)]
  have h₁ : y ^ 3 / 6 * π ≤ 2 * y * y := by
    have : y * π ≤ 12 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr this)]
  have h₂ : 2 / π * y * y ≤ Real.sin y * y := mul_le_mul_of_nonneg_right hs₁ hy.le
  have h₃ : y ^ 3 / 6 ≤ 2 / π * y * y := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]
    linarith
  nlinarith

lemma abs_inv_sin_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |1 / Real.sin (π * s) - 1 / (π * s)| ≤ 1 := by
  have hπ := Real.pi_pos
  rcases lt_trichotomy s 0 with h | rfl | h
  · have := inv_sin_sub_inv_le (y := π * -s) (by nlinarith)
      (by rw [abs_of_neg h] at hs; nlinarith)
    rw [mul_neg, Real.sin_neg, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div] at this
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  · simp
  · have := inv_sin_sub_inv_le (y := π * s) (by positivity)
      (by rw [abs_of_pos h] at hs; nlinarith)
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

/-- The modulated kernel operator `x ↦ ∫ h(x-t) m(t) sin(ν(x)t)/t dt`. -/
def carlesonOp (h : ℝ → ℂ) (ν : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ t, h (x - t) * ((carlesonWeight t * Real.sin (ν x * t) / t : ℝ) : ℂ)

lemma norm_weight_sin_div_le (v t : ℝ) :
    ‖((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ)‖ ≤ |v| * carlesonWeight t := by
  rw [Complex.norm_real, Real.norm_eq_abs, mul_div_assoc, abs_mul,
    abs_of_nonneg (carlesonWeight_nonneg t), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_sin_mul_div_le v t) (carlesonWeight_nonneg t)

lemma integrable_carlesonOp_integrand {h : ℝ → ℂ} {B : ℝ} (hh : Measurable h)
    (hB : ∀ x, ‖h x‖ ≤ B) (v x : ℝ) :
    Integrable fun t => h (x - t) * ((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ) := by
  have hw := measurable_carlesonWeight
  refine (integrable_carlesonWeight.const_mul (B * |v|)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun t => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (hB _) (norm_weight_sin_div_le v t) (norm_nonneg _)
    ((norm_nonneg _).trans (hB 0))

/-- The Fourier partial sums differ from the modulated kernel by a uniformly bounded error. -/
lemma fourierPartialSum_sub_carlesonOp {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) {δ : ℝ} (hδ : ∀ x, ‖g x‖ ≤ δ) {R x : ℝ} (hx : |x| ≤ R) (N : ℕ) :
    ‖fourierPartialSum g N x - ((1 / (π * carlesonMass) : ℝ) : ℂ) *
      carlesonOp ((Icc (-(R + 11)) (R + 11)).indicator g) (fun _ => (2 * N + 1) * π) x‖ ≤
        22 * δ := by
  set M : ℝ := (2 * N + 1) * π
  set c : ℝ := 1 / (π * carlesonMass)
  set g' := (Icc (-(R + 11)) (R + 11)).indicator g
  have hm := carlesonMass_pos
  have hπ := Real.pi_pos
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have hg' : ∀ s, |s| ≤ 11 → g' (x - s) = g (x - s) := fun s hs => by
    refine indicator_of_mem ?_ _
    rw [mem_Icc, ← abs_le]
    exact (abs_sub _ _).trans (by linarith)
  have hg'B : ∀ y, ‖g' y‖ ≤ δ := fun y => by
    by_cases hy : y ∈ Icc (-(R + 11)) (R + 11)
    · rw [show g' y = g y from indicator_of_mem hy _]; exact hδ y
    · rw [show g' y = 0 from indicator_of_notMem hy _, norm_zero]; exact hδ0
  have hg'm : Measurable g' := hg.measurable.indicator measurableSet_Icc
  set A : ℝ → ℂ := (Ioc (-(1 / 2)) (1 / 2)).indicator fun s => g (x - s) * dirichletKernel N s
  set Bf : ℝ → ℂ := fun s => g' (x - s) * ((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)
  have hA : fourierPartialSum g N x = ∫ s, A s := by
    rw [fourierPartialSum_eq_integral hg hp, intervalIntegral.integral_of_le (by norm_num),
      integral_indicator measurableSet_Ioc]
  have hAi : Integrable A := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact ((by fun_prop : Continuous fun s => g (x - s)).mul
      (continuous_dirichletKernel N)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hBi : Integrable Bf := integrable_carlesonOp_integrand hg'm hg'B M x
  have hpt : ∀ s, s ≠ 0 → ‖A s - (c : ℂ) * Bf s‖ ≤
      (Icc (-11 : ℝ) 11).indicator (fun _ => δ) s := by
    intro s hs0
    by_cases hsI : s ∈ Ioc (-(1 / 2) : ℝ) (1 / 2)
    · have hs : |s| ≤ 1 / 2 := abs_le.mpr ⟨hsI.1.le, hsI.2⟩
      have hsin : Real.sin (π * s) ≠ 0 := by
        have h1 := abs_le.mp hs
        rw [Ne, Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith) (by nlinarith)]
        exact mul_ne_zero hπ.ne' hs0
      have hD : dirichletKernel N s = (Real.sin (M * s) : ℂ) / (Real.sin (π * s) : ℂ) := by
        rw [eq_div_iff (by exact_mod_cast hsin), dirichletKernel_mul_sin]
      rw [indicator_of_mem (show s ∈ Icc (-11 : ℝ) 11 from ⟨by linarith [hsI.1], by
        linarith [hsI.2]⟩), show A s = g (x - s) * dirichletKernel N s from indicator_of_mem hsI _]
      simp only [Bf, hg' s (by linarith), carlesonWeight_eq_mass (by linarith : |s| ≤ 2), hD]
      have he : (g (x - s) * ((Real.sin (M * s) : ℂ) / (Real.sin (π * s) : ℂ)) -
          (c : ℂ) * (g (x - s) * ((carlesonMass * Real.sin (M * s) / s : ℝ) : ℂ))) =
          g (x - s) * (Real.sin (M * s) : ℂ) *
            ((1 / Real.sin (π * s) - 1 / (π * s) : ℝ) : ℂ) := by
        have h1 : (carlesonMass : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        have h2 : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
        have h3 : ((Real.sin (π * s) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin
        rw [Complex.ofReal_sin, Complex.ofReal_mul] at h3
        have h3' : Complex.sin (s * π) ≠ 0 := by rwa [mul_comm]
        have h4 : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
        simp only [c]
        push_cast
        field_simp
      rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      calc ‖g (x - s)‖ * |Real.sin (M * s)| * |1 / Real.sin (π * s) - 1 / (π * s)|
          ≤ δ * 1 * 1 := by
            gcongr
            · exact hδ _
            · exact Real.abs_sin_le_one _
            · exact abs_inv_sin_sub_le hs
        _ = δ := by ring
    · rw [show A s = 0 from indicator_of_notMem hsI _, zero_sub, norm_neg]
      have hs : 1 / 2 ≤ |s| := by
        by_contra h
        rw [not_le, abs_lt] at h
        exact hsI ⟨h.1, h.2.le⟩
      by_cases h11 : |s| < 11
      · rw [indicator_of_mem (show s ∈ Icc (-11 : ℝ) 11 from abs_le.mp h11.le), norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < c), norm_mul]
        have hw : ‖((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)‖ ≤ 2 * carlesonMass := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
            abs_of_nonneg (carlesonWeight_nonneg s), div_le_iff₀ (by linarith)]
          have := Real.abs_sin_le_one (M * s)
          have := carlesonWeight_le_mass s
          have := carlesonWeight_nonneg s
          nlinarith
        calc c * (‖g' (x - s)‖ * ‖((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)‖)
            ≤ c * (δ * (2 * carlesonMass)) := by
              gcongr
              · exact hg'B _
            _ = δ * (2 / π) := by simp only [c]; field_simp
            _ ≤ δ := by
              have : 2 / π ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
              nlinarith
      · have h0 : Bf s = 0 := by simp [Bf, carlesonWeight_eq_zero (not_lt.mp h11)]
        rw [h0, mul_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => hδ0) _
  have hbd : Integrable ((Icc (-11 : ℝ) 11).indicator fun _ => δ) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (C := δ) (by simp))
  calc ‖fourierPartialSum g N x - (c : ℂ) * carlesonOp g' (fun _ => M) x‖
      = ‖∫ s, (A s - (c : ℂ) * Bf s)‖ := by
        rw [hA, integral_sub hAi (hBi.const_mul _), integral_const_mul]
        rfl
    _ ≤ ∫ s, (Icc (-11 : ℝ) 11).indicator (fun _ => δ) s :=
        norm_integral_le_of_norm_le hbd (by
          filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with s hs
          exact hpt s hs)
    _ = 22 * δ := by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
          smul_eq_mul]
        norm_num

end Kernel

section Maximal

open Real

lemma measurable_carlesonOp {h : ℝ → ℂ} {ν : ℝ → ℝ} (hh : Measurable h) (hν : Measurable ν) :
    Measurable (carlesonOp h ν) := by
  have hw := measurable_carlesonWeight
  have hm : Measurable fun p : ℝ × ℝ =>
      h (p.1 - p.2) * ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) := by
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

lemma norm_carlesonOp_le {h : ℝ → ℂ} {ν : ℝ → ℝ} {B V : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (hV : ∀ x, |ν x| ≤ V) (x : ℝ) :
    ‖carlesonOp h ν x‖ ≤ B * V * ∫ t, carlesonWeight t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc ‖carlesonOp h ν x‖ ≤ ∫ t, B * |ν x| * carlesonWeight t :=
        norm_integral_le_of_norm_le (integrable_carlesonWeight.const_mul _)
          (ae_of_all _ fun t => by
            rw [norm_mul, mul_assoc]
            exact mul_le_mul (hB _) (norm_weight_sin_div_le _ t) (norm_nonneg _) hB0)
    _ ≤ B * V * ∫ t, carlesonWeight t := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hV x) hB0)
          (integral_nonneg carlesonWeight_nonneg)

/-- The modulated form of an indicator is the integral of the operator over the set. -/
lemma carlesonForm_indicator {Q : Set ℝ} (hQ : MeasurableSet Q) {h : ℝ → ℂ} {ν : ℝ → ℝ}
    {B V : ℝ} (hh : Measurable h) (hν : Measurable ν) (hB : ∀ x, ‖h x‖ ≤ B)
    (hV : ∀ x, |ν x| ≤ V) (hQR : volume Q ≠ ⊤) :
    carlesonForm (Q.indicator 1) ν h = ∫ x in Q, carlesonOp h ν x := by
  have hi : Integrable fun x => Q.indicator (1 : ℝ → ℝ) x ^ 2 * |ν x| := by
    refine ((integrableOn_const (C := V) hQR).integrable_indicator hQ).mono'
      (Measurable.aestronglyMeasurable (by fun_prop (disch := exact hQ)))
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ Q
    · simp [hx, hV x]
    · simp [hx]
  have hint := integrable_carlesonForm (measurable_one.indicator hQ) hν hh hB hi
  rw [Measure.volume_eq_prod] at hint
  rw [carlesonForm, Measure.volume_eq_prod, integral_prod _ hint, ← integral_indicator hQ]
  congr 1
  ext x
  by_cases hx : x ∈ Q
  · simp [hx, carlesonOp]
  · simp [hx]

/-- A set on which the operator has large real part after rotation has controlled measure. -/
lemma volume_le_of_re_le {Q : Set ℝ} (hQ : MeasurableSet Q) (hQf : volume Q ≠ ⊤) {z : ℝ → ℂ}
    (hz : IntegrableOn z Q) {K B lam : ℝ} (hKB : 0 ≤ K * B) (hlam : 0 < lam)
    (hK : ‖∫ x in Q, z x‖ ≤ K * B * (volume Q).toReal ^ (2 / 3 : ℝ)) {u : ℂ} (hu : ‖u‖ = 1)
    (hre : ∀ x ∈ Q, lam ≤ (u * z x).re) : (volume Q).toReal ≤ (K * B / lam) ^ 3 := by
  set v := (volume Q).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have h₁ : lam * v ≤ K * B * v ^ (2 / 3 : ℝ) := by
    calc lam * v = ∫ x in Q, lam := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
      _ ≤ ∫ x in Q, (u * z x).re :=
          setIntegral_mono_on (integrableOn_const hQf) (hz.const_mul u).re hQ hre
      _ = (u * ∫ x in Q, z x).re := by
          rw [← integral_const_mul]
          exact integral_re (hz.const_mul u)
      _ ≤ ‖u * ∫ x in Q, z x‖ := Complex.re_le_norm _
      _ = ‖∫ x in Q, z x‖ := by rw [norm_mul, hu, one_mul]
      _ ≤ K * B * v ^ (2 / 3 : ℝ) := hK
  rcases hv.eq_or_lt with hv0 | hvpos
  · rw [← hv0]
    positivity
  have hsplit : v = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hvpos]
    norm_num
  have h₂ : lam * v ^ (1 / 3 : ℝ) ≤ K * B := by
    have hpos : 0 < v ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hvpos _
    have h₁' : lam * v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) ≤ K * B * v ^ (2 / 3 : ℝ) := by
      rw [mul_assoc, ← hsplit]
      exact h₁
    exact le_of_mul_le_mul_right h₁' hpos
  have h₃ : v ^ (1 / 3 : ℝ) ≤ K * B / lam := by
    rw [le_div_iff₀ hlam, mul_comm]
    exact h₂
  calc v = (v ^ (1 / 3 : ℝ)) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
        norm_num
    _ ≤ (K * B / lam) ^ 3 := pow_le_pow_left₀ (by positivity) h₃ 3

/-- Recursive linearization of the maximal frequency. -/
def carlesonLin (T : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => M 0
  | n + 1 => fun x => if lam < ‖T (n + 1) x‖ then M (n + 1) else carlesonLin T M lam n x

lemma carlesonLin_mem (T : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (lam : ℝ) (n : ℕ) (x : ℝ) :
    ∃ m ≤ n, carlesonLin T M lam n x = M m := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    simp only [carlesonLin]
    split_ifs
    · exact ⟨n + 1, le_rfl, rfl⟩
    · obtain ⟨m, hm, he⟩ := ih
      exact ⟨m, hm.trans (Nat.le_succ n), he⟩

lemma measurable_carlesonLin {T : ℕ → ℝ → ℂ} (hT : ∀ n, Measurable (T n)) (M : ℕ → ℝ)
    (lam : ℝ) (n : ℕ) : Measurable (carlesonLin T M lam n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_lt measurable_const (hT (n + 1)).norm)
      measurable_const ih

lemma lt_norm_carlesonLin {h : ℝ → ℂ} {M : ℕ → ℝ} {lam : ℝ} (n : ℕ) {x : ℝ}
    (hx : ∃ m ≤ n, lam < ‖carlesonOp h (fun _ => M m) x‖) :
    lam < ‖carlesonOp h (carlesonLin (fun m => carlesonOp h fun _ => M m) M lam n) x‖ := by
  induction n with
  | zero =>
    obtain ⟨m, hm, hl⟩ := hx
    obtain rfl := Nat.le_zero.mp hm
    exact hl
  | succ n ih =>
    by_cases hn : lam < ‖carlesonOp h (fun _ => M (n + 1)) x‖
    · have : carlesonLin (fun m => carlesonOp h fun _ => M m) M lam (n + 1) x = M (n + 1) := by
        simp [carlesonLin, hn]
      simpa [carlesonOp, this] using hn
    · have he : carlesonLin (fun m => carlesonOp h fun _ => M m) M lam (n + 1) x =
          carlesonLin (fun m => carlesonOp h fun _ => M m) M lam n x := by
        simp [carlesonLin, hn]
      obtain ⟨m, hm, hl⟩ := hx
      have hm' : m ≤ n := by
        rcases Nat.lt_or_ge m (n + 1) with h' | h'
        · exact Nat.lt_succ_iff.mp h'
        · exact absurd (le_antisymm hm h' ▸ hl) hn
      have := ih ⟨m, hm', hl⟩
      simpa [carlesonOp, he] using this

/-- Linearized maximal estimate for the modulated kernels at the Dirichlet frequencies. -/
theorem carleson_maximal (bound : HasTriangularHilbertBound) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℂ) (B lam : ℝ), Measurable h →
    (∀ x, ‖h x‖ ≤ B) → (∀ x, R + 11 < |x| → h x = 0) → 0 < lam →
    volume {x | x ∈ Icc (-R) R ∧ ∃ N : ℕ, lam < ‖carlesonOp h (fun _ => (2 * N + 1) * π) x‖} ≤
      ENNReal.ofReal (4 * (2 * K * B / lam) ^ 3) := by
  obtain ⟨K, hK0, hK⟩ := carleson_rough_bound bound (R + 11)
  refine ⟨K, hK0, fun h B lam hh hB hhz hlam => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set M : ℕ → ℝ := fun N => (2 * N + 1) * π
  have hM0 : ∀ n, 0 ≤ M n := fun n => by positivity
  have hMmono : Monotone M := fun m n hmn => by
    have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    have := Real.pi_pos
    simp only [M]
    nlinarith
  set T : ℕ → ℝ → ℂ := fun m => carlesonOp h fun _ => M m
  set E : ℕ → Set ℝ := fun n => {x | x ∈ Icc (-R) R ∧ ∃ m ≤ n, lam < ‖T m x‖}
  have hU : {x | x ∈ Icc (-R) R ∧ ∃ N : ℕ, lam < ‖carlesonOp h (fun _ => (2 * N + 1) * π) x‖} =
      ⋃ n, E n := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, E, T, M]
    constructor
    · rintro ⟨hx, N, hN⟩
      exact ⟨N, hx, N, le_rfl, hN⟩
    · rintro ⟨n, hx, m, -, hm⟩
      exact ⟨hx, m, hm⟩
  have hmono : Monotone E := fun m n hmn x ⟨hx, k, hk, hl⟩ => ⟨hx, k, hk.trans hmn, hl⟩
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  set ν := carlesonLin T M lam n
  have hνm : Measurable ν :=
    measurable_carlesonLin (fun m => measurable_carlesonOp hh measurable_const) M lam n
  have hνV : ∀ x, |ν x| ≤ M n := fun x => by
    obtain ⟨m, hm, he⟩ := carlesonLin_mem T M lam n x
    rw [show ν x = M m from he, abs_of_nonneg (hM0 m)]
    exact hMmono hm
  set z := carlesonOp h ν
  have hzm : Measurable z := measurable_carlesonOp hh hνm
  have hE : ∀ x ∈ E n, lam < ‖z x‖ := fun x hx => lt_norm_carlesonLin n hx.2
  set ωs : Fin 4 → ℂ := ![1, -1, -Complex.I, Complex.I]
  set Q : Fin 4 → Set ℝ := fun j => {x | x ∈ Icc (-R) R ∧ lam / 2 ≤ (ωs j * z x).re}
  have hcover : E n ⊆ ⋃ j, Q j := by
    intro x hx
    have h₁ := hE x hx
    have h₂ := Complex.norm_le_abs_re_add_abs_im (z x)
    simp only [mem_iUnion, Q, mem_ofPred_eq]
    by_cases hre : lam / 2 ≤ |(z x).re|
    · rcases le_abs.mp hre with h | h
      · exact ⟨0, hx.1, by simpa [ωs] using h⟩
      · exact ⟨1, hx.1, by simpa [ωs] using h⟩
    · have him : lam / 2 ≤ |(z x).im| := by linarith
      rcases le_abs.mp him with h | h
      · exact ⟨2, hx.1, by simpa [ωs] using h⟩
      · exact ⟨3, hx.1, by simpa [ωs] using h⟩
  have hQ : ∀ j, volume (Q j) ≤ ENNReal.ofReal ((2 * K * B / lam) ^ 3) := by
    intro j
    have hQm : MeasurableSet (Q j) := measurableSet_Icc.inter
      (measurableSet_le measurable_const (Complex.measurable_re.comp (hzm.const_mul _)))
    have hfin : volume (Q j) ≠ ⊤ :=
      ((measure_mono fun x hx => hx.1).trans_lt (by simp [Real.volume_Icc])).ne
    have hform := hK (Q j) ν h R (M n) B hQm (fun x hx => hx.1) hνm hνV hh hB hhz
    rw [carlesonForm_indicator hQm hh hνm hB hνV hfin] at hform
    have hzi : IntegrableOn z (Q j) :=
      Measure.integrableOn_of_bounded hfin hzm.aestronglyMeasurable
        (ae_of_all _ (norm_carlesonOp_le hB hνV))
    have hω : ‖ωs j‖ = 1 := by fin_cases j <;> simp [ωs]
    have hv := volume_le_of_re_le hQm hfin hzi (mul_nonneg hK0 hB0) (half_pos hlam) hform hω
      (fun x hx => hx.2)
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal (hv.trans_eq ?_)
    congr 1
    field_simp
  calc volume (E n) ≤ volume (⋃ j, Q j) := measure_mono hcover
    _ ≤ ∑ j, volume (Q j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin 4, ENNReal.ofReal ((2 * K * B / lam) ^ 3) := Finset.sum_le_sum fun j _ => hQ j
    _ = ENNReal.ofReal (4 * (2 * K * B / lam) ^ 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_mul (by norm_num),
          nsmul_eq_mul]
        norm_num

end Maximal

section Main

open Real

/-- The scalar triangular estimate implies almost-everywhere Fourier convergence
for continuous functions of period one. -/
theorem carleson_of_triangular_bound (bound : HasTriangularHilbertBound) {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  have hm := carlesonMass_pos
  have hπ := Real.pi_pos
  have key : ∀ R j : ℕ, volume {x | x ∈ Icc (-(R : ℝ)) R ∧
      ∃ᶠ N in atTop, 1 / ((j : ℝ) + 1) < ‖fourierPartialSum f N x - f x‖} = 0 := by
    intro R j
    set lam : ℝ := 1 / ((j : ℝ) + 1)
    have hlam : 0 < lam := by positivity
    set lam₀ := π * carlesonMass * (lam / 2)
    have hlam₀ : 0 < lam₀ := by positivity
    obtain ⟨K, -, hK⟩ := carleson_maximal bound R
    set S := {x | x ∈ Icc (-(R : ℝ)) R ∧
      ∃ᶠ N in atTop, lam < ‖fourierPartialSum f N x - f x‖}
    have hbound : ∀ δ ∈ Ioo (0 : ℝ) (lam / 46),
        volume S ≤ ENNReal.ofReal (4 * (2 * K * δ / lam₀) ^ 3) := by
      rintro δ ⟨hδ, hδ'⟩
      obtain ⟨P, hPc, hPp, ⟨K₀, hK₀⟩, hfP⟩ := exists_trig_approx hf hp hδ
      set g := fun x => f x - P x
      have hgc : Continuous g := hf.sub hPc
      have hgp : Function.Periodic g 1 := fun x => by simp only [g, hp x, hPp x]
      have hgδ : ∀ x, ‖g x‖ ≤ δ := fun x => (hfP x).le
      set g' := (Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11)).indicator g
      have hg'm : Measurable g' := hgc.measurable.indicator measurableSet_Icc
      have hg'B : ∀ x, ‖g' x‖ ≤ δ := fun x => by
        by_cases hx : x ∈ Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11)
        · rw [show g' x = g x from indicator_of_mem hx _]; exact hgδ x
        · rw [show g' x = 0 from indicator_of_notMem hx _, norm_zero]; exact hδ.le
      have hg'z : ∀ x, (R : ℝ) + 11 < |x| → g' x = 0 := fun x hx =>
        indicator_of_notMem (show x ∉ Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11) from
          fun h => (not_le.mpr hx) (abs_le.mpr h)) _
      refine le_trans (measure_mono ?_) (hK g' δ lam₀ hg'm hg'B hg'z hlam₀)
      rintro x ⟨hx, hfr⟩
      refine ⟨hx, ?_⟩
      obtain ⟨N, hN, hNK⟩ := (hfr.and_eventually (eventually_ge_atTop K₀)).exists
      refine ⟨N, ?_⟩
      have hsplit : fourierPartialSum f N x - f x = fourierPartialSum g N x - g x := by
        have : fourierPartialSum f N x = fourierPartialSum g N x + fourierPartialSum P N x := by
          rw [← fourierPartialSum_add hgc hPc]
          simp [g]
        rw [this, hK₀ N hNK x]
        simp only [g]
        ring
      rw [hsplit] at hN
      have hd : ‖fourierPartialSum g N x - ((1 / (π * carlesonMass) : ℝ) : ℂ) *
          carlesonOp g' (fun _ => (2 * N + 1) * π) x‖ ≤ 22 * δ :=
        fourierPartialSum_sub_carlesonOp hgc hgp hgδ (abs_le.mpr hx) N
      have h₁ := norm_sub_le (fourierPartialSum g N x) (g x)
      have h₂ := norm_le_insert' (fourierPartialSum g N x) (((1 / (π * carlesonMass) : ℝ) : ℂ) *
        carlesonOp g' (fun _ => (2 * N + 1) * π) x)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h₂
      have h₃ : lam / 2 <
          1 / (π * carlesonMass) * ‖carlesonOp g' (fun _ => (2 * N + 1) * π) x‖ := by
        linarith [hgδ x]
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity)] at h₃
      change π * carlesonMass * (lam / 2) < _
      linarith
    have hlim : Tendsto (fun δ => ENNReal.ofReal (4 * (2 * K * δ / lam₀) ^ 3)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun δ : ℝ => 4 * (2 * K * δ / lam₀) ^ 3) (𝓝 0) (𝓝 0) := by
        have : Continuous fun δ : ℝ => 4 * (2 * K * δ / lam₀) ^ 3 := by fun_prop
        simpa using this.tendsto 0
      simpa using (ENNReal.tendsto_ofReal h).mono_left nhdsWithin_le_nhds
    refine nonpos_iff_eq_zero.mp (ge_of_tendsto hlim ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < lam / 46 by positivity)] with δ hδ
    exact hbound δ hδ
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun R : ℕ =>
    measure_iUnion_null fun j : ℕ => key R j)
  intro x hx
  simp only [mem_ofPred_eq, Metric.tendsto_atTop, not_forall, not_exists, not_lt] at hx
  obtain ⟨ε, hε, hfreq⟩ := hx
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  simp only [mem_iUnion]
  refine ⟨⌈|x|⌉₊, j, ?_, ?_⟩
  · rw [mem_Icc, ← abs_le]
    exact Nat.le_ceil _
  · rw [Filter.frequently_atTop]
    intro N₀
    obtain ⟨N, hN, hd⟩ := hfreq N₀
    exact ⟨N, hN, by rw [← dist_eq_norm]; linarith⟩

end Main

/-- The completed application of the triangular estimate to periodic Fourier convergence. -/
private theorem carleson {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 (f x)) :=
  carleson_of_triangular_bound triangularHilbert_main hf hp

end

end Triangular.Auto
