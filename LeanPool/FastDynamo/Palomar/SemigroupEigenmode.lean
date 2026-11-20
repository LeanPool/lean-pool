/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.FourierDictionary

/-!
# Eigenmodes of an abstract induction semigroup

This module derives the consequences of an eigenmode of the induction operator for an arbitrary
semigroup `S` with `IsInductionSemigroup u ε S` in the sense of the Challenge statement.  Nothing
here depends on a particular velocity or semigroup: the arguments use only the four fields of
`IsInductionSemigroup`, Fourier injectivity and Parseval on `L2 = L²(𝕋³;ℂ³)`.  No regularity of
the velocity `u : T3 → R3` is needed: the eigen-equation is stated through `inductionRHS`, and the
only property of `u` that enters is that it is real-valued.

Let `V ∈ H² ∩ L²_σ` with `inductionRHS u ε V = λ V̂`.

* **The orbit of an eigenmode** (`isInductionSemigroup_apply_eigenmode`).  `S t V = e^{tλ} V` for
  every `t ≥ 0`.  The generator field gives `D ∈ L²_σ` with `D̂ = inductionRHS u ε V = λ V̂`, so
  `D = λ V`; the semigroup law turns this into the right derivative `λ S t V` of `t ↦ S t V` at
  every `t ≥ 0`, and `e^{-tλ} S t V` has right derivative `0`, hence is constant.
* **Growth** (`exp_mul_le_norm_of_eigenmode`).  If `V ≠ 0` and `γ₀ ≤ Re λ`, then
  `e^{γ₀ t} ≤ ‖S t‖` for every `t ≥ 0`.
* **Conjugation** (`conjL2`).  Coordinatewise complex conjugation on `L2` is conjugate-linear,
  acts on Fourier coefficients by `(conj B)ᵢ^(m) = conj (B̂ᵢ(-m))`
  (`mFourierCoeff_conjL2`), preserves `L²_σ`, `H²` and the norm, and, since `u` is real, maps an
  eigenmode for `λ` to an eigenmode for `conj λ` (`inductionRHS_conjL2`).
* **The real part** (`re3L2 W = (W + conj W)/2`, a representative of `x ↦ re3 (W x)`).  If
  the coefficients of `W` live on the plane `m₃ = K` with `K ≠ 0`, those of `conj W` live on
  `m₃ = -K`, so `W ⟂ conj W` and `‖Re W‖² = ‖W‖²/2` (`norm_sq_re3L2`).
* **The growing real solution** (`exists_realPart_eigenmode`).  For an eigenmode supported on
  `m₃ = K ≠ 0`, the datum `B_in = Re V` is non-zero, lies in `H² ∩ L²_σ`, and its orbit under any
  `S` with `IsInductionSemigroup u ε S` is `Re (e^{tλ} V)`, of norm `e^{t Re λ} ‖B_in‖`.

The growth clause (`forall_exp_mul_le_norm_of_eigenmode`) and the inner block of the eigenmode
clause (`exists_realPart_eigenmode`) have exactly the shape of the corresponding parts of the
Challenge statement; `eigenmode_clauses` combines them.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Set Filter Topology
open scoped ComplexConjugate NNReal

/-! ## The orbit of an eigenmode -/

section Orbit

variable {u : T3 → R3} {ε : ℝ} {S : ℝ≥0 → L2σ →L[ℂ] L2σ}

/-- The generator of an induction semigroup at an eigenmode: the derivative field `D` of the
generator clause is `λ V`. -/
theorem isInductionSemigroup_hasDerivWithinAt_eigenmode (hS : IsInductionSemigroup u ε S)
    {lam : ℂ} {V : L2σ} (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) :
    HasDerivWithinAt (fun t : ℝ ↦ S t.toNNReal V) (lam • V) (Ici 0) 0 := by
  obtain ⟨D, hD, hDc⟩ := hS.generator V hH2
  have hDeq : D = lam • V := by
    refine Subtype.ext (l2_ext_mFourierCoeff fun m i ↦ ?_)
    rw [hDc, heig, Submodule.coe_smul, mFourierCoeff_l2_smul]
  rw [← hDeq]
  rw [hasDerivWithinAt_iff_isLittleO] at hD ⊢
  rw [← Asymptotics.isLittleO_norm_left] at hD ⊢
  convert hD using 2 with h
  rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sub, ← Submodule.coe_sub, Submodule.norm_coe]

/-- The orbit of an eigenmode has the right derivative `λ S t V` at every `t ≥ 0`. -/
theorem isInductionSemigroup_hasDerivWithinAt_orbit_eigenmode (hS : IsInductionSemigroup u ε S)
    {lam : ℂ} {V : L2σ} (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t : ℝ ↦ S t.toNNReal V) (lam • S s.toNNReal V) (Ici s) s := by
  have h0 := isInductionSemigroup_hasDerivWithinAt_eigenmode hS hH2 heig
  have h1 : HasDerivWithinAt (fun h : ℝ ↦ S s.toNNReal (S h.toNNReal V))
      (S s.toNNReal (lam • V)) (Ici 0) 0 :=
    ((S s.toNNReal).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h0
  have h2 := h1.scomp_of_eq s ((hasDerivAt_id s).sub_const s).hasDerivWithinAt
    (fun r hr ↦ sub_nonneg.2 (mem_Ici.1 hr)) (sub_self s).symm
  simp only [one_smul, map_smul] at h2
  refine h2.congr (fun r hr ↦ ?_) ?_
  · have hr' : s ≤ r := mem_Ici.1 hr
    simp only [Function.comp_apply, id_eq]
    rw [← ContinuousLinearMap.comp_apply, ← hS.map_add, ← Real.toNNReal_add hs (sub_nonneg.2 hr'),
      add_sub_cancel]
  · simp only [Function.comp_apply, id_eq, sub_self, Real.toNNReal_zero, hS.map_zero,
      ContinuousLinearMap.id_apply]

/-- **A1, the orbit of an eigenmode.**  If `V ∈ H² ∩ L²_σ` satisfies the eigen-equation
`inductionRHS u ε V = λ V̂`, then every induction semigroup maps it to `e^{tλ} V`. -/
theorem isInductionSemigroup_apply_eigenmode (hS : IsInductionSemigroup u ε S)
    {lam : ℂ} {V : L2σ} (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) (t : ℝ≥0) :
    S t V = Complex.exp (t * lam) • V := by
  set z : ℝ → L2σ := fun r ↦ S r.toNNReal V with hz
  set w : ℝ → L2σ := fun r ↦ Complex.exp (-((r : ℂ) * lam)) • z r with hw
  have hzc : Continuous z := (hS.continuous V).comp continuous_real_toNNReal
  have hwc : Continuous w :=
    ((Complex.continuous_ofReal.mul continuous_const).neg.cexp).smul hzc
  have hderiv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt w 0 (Ici s) s := by
    intro s hs
    have hc : HasDerivAt (fun r : ℝ ↦ Complex.exp (-((r : ℂ) * lam)))
        (Complex.exp (-((s : ℂ) * lam)) * -(1 * lam)) s :=
      (((hasDerivAt_id s).ofReal_comp).mul_const lam).neg.cexp
    have h := hc.hasDerivWithinAt.smul
      (isInductionSemigroup_hasDerivWithinAt_orbit_eigenmode hS hH2 heig hs.1)
    convert h using 1
    rw [smul_smul, ← add_smul]
    simp
  have hconst := constant_of_has_deriv_right_zero hwc.continuousOn hderiv t
    ⟨t.2, le_rfl⟩
  simp only [hw, hz, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_smul,
    Real.toNNReal_zero, hS.map_zero, ContinuousLinearMap.id_apply, Real.toNNReal_coe] at hconst
  calc S t V = Complex.exp (t * lam) • (Complex.exp (-((t : ℂ) * lam)) • S t V) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp (t * lam) • V := by rw [hconst]

/-- **A1, growth.**  If an induction semigroup has a non-zero eigenmode `V ∈ H² ∩ L²_σ` with
eigenvalue `λ` and `γ₀ ≤ Re λ`, then `e^{γ₀ t} ≤ ‖S t‖` for every `t ≥ 0`. -/
theorem exp_mul_le_norm_of_eigenmode (hS : IsInductionSemigroup u ε S) {lam : ℂ} {V : L2σ}
    (hV : V ≠ 0) (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) {γ₀ : ℝ} (hγ : γ₀ ≤ lam.re) (t : ℝ≥0) :
    Real.exp (γ₀ * t) ≤ ‖S t‖ := by
  have hVpos : 0 < ‖V‖ := norm_pos_iff.2 hV
  have h := (S t).le_opNorm V
  rw [isInductionSemigroup_apply_eigenmode hS hH2 heig t, norm_smul, Complex.norm_exp,
    Complex.re_ofReal_mul] at h
  refine le_trans ?_ (le_of_mul_le_mul_right h hVpos)
  rw [mul_comm (t : ℝ)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hγ t.2)

end Orbit

/-! ## Conjugation -/

/-- Coordinatewise complex conjugation on `ℂ³`, a conjugate-linear isometry. -/
def starC3 : C3 →L⋆[ℂ] C3 :=
  LinearMap.mkContinuous
    { toFun := fun v ↦ WithLp.toLp 2 fun i ↦ conj (v i)
      map_add' := fun v w ↦ by ext i; simp
      map_smul' := fun c v ↦ by ext i; simp }
    1 fun v ↦ by simp [EuclideanSpace.norm_eq]

/-- The coordinates of the conjugate vector. -/
@[simp] theorem starC3_apply (v : C3) (i : Fin 3) : starC3 v i = conj (v i) := rfl

/-- Coordinatewise complex conjugation of fields, `B ↦ (x ↦ conj (B x))`, as a conjugate-linear
continuous map of `L²(𝕋³;ℂ³)`. -/
def conjL2 : L2 →L⋆[ℂ] L2 := starC3.compLpL 2 volume

/-- The conjugate field is the pointwise conjugate, almost everywhere. -/
theorem conjL2_coe_ae (B : L2) : ∀ᵐ x ∂volume, conjL2 B x = starC3 (B x) :=
  starC3.coeFn_compLpL B

/-- The Fourier coefficients of the conjugate of a scalar function:
`(conj f)^(m) = conj (f̂(-m))`.  No integrability is needed: both sides are junk values together. -/
theorem mFourierCoeff_conj (f : T3 → ℂ) (m : Fin 3 → ℤ) :
    mFourierCoeff (fun x ↦ conj (f x)) m = conj (mFourierCoeff f (-m)) := by
  rw [mFourierCoeff_eq_integral_volume, mFourierCoeff_eq_integral_volume, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [mFourier_neg]

/-- The Fourier coefficients of the conjugate field: `(conj B)ᵢ^(m) = conj (B̂ᵢ(-m))`. -/
theorem mFourierCoeff_conjL2 (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ conjL2 B x i) m = conj (mFourierCoeff (fun x ↦ B x i) (-m)) := by
  rw [← mFourierCoeff_conj]
  refine mFourierCoeff_congr_ae ?_ m
  filter_upwards [conjL2_coe_ae B] with x hx
  rw [hx, starC3_apply]

/-- Products with a real scalar field: `(f · conj B)ᵢ^(m) = conj ((f Bᵢ)^(-m))`. -/
theorem mFourierCoeff_real_mul_conjL2 (f : T3 → ℝ) (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ ((f x : ℝ) : ℂ) * conjL2 B x i) m =
      conj (mFourierCoeff (fun x ↦ ((f x : ℝ) : ℂ) * B x i) (-m)) := by
  rw [← mFourierCoeff_conj]
  refine mFourierCoeff_congr_ae ?_ m
  filter_upwards [conjL2_coe_ae B] with x hx
  rw [hx, starC3_apply, map_mul, Complex.conj_ofReal]

/-- **Conjugation and the induction operator.**  Since the velocity is real,
`inductionRHS u ε (conj B) m = conj (inductionRHS u ε B (-m))`. -/
theorem inductionRHS_conjL2 (u : T3 → R3) (ε : ℝ) (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    inductionRHS u ε ⇑(conjL2 B) m i = conj (inductionRHS u ε ⇑B (-m) i) := by
  simp only [inductionRHS, mFourierCoeff_real_mul_conjL2 (fun x ↦ u x _), mFourierCoeff_conjL2,
    map_sub, map_mul, map_sum, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    map_intCast, map_pow, Pi.neg_apply, Int.cast_neg, Complex.ofReal_neg, neg_sq]
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]

/-- Conjugation is an involution. -/
@[simp] theorem conjL2_conjL2 (B : L2) : conjL2 (conjL2 B) = B :=
  l2_ext_mFourierCoeff fun m i ↦ by simp [mFourierCoeff_conjL2]

/-- Conjugation preserves the solenoidal subspace. -/
theorem conjL2_mem_L2σ {B : L2} (hB : B ∈ L2σ) : conjL2 B ∈ L2σ := by
  rw [mem_L2σ_iff] at hB ⊢
  intro m
  have h := congrArg (fun z ↦ -conj z) (hB (-m))
  simpa [mFourierCoeff_conjL2, ← Finset.sum_neg_distrib] using h

/-- The `H²` summand at `-m` is the summand at `m`. -/
theorem h2Weight_neg (m : Fin 3 → ℤ) :
    (∑ i, (((-m) i : ℤ) : ℝ) ^ 2) ^ 2 = (∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ 2 := by
  simp

/-- Conjugation preserves `H²`. -/
theorem memH2_conjL2 {B : L2} (hB : MemH2 ⇑B) : MemH2 ⇑(conjL2 B) := by
  have h := hB.comp_injective neg_injective
  refine h.congr fun m ↦ ?_
  simp only [Function.comp_apply, mFourierCoeff_conjL2, Complex.norm_conj, h2Weight_neg]

/-- **Plancherel for the conjugate.** -/
theorem norm_conjL2 (B : L2) : ‖conjL2 B‖ = ‖B‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_l2_eq_tsum, norm_sq_l2_eq_tsum]
  simp only [mFourierCoeff_conjL2, Complex.norm_conj]
  exact (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun m ↦ ∑ i, ‖mFourierCoeff (fun x ↦ B x i) m‖ ^ 2)

/-- The conjugate of an eigenmode for `λ` is an eigenmode for `conj λ`. -/
theorem inductionRHS_conjL2_eigen {u : T3 → R3} {ε : ℝ} {lam : ℂ} {B : L2}
    (heig : ∀ m i, inductionRHS u ε ⇑B m i = lam * mFourierCoeff (fun x ↦ B x i) m)
    (m : Fin 3 → ℤ) (i : Fin 3) :
    inductionRHS u ε ⇑(conjL2 B) m i = conj lam * mFourierCoeff (fun x ↦ conjL2 B x i) m := by
  rw [inductionRHS_conjL2, heig, map_mul, mFourierCoeff_conjL2]

/-! ## The real part -/

/-- The real part `(W + conj W)/2` of a field of `L²(𝕋³;ℂ³)`. -/
def re3L2 (W : L2) : L2 := (2⁻¹ : ℂ) • (W + conjL2 W)

/-- The real part is a representative of `x ↦ re3 (W x)`. -/
theorem re3L2_coe_ae (W : L2) : ⇑(re3L2 W) =ᵐ[volume] fun x ↦ re3 (W x) := by
  filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (W + conjL2 W), Lp.coeFn_add W (conjL2 W),
    conjL2_coe_ae W] with x h1 h2 h3
  rw [re3L2, h1, Pi.smul_apply, h2, Pi.add_apply, h3]
  ext i
  simp only [re3, PiLp.smul_apply, PiLp.add_apply, starC3_apply, smul_eq_mul,
    Complex.re_eq_add_conj]
  ring

/-- The Fourier coefficients of the real part: `(Re W)ᵢ^(m) = (Ŵᵢ(m) + conj (Ŵᵢ(-m)))/2`. -/
theorem mFourierCoeff_re3L2 (W : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ re3L2 W x i) m =
      2⁻¹ * (mFourierCoeff (fun x ↦ W x i) m + conj (mFourierCoeff (fun x ↦ W x i) (-m))) := by
  rw [re3L2, mFourierCoeff_l2_smul, mFourierCoeff_l2_add, mFourierCoeff_conjL2]

/-- The real part preserves the solenoidal subspace. -/
theorem re3L2_mem_L2σ {W : L2} (hW : W ∈ L2σ) : re3L2 W ∈ L2σ :=
  L2σ.smul_mem _ (L2σ.add_mem hW (conjL2_mem_L2σ hW))

/-- The real part preserves `H²`. -/
theorem memH2_re3L2 {W : L2} (hW : MemH2 ⇑W) : MemH2 ⇑(re3L2 W) := by
  have hs := hW.add (hW.comp_injective neg_injective)
  refine hs.of_nonneg_of_le (fun m ↦ ?_) fun m ↦ ?_
  · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  · simp only [Function.comp_apply, h2Weight_neg, mFourierCoeff_re3L2, ← mul_add,
      ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (sq_nonneg _)
    set a := mFourierCoeff (fun x ↦ W x i) m
    set b := mFourierCoeff (fun x ↦ W x i) (-m)
    have h1 : ‖(2⁻¹ : ℂ) * (a + conj b)‖ ≤ 2⁻¹ * (‖a‖ + ‖b‖) := by
      rw [norm_mul, norm_inv, Complex.norm_ofNat]
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_conj])
    have h2 : 0 ≤ ‖(2⁻¹ : ℂ) * (a + conj b)‖ := norm_nonneg _
    nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-- A field whose coefficients live on the plane `m₃ = K`, `K ≠ 0`, is orthogonal to its
conjugate, whose coefficients live on `m₃ = -K`. -/
theorem inner_conjL2_eq_zero {W : L2} {K : ℤ} (hK : K ≠ 0)
    (hsupp : ∀ m i, m 2 ≠ K → mFourierCoeff (fun x ↦ W x i) m = 0) :
    inner ℂ W (conjL2 W) = 0 := by
  rw [inner_l2_eq_tsum]
  refine (tsum_congr fun m ↦ Finset.sum_eq_zero fun i _ ↦ ?_).trans tsum_zero
  rw [mFourierCoeff_conjL2]
  by_cases hm : m 2 = K
  · rw [hsupp (-m) i (by rw [Pi.neg_apply, hm]; omega), map_zero, mul_zero]
  · rw [hsupp m i hm, map_zero, zero_mul]

/-- **Plancherel for the real part.**  If the coefficients of `W` live on the plane `m₃ = K`,
`K ≠ 0`, then `‖Re W‖² = ‖W‖²/2`. -/
theorem norm_sq_re3L2 {W : L2} {K : ℤ} (hK : K ≠ 0)
    (hsupp : ∀ m i, m 2 ≠ K → mFourierCoeff (fun x ↦ W x i) m = 0) :
    ‖re3L2 W‖ ^ 2 = ‖W‖ ^ 2 / 2 := by
  rw [re3L2, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ), inner_conjL2_eq_zero hK hsupp,
    norm_conjL2, norm_inv, Complex.norm_ofNat]
  simp only [map_zero, mul_zero, add_zero]
  ring

/-! ## The growing real solution -/

section RealSolution

variable {u : T3 → R3} {ε : ℝ}

/-- The conjugate of a solenoidal field, as a solenoidal field. -/
def conjL2σ (V : L2σ) : L2σ := ⟨conjL2 V, conjL2_mem_L2σ V.2⟩

/-- The field underlying `conjL2σ V`. -/
@[simp] theorem coe_conjL2σ (V : L2σ) : (conjL2σ V : L2) = conjL2 V := rfl

/-- The real part of a solenoidal field, as a solenoidal field. -/
def re3L2σ (V : L2σ) : L2σ := ⟨re3L2 V, re3L2_mem_L2σ V.2⟩

/-- The field underlying `re3L2σ V`. -/
@[simp] theorem coe_re3L2σ (V : L2σ) : (re3L2σ V : L2) = re3L2 V := rfl

/-- `re3L2σ V = (V + conj V)/2` in `L²_σ`. -/
theorem re3L2σ_eq (V : L2σ) : re3L2σ V = (2⁻¹ : ℂ) • (V + conjL2σ V) :=
  Subtype.ext (by rw [coe_re3L2σ, Submodule.coe_smul, Submodule.coe_add, coe_conjL2σ, re3L2])

/-- **The orbit of the real part of an eigenmode.**  Every induction semigroup maps `Re V` to
`Re (e^{tλ} V)`. -/
theorem isInductionSemigroup_apply_re3L2σ {S : ℝ≥0 → L2σ →L[ℂ] L2σ}
    (hS : IsInductionSemigroup u ε S) {lam : ℂ} {V : L2σ} (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) (t : ℝ≥0) :
    (S t (re3L2σ V) : L2) = re3L2 (Complex.exp (t * lam) • (V : L2)) := by
  have h1 : MemH2 ⇑(conjL2σ V : L2) := by
    rw [coe_conjL2σ]
    exact memH2_conjL2 hH2
  have h2 : ∀ m i, inductionRHS u ε ⇑(conjL2σ V : L2) m i =
      conj lam * mFourierCoeff (fun x ↦ (conjL2σ V : L2) x i) m := by
    rw [coe_conjL2σ]
    exact inductionRHS_conjL2_eigen heig
  have hc : S t (conjL2σ V) = Complex.exp (t * conj lam) • conjL2σ V :=
    isInductionSemigroup_apply_eigenmode hS h1 h2 t
  rw [re3L2σ_eq, map_smul, map_add, isInductionSemigroup_apply_eigenmode hS hH2 heig t, hc,
    re3L2, map_smulₛₗ]
  simp only [Submodule.coe_smul, Submodule.coe_add, coe_conjL2σ, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal]

/-- **A2, the growing real solution.**  Let `V ∈ H² ∩ L²_σ` be a non-zero eigenmode,
`inductionRHS u ε V = λ V̂`, whose Fourier coefficients vanish off the plane `m₃ = K`, `K ≠ 0`.
Then the real datum `B_in = Re V` is a non-zero element of `H² ∩ L²_σ`, and for every induction
semigroup `S` its orbit is `Re (e^{tλ} V)`, of norm `e^{t Re λ} ‖B_in‖`.  This is the inner block
of the eigenmode clause of the Challenge statement. -/
theorem exists_realPart_eigenmode {K : ℤ} {lam : ℂ} {V : L2σ} (hK : K ≠ 0) (hV : V ≠ 0)
    (hH2 : MemH2 ⇑(V : L2))
    (hsupp : ∀ m i, m 2 ≠ K → mFourierCoeff (fun x ↦ (V : L2) x i) m = 0)
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) :
    ∃ Bin : L2σ, Bin ≠ 0 ∧ MemH2 ⇑(Bin : L2) ∧
      ⇑(Bin : L2) =ᵐ[volume] (fun x ↦ re3 ((V : L2) x)) ∧
      ∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0,
        ⇑(S t Bin : L2) =ᵐ[volume] (fun x ↦ re3 (Complex.exp (t * lam) • (V : L2) x)) ∧
        ‖S t Bin‖ = Real.exp (t * lam.re) * ‖Bin‖ := by
  have hnorm : ‖re3L2σ V‖ ^ 2 = ‖V‖ ^ 2 / 2 := by
    rw [← Submodule.norm_coe, coe_re3L2σ, norm_sq_re3L2 hK hsupp, Submodule.norm_coe]
  refine ⟨re3L2σ V, ?_, memH2_re3L2 hH2, re3L2_coe_ae _, fun S hS t ↦ ⟨?_, ?_⟩⟩
  · intro h
    rw [h, norm_zero] at hnorm
    have : ‖V‖ = 0 := by nlinarith [norm_nonneg V]
    exact hV (norm_eq_zero.1 this)
  · rw [isInductionSemigroup_apply_re3L2σ hS hH2 heig t]
    filter_upwards [re3L2_coe_ae (Complex.exp (t * lam) • (V : L2)),
      Lp.coeFn_smul (Complex.exp (t * lam)) (V : L2)] with x h1 h2
    rw [h1, h2, Pi.smul_apply]
  · have hsupp' : ∀ m i, m 2 ≠ K →
        mFourierCoeff (fun x ↦ (Complex.exp (t * lam) • (V : L2)) x i) m = 0 := by
      intro m i hm
      rw [mFourierCoeff_l2_smul, hsupp m i hm, mul_zero]
    refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [← Submodule.norm_coe, isInductionSemigroup_apply_re3L2σ hS hH2 heig t,
      norm_sq_re3L2 hK hsupp', mul_pow, hnorm, norm_smul, Complex.norm_exp,
      Complex.re_ofReal_mul, Submodule.norm_coe]
    ring

/-- **A1, the growth clause.**  If `V ∈ H² ∩ L²_σ` is a non-zero eigenmode,
`inductionRHS u ε V = λ V̂`, with `γ₀ ≤ Re λ`, then every induction semigroup satisfies
`e^{γ₀ t} ≤ ‖S t‖` for all `t ≥ 0`.  This is the growth clause of the Challenge statement. -/
theorem forall_exp_mul_le_norm_of_eigenmode {lam : ℂ} {V : L2σ} (hV : V ≠ 0)
    (hH2 : MemH2 ⇑(V : L2))
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) {γ₀ : ℝ} (hγ : γ₀ ≤ lam.re) :
    ∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0, Real.exp (γ₀ * t) ≤ ‖S t‖ :=
  fun _ hS t ↦ exp_mul_le_norm_of_eigenmode hS hV hH2 heig hγ t

/-- **A1 and A2 together.**  The growth clause and the inner block of the eigenmode clause of
the Challenge statement, for an arbitrary velocity, diffusivity and eigenmode. -/
theorem eigenmode_clauses {K : ℤ} {lam : ℂ} {V : L2σ} {γ₀ : ℝ} (hK : K ≠ 0)
    (hγ : γ₀ ≤ lam.re) (hV : V ≠ 0) (hH2 : MemH2 ⇑(V : L2))
    (hsupp : ∀ m i, m 2 ≠ K → mFourierCoeff (fun x ↦ (V : L2) x i) m = 0)
    (heig : ∀ m i, inductionRHS u ε ⇑(V : L2) m i =
      lam * mFourierCoeff (fun x ↦ (V : L2) x i) m) :
    (∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0, Real.exp (γ₀ * t) ≤ ‖S t‖) ∧
    ∃ Bin : L2σ, Bin ≠ 0 ∧ MemH2 ⇑(Bin : L2) ∧
      ⇑(Bin : L2) =ᵐ[volume] (fun x ↦ re3 ((V : L2) x)) ∧
      ∀ S, IsInductionSemigroup u ε S → ∀ t : ℝ≥0,
        ⇑(S t Bin : L2) =ᵐ[volume] (fun x ↦ re3 (Complex.exp (t * lam) • (V : L2) x)) ∧
        ‖S t Bin‖ = Real.exp (t * lam.re) * ‖Bin‖ :=
  ⟨forall_exp_mul_le_norm_of_eigenmode hV hH2 heig hγ,
    exists_realPart_eigenmode hK hV hH2 hsupp heig⟩

end RealSolution

end

end FastDynamo
