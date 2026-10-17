/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionSobolev
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.BasicLemmas
public import LeanPool.HighContrastHomogenization.Support.Sobolev.FiniteLpExponent
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeReflection.Derivatives

/-!
# OddReflectionGlue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `H¹` gluing of the odd reflection across one face

Three steps, each proved here:

1. **`L²` graph closure** (`hasWeakGradientOn_of_tendsto_lp`): the weak-gradient
   graph is closed under `L²` convergence of the function together with all of
   its gradient coordinates.
2. **Zero extension** (`hasWeakGradientOn_univ_zeroExtend`): the literal zero
   extension of an `H¹₀(V)` function has the zero-extended gradient as a *global*
   weak gradient.  This is where the `H¹₀` approximants earn their keep: they are
   already supported in `V`, so integration by parts against a test function
   supported anywhere in `ℝᵈ` is legitimate for each approximant, and the limit
   is taken in `L²`.
3. **Reflection transport** (`hasWeakGradientOn_univ_comp_coordFaceReflection`):
   pre-composition with the face reflection `r` transports the weak gradient by
   the reflected gradient `coordReflectionLinear i ∘ G ∘ r`; the change of
   variables is `measurePreserving_coordFaceReflection` and the sign is the
   one-face chain rule `euclideanCoordDeriv_comp_coordFaceReflection`.

Together, the *odd* extension `W - W ∘ r` of the zero extension `W` of an
`H¹₀(V)`-function of the half is `H¹` on `ℝᵈ`
(`hasWeakGradientOn_univ_oddFaceExtend`), and it is the expected pointwise odd
extension: it is `W` on the half and `-W ∘ r` on the reflected half
(`oddFaceExtend_zeroExtend_of_mem`, `oddFaceExtend_zeroExtend_of_notMem`).

## What is not done here

The multi-face assembly — that the *iterated* `oddExtend` of `OddReflectionMap`
is `H¹` on the whole partially reflected window — is not proved here; only the
single-face gluing is, which is the step the interface argument actually needs
(the met faces are pairwise orthogonal, `not_meetsLowerFace_of_meetsUpperFace`,
so a neighbourhood of any interface point meets exactly one of them).

## References

* CoarseGraining `Homogenization.Sobolev.W1p.WeakGradientClosure`,
  `Homogenization.Sobolev.W1p.ZeroExtensionGraph` (route source; no oleans).
* CoarseGraining
  `Homogenization.Sobolev.Foundations.CubeReflection.Reflections`
  (`measurePreserving_coordFaceReflection`, `coordFaceReflection_involutive`),
  `.CubeReflection.Derivatives`
  (`euclideanCoordDeriv_comp_coordFaceReflection`),
  `.CubeReflection.Homeomorphism` (`coordFaceReflectionHomeomorph`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` closure of the weak-gradient graph -/

private theorem tendsto_setIntegral_mul_of_tendsto_eLpNorm
    {U : Set (Vec d)} (p : FiniteLpExponent) {h : Vec d → ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h p.conjugate.exponent (volume.restrict U))
    (hf : ∀ n, MemLp (f n) p.exponent (volume.restrict U))
    (hg : MemLp g p.exponent (volume.restrict U))
    (htend : Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in U, f n x * h x ∂volume)
      atTop (nhds (∫ x in U, g x * h x ∂volume)) := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
  let : ENNReal.HolderConjugate p.conjugate.exponent p.exponent := inferInstance
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hh.fun_mul (hf n)))
  have hgh_int : Integrable (fun x => g x * h x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hh.fun_mul hg))
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ) =
        ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) p.exponent μ *
      eLpNorm h p.conjugate.exponent μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h p.conjugate.exponent μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.eLpNorm_lt_top.ne)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have hh' := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p.exponent) (q := p.conjugate.exponent) (r := 1)
      (fun x y => x * y) 1 continuous_mul ((hf n).sub hg).aestronglyMeasurable
      hh.aestronglyMeasurable hbound
    simpa [B] using! hh'
  calc ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
        have hm : AEStronglyMeasurable (fun x => (f n x - g x) * h x) μ :=
          ((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable
        rw [eLpNorm_one_eq_lintegral_enorm hm]
        simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
        refine ENNReal.toReal_mono ?_ hHolder
        exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_lt_top.ne hh.eLpNorm_lt_top.ne

/-- **Graph closure, one coordinate.**  Re-derivation of CoarseGraining's
`HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp` (no olean upstream). -/
theorem hasWeakPartialDerivOn_of_tendsto_lp {U : Set (Vec d)}
    (p : FiniteLpExponent) {i : Fin d} {u gi : Vec d → ℝ}
    {u_n g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hgi : MemLp gi p.exponent (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) p.exponent (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_g : Tendsto
      (fun n => eLpNorm (fun x => g_n n x - gi x) p.exponent (volume.restrict U))
      atTop (nhds 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) p.conjugate.exponent
      (volume.restrict U) := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      refine HasCompactSupport.mono' (hφ_compact.fderiv ℝ) ?_
      intro x hx
      refine subset_tsupport (fderiv ℝ φ) ?_
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp)
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hφmem : MemLp φ p.conjugate.exponent (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
  have hlhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm p hDφ hu_n hu htend_u
  have hrhs := tendsto_setIntegral_mul_of_tendsto_eLpNorm p hφmem hg_n hgi htend_g
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        -(∫ x in U, g_n n x * φ x ∂volume) :=
    fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Tendsto (fun n => -(∫ x in U, g_n n x * φ x ∂volume)) atTop
      (nhds (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n
    rw [heq_n n]
  exact tendsto_nhds_unique hlhs' hrhs.neg

/-- **Graph closure.**  Re-derivation of CoarseGraining's
`HasWeakGradientOn.of_tendsto_eLpNorm_finiteLp` (no olean upstream). -/
theorem hasWeakGradientOn_of_tendsto_lp {U : Set (Vec d)} (p : FiniteLpExponent)
    {u : Vec d → ℝ} {Du : Vec d → Vec d} {u_n : ℕ → Vec d → ℝ}
    {Du_n : ℕ → Vec d → Vec d}
    (hu : MemLp u p.exponent (volume.restrict U))
    (hDu : GradMemLpOn U p.exponent Du)
    (hu_n : ∀ n, MemLp (u_n n) p.exponent (volume.restrict U))
    (hDu_n : ∀ n, GradMemLpOn U p.exponent (Du_n n))
    (hweak : ∀ n, HasWeakGradientOn U (u_n n) (Du_n n))
    (htend_u : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p.exponent (volume.restrict U))
      atTop (nhds 0))
    (htend_Du : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => Du_n n x i - Du x i) p.exponent
        (volume.restrict U)) atTop (nhds 0)) :
    HasWeakGradientOn U u Du := fun i =>
  hasWeakPartialDerivOn_of_tendsto_lp p hu (hDu i) hu_n (fun n => hDu_n n i)
    (fun n => hweak n i) htend_u (htend_Du i)

/-! ## 2. Zero extension of an `H¹₀` function -/

/-- The literal zero extension of a scalar off `V`. -/
def zeroExtend (V : Set (Vec d)) (u : Vec d → ℝ) : Vec d → ℝ :=
  Set.indicator V u

/-- The literal zero extension of a gradient field off `V`. -/
def zeroExtendGrad (V : Set (Vec d)) (G : Vec d → Vec d) : Vec d → Vec d :=
  Set.indicator V G

theorem zeroExtend_of_mem {V : Set (Vec d)} (u : Vec d → ℝ) {y : Vec d}
    (hy : y ∈ V) : zeroExtend V u y = u y :=
  Set.indicator_of_mem hy u

theorem zeroExtend_of_notMem {V : Set (Vec d)} (u : Vec d → ℝ) {y : Vec d}
    (hy : y ∉ V) : zeroExtend V u y = 0 :=
  Set.indicator_of_notMem hy u

theorem zeroExtendGrad_of_mem {V : Set (Vec d)} (G : Vec d → Vec d) {y : Vec d}
    (hy : y ∈ V) : zeroExtendGrad V G y = G y :=
  Set.indicator_of_mem hy G

theorem zeroExtendGrad_of_notMem {V : Set (Vec d)} (G : Vec d → Vec d)
    {y : Vec d} (hy : y ∉ V) : zeroExtendGrad V G y = 0 :=
  Set.indicator_of_notMem hy G

theorem zeroExtendGrad_apply_coord (V : Set (Vec d)) (G : Vec d → Vec d)
    (i : Fin d) :
    (fun y => zeroExtendGrad V G y i) = Set.indicator V (fun y => G y i) := by
  funext y
  by_cases hy : y ∈ V
  · rw [zeroExtendGrad_of_mem G hy, Set.indicator_of_mem hy]
  · rw [zeroExtendGrad_of_notMem G hy, Set.indicator_of_notMem hy]
    rfl

private theorem approx_eq_zero_of_notMem {V : Set (Vec d)} (u : H10Function V)
    (n : ℕ) {y : Vec d} (hy : y ∉ V) : u.approx n y = 0 := by
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hsupp
  exact hy (u.approx_support_subset n hsupp)

private theorem fderiv_approx_eq_zero_of_notMem {V : Set (Vec d)}
    (u : H10Function V) (n : ℕ) (i : Fin d) {y : Vec d} (hy : y ∉ V) :
    (fderiv ℝ (u.approx n) y) (basisVec i) = 0 := by
  have hout : y ∉ tsupport (u.approx n) := fun hsupp =>
    hy (u.approx_support_subset n hsupp)
  have hzero : u.approx n =ᶠ[nhds y] 0 :=
    ((isClosed_tsupport (f := u.approx n)).isOpen_compl.eventually_mem hout).mono
      fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

private theorem approx_sub_zeroExtend_eq {V : Set (Vec d)} (u : H10Function V)
    (n : ℕ) :
    (fun y => u.approx n y - zeroExtend V u.toH1Function.toFun y) =
      Set.indicator V (fun y => u.approx n y - u.toH1Function.toFun y) := by
  funext y
  by_cases hy : y ∈ V
  · rw [Set.indicator_of_mem hy, zeroExtend_of_mem _ hy]
  · rw [Set.indicator_of_notMem hy, zeroExtend_of_notMem _ hy, sub_zero,
      approx_eq_zero_of_notMem u n hy]

private theorem fderiv_approx_sub_zeroExtendGrad_eq {V : Set (Vec d)}
    (u : H10Function V) (n : ℕ) (i : Fin d) :
    (fun y => (fderiv ℝ (u.approx n) y) (basisVec i) -
        zeroExtendGrad V u.toH1Function.grad y i) =
      Set.indicator V (fun y => (fderiv ℝ (u.approx n) y) (basisVec i) -
        u.toH1Function.grad y i) := by
  funext y
  by_cases hy : y ∈ V
  · rw [Set.indicator_of_mem hy, zeroExtendGrad_of_mem _ hy]
  · rw [Set.indicator_of_notMem hy, zeroExtendGrad_of_notMem _ hy, Pi.zero_apply,
      sub_zero, fderiv_approx_eq_zero_of_notMem u n i hy]

theorem memL2_zeroExtend {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) :
    MemLp (zeroExtend V u.toH1Function.toFun) 2 (volume : Measure (Vec d)) :=
  (MeasureTheory.memLp_indicator_iff_restrict hV).2 u.toH1Function.memL2

theorem gradMemL2_zeroExtendGrad {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) :
    GradMemLpOn Set.univ 2 (zeroExtendGrad V u.toH1Function.grad) := by
  intro i
  change MemLp (fun y => zeroExtendGrad V u.toH1Function.grad y i) 2
    (volume.restrict Set.univ)
  rw [Measure.restrict_univ, zeroExtendGrad_apply_coord]
  exact (MeasureTheory.memLp_indicator_iff_restrict hV).2 (u.toH1Function.gradMemL2 i)

/-- **, step 2: the zero extension is a global weak-gradient graph.** Re-derivation
of CoarseGraining's `H10Function.hasWeakGradientOn_univ_zeroExtension` (no
olean upstream). -/
theorem hasWeakGradientOn_univ_zeroExtend {V : Set (Vec d)}
    (hV : MeasurableSet V) (u : H10Function V) :
    HasWeakGradientOn Set.univ (zeroExtend V u.toH1Function.toFun)
      (zeroExtendGrad V u.toH1Function.grad) := by
  refine hasWeakGradientOn_of_tendsto_lp FiniteLpExponent.two
    (u_n := fun n => u.approx n)
    (Du_n := fun n y => fun i => (fderiv ℝ (u.approx n) y) (basisVec i))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Measure.restrict_univ] using! memL2_zeroExtend hV u
  · exact gradMemL2_zeroExtendGrad hV u
  · intro n
    exact ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (u.approx_hasCompactSupport n)).restrict Set.univ
  · intro n i
    have hcont : Continuous (fun y => (fderiv ℝ (u.approx n) y) (basisVec i)) :=
      ((u.approx_smooth n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hsupp : HasCompactSupport
        (fun y => (fderiv ℝ (u.approx n) y) (basisVec i)) := by
      simpa only using (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hsupp).restrict Set.univ
  · intro n
    exact HasWeakGradientOn.of_contDiff ((u.approx_smooth n).of_le (by norm_num))
  · have htend : Tendsto
        (fun n => eLpNorm (fun y => u.approx n y -
          zeroExtend V u.toH1Function.toFun y) 2 volume) atTop (nhds 0) := by
      refine u.tendsto_approx.congr fun n => ?_
      rw [approx_sub_zeroExtend_eq u n,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV]
    simpa only [Measure.restrict_univ] using! htend
  · intro i
    have htend : Tendsto
        (fun n => eLpNorm (fun y => (fderiv ℝ (u.approx n) y) (basisVec i) -
          zeroExtendGrad V u.toH1Function.grad y i) 2 volume) atTop (nhds 0) := by
      refine (u.tendsto_approx_grad i).congr fun n => ?_
      rw [fderiv_approx_sub_zeroExtendGrad_eq u n i,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV]
    simpa only [Measure.restrict_univ] using! htend

/-! ## 3. Reflection transport of a global weak gradient -/

theorem coordReflectionLinear_apply_coord (i : Fin d) (v : Vec d) (k : Fin d) :
    coordReflectionLinear i v k = (if k = i then (-1 : ℝ) else 1) * v k := by
  by_cases hki : k = i <;> simp [coordReflectionLinear, hki]

/-! ## 4. The one-face odd extension is `H¹` across the interface -/

/-- The odd extension of a scalar across the face `{yᵢ = a}`. -/
def oddFaceExtend (a : ℝ) (i : Fin d) (w : Vec d → ℝ) : Vec d → ℝ :=
  fun y => w y - w (coordFaceReflection a i y)

/-- The gradient field of the odd extension. -/
def oddFaceExtendGrad (a : ℝ) (i : Fin d) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun y => G y - coordReflectionLinear i (G (coordFaceReflection a i y))

/-- The odd extension is odd, as its name says. -/
theorem oddFaceExtend_comp_coordFaceReflection (a : ℝ) (i : Fin d)
    (w : Vec d → ℝ) (y : Vec d) :
    oddFaceExtend a i w (coordFaceReflection a i y) = -oddFaceExtend a i w y := by
  simp only [oddFaceExtend, coordFaceReflection_involutive]
  ring

/-! ## 5. The pointwise shape of the one-face odd extension -/

/-- The reflection of a point of the `σ`-half proves outside it. -/
theorem coordFaceReflection_notMem_faceHalf {U : Set (Vec d)} {i : Fin d}
    {a σ : ℝ} {y : Vec d} (hy : y ∈ faceHalf U i a σ) :
    coordFaceReflection a i y ∉ faceHalf U i a σ := by
  intro hry
  have hcoord : (coordFaceReflection a i y) i = 2 * a - y i := by
    have h1 : coordFaceReflection a i y i =
        coordReflectionLinear i y i + coordFaceReflectionOffset a i i := rfl
    have h2 : coordReflectionLinear i y i = -(y i) := by
      simp [coordReflectionLinear]
    have h3 : coordFaceReflectionOffset a i i = 2 * a := by
      simp [coordFaceReflectionOffset]
    rw [h1, h2, h3]
    ring
  have h1 : 0 < σ * (a - y i) := hy.2
  have h2 : 0 < σ * (a - (coordFaceReflection a i y) i) := hry.2
  rw [hcoord] at h2
  have h3 : σ * (a - (2 * a - y i)) = -(σ * (a - y i)) := by ring
  rw [h3] at h2
  linarith only [h1, h2]

theorem oddFaceExtend_zeroExtend_of_mem {V : Set (Vec d)} (u : Vec d → ℝ)
    (a : ℝ) (i : Fin d) {y : Vec d} (hy : y ∈ V)
    (hry : coordFaceReflection a i y ∉ V) :
    oddFaceExtend a i (zeroExtend V u) y = u y := by
  rw [oddFaceExtend, zeroExtend_of_mem u hy, zeroExtend_of_notMem u hry, sub_zero]

/-- On the half itself the odd extension of the zero extension is the original
function. -/
theorem oddFaceExtend_zeroExtend_faceHalf {U : Set (Vec d)} (u : Vec d → ℝ)
    {i : Fin d} {a σ : ℝ} {y : Vec d} (hy : y ∈ faceHalf U i a σ) :
    oddFaceExtend a i (zeroExtend (faceHalf U i a σ) u) y = u y :=
  oddFaceExtend_zeroExtend_of_mem u a i hy (coordFaceReflection_notMem_faceHalf hy)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
