/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.EuclideanConvolution
public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Identities of convolution operators on the torus

The kernels `Φ` of `ℝ^d` act on `L_p(𝕋^d)`, `1 ≤ p < ∞`, by the bounded operators
`f ↦ Φ ⋆ f` (`Torus.econvLp`), and the characters are their eigenfunctions,
`Φ ⋆ e_m = 𝓕Φ(m) e_m` (`Torus.econvLp_mFourierLp`). Since the characters span a dense subspace
of `L_p(𝕋^d)`, a bounded linear map on `L_p(𝕋^d)` is determined by its values on them
(`Torus.ext_mFourierLp`), and every identity between these operators is an identity of Fourier
multipliers:

* `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f` (`Torus.econvLp_comp_econvLp`, and
  `Torus.econvLp_comp_econvLp_of_eq` for a given `M = K ⋆ L`), from `𝓕(K ⋆ L) = 𝓕K · 𝓕L`
  (`Rd.fourier_conv`); in particular the operators commute (`Torus.econvLp_comm`);
* the operator is additive in the kernel (`Torus.econvLp_add_kernel`,
  `Torus.econvLp_sub_kernel`), constants move from the kernel to the function
  (`Torus.econv_smul_kernel`), and equal kernels give the same operator
  (`Torus.econvLp_congr_kernel`);
* if `𝓕Φ(m) = 0` for `deg m < n`, the operator annihilates the trigonometric polynomials of
  degree `< n` (`Torus.econvLp_eq_zero_of_mem`).

**Approximate identities** (`Torus.tendsto_econvLp_of_fourier`): a family of kernels with
bounded `L_1` norms whose Fourier transforms tend to `1` at every lattice point satisfies
`Φ_i ⋆ f → f` in `L_p(𝕋^d)`. The convergence holds on the characters, the operators are
uniformly bounded (`Torus.norm_econvLp_le`), so the set where it holds is a closed subspace.
This applies to the dilations `K_c ⋆ f → f` of a kernel with `∫ K = 1`
(`Torus.tendsto_econvLp_dilate`) and to the Littlewood–Paley kernels `Φ_J`
(`Torus.tendsto_econvLp_Phi`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Topology
open scoped ENNReal FourierTransform TorusHaar

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Operators are determined by the characters -/

/-- **Bounded linear maps on `L_p(𝕋^d)` are determined by the characters**: for `1 ≤ p < ∞`,
two bounded linear maps from `L_p(𝕋^d)` into a normed space that agree on every `e_m` are equal,
since the characters span a dense subspace (Mathlib's `span_mFourierLp_closure_eq_top`). -/
theorem ext_mFourierLp (hp : p ≠ ∞) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T S : Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] F}
    (h : ∀ m : d → ℤ, T (mFourierLp p m) = S (mFourierLp p m)) : T = S :=
  ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.2 (span_mFourierLp_closure_eq_top hp))
    (by rintro _ ⟨m, rfl⟩; exact h m)

/-! ### Composition and linearity in the kernel -/

/-- **Composition of convolution operators**: `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f` on `L_p(𝕋^d)`, for
integrable kernels `K`, `L` on `ℝ^d`; on the characters both sides multiply by
`𝓕K(m) 𝓕L(m) = 𝓕(K ⋆ L)(m)`. -/
theorem econvLp_comp_econvLp (hp : p ≠ ∞) {K L : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (hL : Integrable L) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp hK (econvLp hp hL f) = econvLp hp (Rd.integrable_conv hK hL) f := by
  have h : (econvLp hp hK).comp (econvLp hp hL) = econvLp hp (Rd.integrable_conv hK hL) :=
    ext_mFourierLp hp fun m => by
      rw [ContinuousLinearMap.comp_apply, econvLp_mFourierLp, map_smul, econvLp_mFourierLp,
        smul_smul, econvLp_mFourierLp, Rd.fourier_conv hK hL, mul_comm]
  exact DFunLike.congr_fun h f

/-- If `K ⋆ L = M` on `ℝ^d`, then `K ⋆ (L ⋆ f) = M ⋆ f` on `L_p(𝕋^d)`. -/
theorem econvLp_comp_econvLp_of_eq (hp : p ≠ ∞) {K L M : EuclideanSpace ℝ d → ℂ}
    (hK : Integrable K) (hL : Integrable L) (hM : Integrable M) (h : Rd.conv K L volume = M)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp hK (econvLp hp hL f) = econvLp hp hM f := by
  rw [econvLp_comp_econvLp hp hK hL]
  subst h
  rfl

/-- **Convolution operators commute**: `K ⋆ (L ⋆ f) = L ⋆ (K ⋆ f)` on `L_p(𝕋^d)`. -/
theorem econvLp_comm (hp : p ≠ ∞) {K L : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (hL : Integrable L) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp hK (econvLp hp hL f) = econvLp hp hL (econvLp hp hK f) := by
  have h : (econvLp hp hK).comp (econvLp hp hL) = (econvLp hp hL).comp (econvLp hp hK) :=
    ext_mFourierLp hp fun m => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        econvLp_mFourierLp hp hL, map_smul, econvLp_mFourierLp hp hK, smul_smul, map_smul,
        econvLp_mFourierLp hp hL, smul_smul, mul_comm]
  exact DFunLike.congr_fun h f

/-- **Additivity in the kernel**: `(K + L) ⋆ f = K ⋆ f + L ⋆ f` on `L_p(𝕋^d)`. -/
theorem econvLp_add_kernel (hp : p ≠ ∞) {K L : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (hL : Integrable L) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp (hK.add hL) f = econvLp hp hK f + econvLp hp hL f := by
  have h : econvLp hp (hK.add hL) = econvLp hp hK + econvLp hp hL :=
    ext_mFourierLp hp fun m => by
      rw [add_apply, econvLp_mFourierLp, econvLp_mFourierLp,
        econvLp_mFourierLp, Rd.fourier_add_apply hK hL, add_smul]
  exact DFunLike.congr_fun h f

/-- **Subtractivity in the kernel**: `(K - L) ⋆ f = K ⋆ f - L ⋆ f` on `L_p(𝕋^d)`. -/
theorem econvLp_sub_kernel (hp : p ≠ ∞) {K L : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (hL : Integrable L) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp (hK.sub hL) f = econvLp hp hK f - econvLp hp hL f := by
  have h : econvLp hp (hK.sub hL) = econvLp hp hK - econvLp hp hL :=
    ext_mFourierLp hp fun m => by
      rw [sub_apply, econvLp_mFourierLp, econvLp_mFourierLp,
        econvLp_mFourierLp, Rd.fourier_sub_apply hK hL, sub_smul]
  exact DFunLike.congr_fun h f

/-- **Constants move from the kernel to the function**: `(c K) ⋆ g = K ⋆ (c g)` at every point
of the torus, for every `c ∈ ℂ`, every function `K` on `ℝ^d` and every function `g` on `𝕋^d`. -/
theorem econv_smul_kernel (c : ℂ) (K : EuclideanSpace ℝ d → ℂ) (g : UnitAddTorus d → ℂ) :
    econv (c • K) g = econv K (c • g) := by
  rw [econv_smul]
  funext t
  simp only [econv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

/-- Equal integrable kernels `K = L` on `ℝ^d` give the same convolution operator on
`L_p(𝕋^d)`. -/
theorem econvLp_congr_kernel (hp : p ≠ ∞) {K L : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (hL : Integrable L) (h : K = L) : econvLp hp hK = econvLp hp hL := by
  subst h
  rfl

/-- **Kernels with `𝓕Φ = 0` on the low frequencies annihilate trigonometric polynomials**: if
`𝓕Φ(m) = 0` for `deg m < n`, then `Φ ⋆ a = 0` for every trigonometric polynomial `a` of degree
`< n`. -/
theorem econvLp_eq_zero_of_mem (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {n : ℕ} (hF : ∀ m : d → ℤ, deg m < n → 𝓕 Φ (latticeVec m) = 0)
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p n) :
    econvLp hp hΦ a = 0 := by
  rw [trigPolyLp_eq_span] at ha
  refine LinearMap.eqOn_span (f := (econvLp hp hΦ).toLinearMap) (g := 0) ?_ ha
  rintro _ ⟨m, hm, rfl⟩
  simp [econvLp_mFourierLp, hF m (mem_boxLt.1 hm)]

/-! ### Approximate identities -/

/-- **A uniform bound for convolution operators**: if `∫ |Φ| ≤ C < ∞`, then
`‖Φ ⋆ g‖_p ≤ C ‖g‖_p` in real norms. -/
theorem norm_econvLp_le (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hB : ∫⁻ y, ‖Φ y‖ₑ ≤ C)
    (g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖econvLp hp hΦ g‖ ≤ C.toReal * ‖g‖ := by
  have h : ‖econvLp hp hΦ g‖ₑ ≤ C * ‖g‖ₑ :=
    (enorm_econvLp_le hp hΦ g).trans (mul_le_mul_left hB _)
  calc ‖econvLp hp hΦ g‖ = ‖econvLp hp hΦ g‖ₑ.toReal := (toReal_eNorm _).symm
    _ ≤ (C * ‖g‖ₑ).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) h
    _ = C.toReal * ‖g‖ := by rw [ENNReal.toReal_mul, toReal_eNorm]

/-- **Approximate identities on the torus**: let `Φ_i` be integrable kernels on `ℝ^d` with
`∫ |Φ_i| ≤ C < ∞` and `𝓕Φ_i(m) → 1` for every lattice point `m`. Then `Φ_i ⋆ f → f` in
`L_p(𝕋^d)` for every `f`, `1 ≤ p < ∞`. The `f` with `Φ_i ⋆ f → f` form a subspace that contains
every character; it is closed since the operators are uniformly bounded, hence equicontinuous
(Mathlib's `Equicontinuous.isClosed_setOfPred_tendsto`), and the characters span a dense
subspace. -/
theorem tendsto_econvLp_of_fourier (hp : p ≠ ∞) {ι : Type*} {l : Filter ι}
    {Φ : ι → EuclideanSpace ℝ d → ℂ} (hΦ : ∀ i, Integrable (Φ i)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hB : ∀ i, ∫⁻ y, ‖Φ i y‖ₑ ≤ C)
    (hF : ∀ m : d → ℤ, Tendsto (fun i => 𝓕 (Φ i) (latticeVec m)) l (𝓝 1))
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Tendsto (fun i => econvLp hp (hΦ i) f) l (𝓝 f) := by
  let S : Submodule ℂ (Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
    { carrier := {g | Tendsto (fun i => econvLp hp (hΦ i) g) l (𝓝 g)}
      add_mem' := fun {g h} hg hh => by
        simp only [Set.mem_ofPred_eq, map_add] at hg hh ⊢
        exact hg.add hh
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact tendsto_const_nhds
      smul_mem' := fun c g hg => by
        simp only [Set.mem_ofPred_eq, map_smul] at hg ⊢
        exact hg.const_smul c }
  have hbd : ∃ C' : ℝ, ∀ i (g : Lp ℂ p (volume : Measure (UnitAddTorus d))),
      ‖econvLp hp (hΦ i) g‖ ≤ C' * ‖g‖ :=
    ⟨C.toReal, fun i g => norm_econvLp_le hp (hΦ i) hC (hB i) g⟩
  have hequi : Equicontinuous
      ((↑) ∘ fun i => econvLp hp (hΦ i) :
        ι → Lp ℂ p (volume : Measure (UnitAddTorus d)) →
          Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
    ((NormedSpace.equicontinuous_tfae fun i => econvLp hp (hΦ i)).out 4 2).1 hbd
  have hS : IsClosed (S : Set (Lp ℂ p (volume : Measure (UnitAddTorus d)))) :=
    hequi.isClosed_setOfPred_tendsto continuous_id
  have hspan : Submodule.span ℂ (Set.range (mFourierLp (d := d) p)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    change Tendsto (fun i => econvLp hp (hΦ i) (mFourierLp p m)) l (𝓝 (mFourierLp p m))
    simp only [econvLp_mFourierLp]
    simpa only [one_smul] using (hF m).smul_const (mFourierLp p m)
  have hcl := Submodule.topologicalClosure_minimal _ hspan hS
  rw [span_mFourierLp_closure_eq_top hp] at hcl
  exact hcl Submodule.mem_top

/-- **Dilations are approximate identities on the torus**: for an integrable kernel `K` on `ℝ^d`
with `∫ K = 1` and scales `c_i > 0` with `c_i → ∞` along a filter, `K_{c_i} ⋆ f → f` in
`L_p(𝕋^d)`. The Fourier transforms `𝓕K_{c_i}(m) = 𝓕K(m / c_i)` tend to `𝓕K(0) = ∫ K = 1`, and
`‖K_{c_i}‖_1 = ‖K‖_1`. -/
theorem tendsto_econvLp_dilate (hp : p ≠ ∞) {K : EuclideanSpace ℝ d → ℂ} (hK : Integrable K)
    (h1 : ∫ y, K y = 1) {ι : Type*} {l : Filter ι} {c : ι → ℝ} (hc0 : ∀ i, 0 < c i)
    (hc : Tendsto c l atTop) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Tendsto (fun i => econvLp hp (Rd.integrable_dilate hK (hc0 i).ne') f) l (𝓝 f) := by
  refine tendsto_econvLp_of_fourier hp (fun i => Rd.integrable_dilate hK (hc0 i).ne')
    (hK.2.ne) (fun i => ?_) (fun m => ?_) f
  · rw [← eLpNorm_one_eq_lintegral_eNorm (Rd.integrable_dilate hK (hc0 i).ne').1,
      Rd.eLpNorm_dilate_one hK (hc0 i), eLpNorm_one_eq_lintegral_eNorm hK.1]
  · have hsmul : Tendsto (fun i => (c i)⁻¹ • latticeVec m) l (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero.comp hc).smul_const (latticeVec m)
      rwa [zero_smul] at h
    have hlim := ((Rd.continuous_fourier_of_integrable hK).tendsto 0).comp hsmul
    rw [Rd.fourier_apply_zero, h1] at hlim
    refine hlim.congr fun i => ?_
    simp only [Function.comp_apply]
    rw [Rd.fourier_dilate K (hc0 i)]

/-- **The Littlewood–Paley kernels are an approximate identity on the torus**: `Φ_J ⋆ f → f`
in `L_p(𝕋^d)` as `J → ∞`, for `1 ≤ p < ∞`. -/
theorem tendsto_econvLp_Phi (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Tendsto (fun J => econvLp hp (Rd.integrable_Phi (V := EuclideanSpace ℝ d) J) f) atTop
      (𝓝 f) :=
  tendsto_econvLp_dilate hp Rd.integrable_lpKernel Rd.integral_lpKernel
    (c := fun J : ℕ => (2 : ℝ) ^ J) (fun J => by positivity)
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f

end Torus
