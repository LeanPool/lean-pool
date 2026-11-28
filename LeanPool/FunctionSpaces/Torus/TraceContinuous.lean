/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Trace
public import LeanPool.FunctionSpaces.Torus.LpJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The trace of a continuous function on the torus

The trace `Tr = (Torus.traceBound p n hp).ext` of `Torus.trace_besov`, `1 ≤ p < ∞`, is a limit of
traces of near-best approximants. For every bounded continuous `f` on `𝕋^(n+1)` whose class lies
in `B^{1/p}_{p,1}(𝕋^(n+1))`, it is the restriction `f(0, ·)` to the face
(`Torus.traceBound_ext_eq_restrictFace`), in particular for `f ∈ B^{s+1/p}_{p,q}`, `s > 0`
(`Torus.trace_besov_eq_restrictFace`). For `s > n/p` every element of `B^{s+1/p}_{p,q}(𝕋^(n+1))`
has a continuous representative, and its trace is the restriction of that representative
(`Torus.exists_trace_eq_restrictFace`).

The proof uses the uniform density of the trigonometric polynomials
(`Torus.dense_iUnion_trigPoly`) and the convolution of bounded continuous functions with
integrable kernels on `ℝ^d` (`Torus.econvBCF`).

* **De la Vallée Poussin operators** (`Torus.valleePoussin`, `Torus.valleePoussinBCF`):
  `V_k f = Θ_{k+#d} ⋆ f` reproduces the trigonometric polynomials of degree `< 2^k`, has degree
  `< 2^(k+#d+2)` and norm `≤ ‖Θ‖_1`; hence it is near-best in `L_p` and in the sup norm:
  `‖f - V_k f‖ ≤ (1 + ‖Θ‖_1) ‖f - a‖` for every `a` of degree `< 2^k`.

The main theorem combines both norms: `V_k f → f` uniformly, so `(V_k f)(0, ·) → f(0, ·)` in
`L_p(𝕋^n)`; and `V_k f → f` in `L_p` at the rate of the abstract trace theorem
(`ApproximationScheme.TraceBound.tendsto_ext`), so `(V_k f)(0, ·) → Tr f`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter Topology
open scoped ENNReal BoundedContinuousFunction FourierTransform TorusHaar

open ENNReal (dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### De la Vallée Poussin operators -/

/-- `𝓕Θ_j` vanishes at the lattice points of degree `≥ 2^(j+2)`. -/
theorem fourier_Theta_latticeVec_eq_zero {j : ℕ} {m : d → ℤ} (hm : 2 ^ (j + 2) ≤ deg m) :
    𝓕 (Rd.Theta (V := EuclideanSpace ℝ d) j) (latticeVec m) = 0 := by
  by_contra h
  have h1 := Rd.norm_lt_of_fourier_Theta_ne_zero h
  have h2 := deg_le_norm_latticeVec m
  have h3 : ((2 : ℝ) ^ (j + 2)) ≤ deg m := by exact_mod_cast hm
  linarith

/-- The **de la Vallée Poussin operator** `V_k F = Θ_{k+#d} ⋆ F` on `L_p(𝕋^d)`, `1 ≤ p < ∞`, with
the band-limiting kernel `Θ_J` of `ℝ^d` (`Rd.Theta`). It is a smooth de la Vallée Poussin
operator: its multiplier is `1` on frequencies of degree `< 2^k` and `0` from degree
`2^(k+#d+2)` on. -/
noncomputable def valleePoussin (hp : p ≠ ∞) (k : ℕ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  econvLp hp (Rd.integrable_Theta (V := EuclideanSpace ℝ d) (k + Fintype.card d))

/-- The **de la Vallée Poussin operator** `V_k f = Θ_{k+#d} ⋆ f` on the bounded continuous
functions on `𝕋^d`, the smooth de la Vallée Poussin operator of `Torus.valleePoussin`. -/
noncomputable def valleePoussinBCF (k : ℕ) :
    (UnitAddTorus d →ᵇ ℂ) →L[ℂ] (UnitAddTorus d →ᵇ ℂ) :=
  econvBCF (Rd.integrable_Theta (V := EuclideanSpace ℝ d) (k + Fintype.card d))

/-- `V_k F` is a trigonometric polynomial of degree `< 2^(k+#d+2)`. -/
theorem valleePoussin_mem_trigPolyLp (hp : p ≠ ∞) (k : ℕ)
    (F : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    valleePoussin hp k F ∈ trigPolyLp p (2 ^ (k + Fintype.card d + 2)) :=
  econvLp_mem_trigPolyLp hp _ (fun _ hm => fourier_Theta_latticeVec_eq_zero hm) F

/-- `V_k f` is a trigonometric polynomial of degree `< 2^(k+#d+2)`. -/
theorem valleePoussinBCF_mem_trigPoly (k : ℕ) (f : UnitAddTorus d →ᵇ ℂ) :
    valleePoussinBCF k f ∈ trigPoly d (2 ^ (k + Fintype.card d + 2)) :=
  econvBCF_mem_trigPoly _ (fun _ hm => fourier_Theta_latticeVec_eq_zero hm) f

/-- `V_k a = a` for every trigonometric polynomial `a` of degree `< 2^k` in `L_p`. -/
theorem valleePoussin_eq_self (hp : p ≠ ∞) {k : ℕ}
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p (2 ^ k)) :
    valleePoussin hp k a = a :=
  econvLp_Theta_eq_self hp ha

/-- `V_k a = a` for every trigonometric polynomial `a` of degree `< 2^k`. -/
theorem valleePoussinBCF_eq_self {k : ℕ} {a : UnitAddTorus d →ᵇ ℂ}
    (ha : a ∈ trigPoly d (2 ^ k)) : valleePoussinBCF k a = a := by
  refine BoundedContinuousFunction.toLp_injective (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume ?_
  rw [valleePoussinBCF, toLp_econvBCF (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top]
  exact econvLp_Theta_eq_self _ (Submodule.mem_map_of_mem ha)

/-- The `L_p` class of `V_k f` is `V_k` of the class of `f`. -/
theorem toLp_valleePoussinBCF {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
    (hp : p ≠ ∞) (k : ℕ) (f : UnitAddTorus d →ᵇ ℂ) :
    BoundedContinuousFunction.toLp (E := ℂ) p volume 𝕜 (valleePoussinBCF k f) =
      valleePoussin hp k (BoundedContinuousFunction.toLp (E := ℂ) p volume 𝕜 f) :=
  toLp_econvBCF hp _ f

variable (d) in
/-- The **near-best constant** `1 + ‖Θ‖_1` of the smooth de la Vallée Poussin operators. -/
noncomputable def valleePoussinConst : ℝ≥0∞ :=
  1 + eLpNorm (Rd.bandKernel (V := EuclideanSpace ℝ d)) 1 volume

/-- The near-best constant is finite. -/
theorem valleePoussinConst_ne_top : valleePoussinConst d ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, Rd.eLpNorm_bandKernel_ne_top⟩

/-- The near-best constant is `1 + ∫ |Θ_j|` for every `j`, as a real number. -/
theorem toReal_valleePoussinConst (j : ℕ) :
    (valleePoussinConst d).toReal = 1 + ∫ y, ‖Rd.Theta (V := EuclideanSpace ℝ d) j y‖ := by
  rw [integral_norm_eq_lintegral_eNorm
    (Rd.integrable_Theta (V := EuclideanSpace ℝ d) j).aestronglyMeasurable,
    Rd.lintegral_enorm_Theta, valleePoussinConst,
    ENNReal.toReal_add ENNReal.one_ne_top Rd.eLpNorm_bandKernel_ne_top, ENNReal.toReal_one]

/-- **The de la Vallée Poussin operators are near-best in `L_p`**: for every trigonometric
polynomial `a` of degree `< 2^k`, `‖F - V_k F‖_p ≤ (1 + ‖Θ‖_1) ‖F - a‖_p`, by the Lebesgue
inequality `ApproximationScheme.enorm_sub_apply_le_of_apply_eq`. -/
theorem enorm_sub_valleePoussin_le (hp : p ≠ ∞) {k : ℕ}
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p (2 ^ k))
    (F : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖F - valleePoussin hp k F‖ₑ ≤ valleePoussinConst d * ‖F - a‖ₑ := by
  rw [valleePoussinConst, ← Rd.lintegral_enorm_Theta (k + Fintype.card d)]
  exact ApproximationScheme.enorm_sub_apply_le_of_apply_eq (fun x => enorm_econvLp_le hp _ x)
    (valleePoussin_eq_self hp ha) F

/-- **The de la Vallée Poussin operators are near-best in the sup norm**: for every trigonometric
polynomial `a` of degree `< 2^k`, `‖f - V_k f‖_∞ ≤ (1 + ‖Θ‖_1) ‖f - a‖_∞`, by the Lebesgue
inequality `ApproximationScheme.norm_sub_apply_le_of_apply_eq`. -/
theorem norm_sub_valleePoussinBCF_le {k : ℕ} {a : UnitAddTorus d →ᵇ ℂ}
    (ha : a ∈ trigPoly d (2 ^ k)) (f : UnitAddTorus d →ᵇ ℂ) :
    ‖f - valleePoussinBCF k f‖ ≤ (valleePoussinConst d).toReal * ‖f - a‖ := by
  rw [toReal_valleePoussinConst (k + Fintype.card d)]
  exact ApproximationScheme.norm_sub_apply_le_of_apply_eq (fun x => norm_econvBCF_le _ x)
    (valleePoussinBCF_eq_self ha) f

/-- **The de la Vallée Poussin operators converge uniformly**: `V_k f → f` in the sup norm for
every bounded continuous `f`, since `‖f - V_k f‖_∞ ≤ (1 + ‖Θ‖_1) E_{2^k}(f)_∞ → 0`. -/
theorem tendsto_valleePoussinBCF (f : UnitAddTorus d →ᵇ ℂ) :
    Tendsto (fun k => valleePoussinBCF k f) atTop (𝓝 f) := by
  have hE : Tendsto (fun k => valleePoussinConst d * (trigScheme d).approxError f (2 ^ k)) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ((tendsto_approxError_trigScheme f).comp
      (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) one_lt_two)) (Or.inr valleePoussinConst_ne_top)
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun _ => bot_le)
    fun k => ?_
  rw [edist_comm, eDist_eq_eNorm_sub]
  refine ApproximationScheme.le_mul_approxError_of_forall_mem valleePoussinConst_ne_top
    fun a ha => ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_toReal (valleePoussinConst_ne_top (d := d)),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (norm_sub_valleePoussinBCF_le ha f)

/-- **The weighted rate of the de la Vallée Poussin operators**: for `F ∈ A^β_1` of the
trigonometric scheme in `L_p(𝕋^d)`, `β ≥ 0`, `2^(kβ) ‖F - V_k F‖_p → 0`. The canonical near-best
approximants `a_k` have this rate, and `‖F - V_k F‖_p ≤ (1 + ‖Θ‖_1) ‖F - a_k‖_p`. -/
theorem tendsto_dyadicWeight_mul_enorm_sub_valleePoussin (hp : p ≠ ∞) {β : ℝ} (hβ : 0 ≤ β)
    {F : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hF : ((trigScheme d).toLp volume p).MemApprox β 1 F) :
    Tendsto (fun k => dyadicWeight β k * ‖F - valleePoussin hp k F‖ₑ) atTop (𝓝 0) := by
  set D := ApproximationScheme.canonicalApprox ((trigScheme d).toLp volume p) β F
  have hD := D.tendsto_dyadicWeight_mul_enorm_sub (ApproximationScheme.tsum_canonical_ne_top hβ hF)
  have hC := ENNReal.Tendsto.const_mul hD (Or.inr (valleePoussinConst_ne_top (d := d)))
  rw [mul_zero] at hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC (fun _ => bot_le)
    fun k => ?_
  calc dyadicWeight β k * ‖F - valleePoussin hp k F‖ₑ
      ≤ dyadicWeight β k * (valleePoussinConst d * ‖F - D.a k‖ₑ) := by
        gcongr
        exact enorm_sub_valleePoussin_le hp (mem_toLp_trigScheme_iff.1 (D.mem k)) F
    _ = valleePoussinConst d * (dyadicWeight β k * ‖F - D.a k‖ₑ) := by ring

/-! ### The trace of a continuous function -/

variable {n : ℕ}

/-- The restriction to the face is continuous for the sup norm. -/
theorem continuous_restrictFace (n : ℕ) : Continuous (restrictFace n) :=
  BoundedContinuousFunction.continuous_compContinuous (face n)

/-- The `L_p` class of `V_k f` on `𝕋^(n+1)` is an approximant of complexity `2^(k+n+3)` of the
trigonometric scheme in `L_p`. -/
theorem toLpR_valleePoussinBCF_mem (k : ℕ) (f : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ) :
    toLpR p (Fin (n + 1)) (valleePoussinBCF k f) ∈
      (trigScheme (Fin (n + 1))).toLp volume p (2 ^ (k + (n + 3))) := by
  have h := valleePoussinBCF_mem_trigPoly k f
  rw [Fintype.card_fin, show k + (n + 1) + 2 = k + (n + 3) by omega] at h
  exact FunctionScheme.toLp_mem_toLp h

/-- **The trace of a continuous function is its restriction**: for `1 ≤ p < ∞` and a bounded
continuous `f` on `𝕋^(n+1)` whose class lies in `B^{1/p}_{p,1}(𝕋^(n+1))`, the trace of `f` is
`f(0, ·)`. The traces `(V_k f)(0, ·)` of the de la Vallée Poussin approximants converge to the
trace (`ApproximationScheme.TraceBound.tendsto_ext`) and, uniformly, to `f(0, ·)`. -/
theorem traceBound_ext_eq_restrictFace (hp : p ≠ ∞) (f : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ)
    (hf : (trigScheme (Fin (n + 1))).MemBesov volume p p.toReal⁻¹ 1 (toLpR p (Fin (n + 1)) f)) :
    (traceBound p n hp).ext (toLpR p (Fin (n + 1)) f) = toLpR p (Fin n) (restrictFace n f) := by
  have hβ : 0 ≤ p.toReal⁻¹ := by positivity
  have hrate : Tendsto (fun k => dyadicWeight p.toReal⁻¹ k *
      ‖toLpR p (Fin (n + 1)) f - toLpR p (Fin (n + 1)) (valleePoussinBCF k f)‖ₑ) atTop
      (𝓝 0) := by
    simpa only [toLpR, ContinuousLinearMap.coe_coe, toLp_valleePoussinBCF hp] using
      tendsto_dyadicWeight_mul_enorm_sub_valleePoussin hp hβ hf
  have h1 := (traceBound p n hp).tendsto_ext hβ hf (fun k => toLpR_valleePoussinBCF_mem k f) hrate
  have hT : ∀ k, (traceBound p n hp).T (toLpR p (Fin (n + 1)) (valleePoussinBCF k f)) =
      toLpR p (Fin n) (restrictFace n (valleePoussinBCF k f)) := fun k =>
    traceBound_T_toLp p hp (valleePoussinBCF_mem_trigPoly k f)
  have h2 : Tendsto (fun k => toLpR p (Fin n) (restrictFace n (valleePoussinBCF k f))) atTop
      (𝓝 (toLpR p (Fin n) (restrictFace n f))) :=
    (((BoundedContinuousFunction.toLp (E := ℂ) p volume ℝ).continuous.comp
      (continuous_restrictFace n)).tendsto f).comp (tendsto_valleePoussinBCF f)
  simp only [hT] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The trace of a continuous Besov function is its restriction**: for `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞` and a bounded continuous `f` on `𝕋^(n+1)` whose class lies in
`B^{s+1/p}_{p,q}(𝕋^(n+1))`, the trace of `f` is `f(0, ·)`. -/
theorem trace_besov_eq_restrictFace (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ)
    (hf : (trigScheme (Fin (n + 1))).MemBesov volume p (s + p.toReal⁻¹) q
      (toLpR p (Fin (n + 1)) f)) :
    (traceBound p n hp).ext (toLpR p (Fin (n + 1)) f) = toLpR p (Fin n) (restrictFace n f) :=
  traceBound_ext_eq_restrictFace hp f (ApproximationScheme.MemApprox.mono hq le_rfl
    (by positivity) (Or.inl (by linarith)) hf)

/-- **The trace of a continuous function, almost everywhere**: under the hypotheses of
`Torus.traceBound_ext_eq_restrictFace`, the trace of `f` is `x' ↦ f(0, x')` almost everywhere
on `𝕋^n`. -/
theorem ae_trace_eq_restrictFace (hp : p ≠ ∞) (f : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ)
    (hf : (trigScheme (Fin (n + 1))).MemBesov volume p p.toReal⁻¹ 1 (toLpR p (Fin (n + 1)) f)) :
    ⇑((traceBound p n hp).ext (toLpR p (Fin (n + 1)) f)) =ᵐ[volume]
      fun x' => f (Fin.cons 0 x') := by
  rw [traceBound_ext_eq_restrictFace hp f hf]
  exact BoundedContinuousFunction.coeFn_toLp (E := ℂ) p volume ℝ (restrictFace n f)

/-- **Every smooth enough Besov function has a continuous representative whose restriction is its
trace**: for `1 ≤ p < ∞`, `s > n/p` and `1 ≤ q ≤ ∞`, every `F ∈ B^{s+1/p}_{p,q}(𝕋^(n+1))` is the
class of a bounded continuous `f` (the Besov embedding, since `s + 1/p > (n+1)/p`), and the trace
of `F` is `f(0, ·)`. -/
theorem exists_trace_eq_restrictFace (hp : p ≠ ∞) {s : ℝ} (hs : (n : ℝ) * p.toReal⁻¹ < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure (UnitAddTorus (Fin (n + 1))))}
    (hF : (trigScheme (Fin (n + 1))).MemBesov volume p (s + p.toReal⁻¹) q F) :
    ∃ f : UnitAddTorus (Fin (n + 1)) →ᵇ ℂ, toLpR p (Fin (n + 1)) f = F ∧
      (traceBound p n hp).ext F = toLpR p (Fin n) (restrictFace n f) := by
  have hD : (Fintype.card (Fin (n + 1)) : ℝ) * p.toReal⁻¹ < s + p.toReal⁻¹ := by
    rw [Fintype.card_fin]
    push_cast
    linarith
  obtain ⟨f, hf⟩ := FunctionScheme.MemBesov.exists_boundedContinuous trigScheme_hasNikolskii
    (Nat.cast_nonneg _) hD hq hF
  rw [BoundedContinuousFunction.inclusionOfExponentLe_toLp] at hf
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  subst hf
  exact ⟨f, rfl, trace_besov_eq_restrictFace hp hs0 hq f hF⟩

end Torus
