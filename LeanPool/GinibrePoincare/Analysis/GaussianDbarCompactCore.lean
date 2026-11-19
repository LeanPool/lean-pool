/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarCompactCore.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarSmoothTests

/-! # Compact smooth Gaussian antiholomorphic graph core -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem gaussianL2_toLp_tendsto_of_dominated_error {n : ℕ}
    (f : ℕ → Configuration n → ℂ) (g : Configuration n → ℂ)
    (hf : ∀ m, MemLp (f m) 2 (complexGaussianMeasure n))
    (hg : MemLp g 2 (complexGaussianMeasure n))
    (a : Configuration n → ℝ) (ha : Integrable (fun z => a z ^ 2) (complexGaussianMeasure n))
    (hbound : ∀ m z, ‖f m z - g z‖ ≤ a z)
    (ht : ∀ z, Tendsto (fun m => f m z) atTop (𝓝 (g z))) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hg.toLp g)) := by
  have hnorm (m : ℕ) :
      dist ((hf m).toLp (f m)) (hg.toLp g) =
        Real.sqrt (∫ z, ‖f m z - g z‖ ^ 2 ∂complexGaussianMeasure n) := by
    have he : (∫ z, ‖f m z - g z‖ ^ 2 ∂complexGaussianMeasure n) =
        ‖(hf m).toLp (f m) - hg.toLp g‖ ^ 2 := by
      rw [← integral_norm_sq_eq_L2_norm_sq (complexGaussianMeasure n)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hf m).toLp (f m)) (hg.toLp g),
        (hf m).coeFn_toLp, hg.coeFn_toLp] with z hz hfm hgm
      simp only [hz, Pi.sub_apply, hfm, hgm]
    rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]
  have hi : Tendsto (fun m => ∫ z, ‖f m z - g z‖ ^ 2 ∂complexGaussianMeasure n)
      atTop (𝓝 0) := by
    rw [← integral_zero (μ := complexGaussianMeasure n) (G := ℝ)]
    apply tendsto_integral_of_dominated_convergence (fun z => a z ^ 2)
    · intro m
      exact ((hf m).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2
    · exact ha
    · intro m
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn := norm_nonneg (f m z - g z)
      have hb := hbound m z
      nlinarith
    · filter_upwards with z
      simpa using (((ht z).sub_const (g z)).norm).pow 2
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [hnorm]
  simpa using hi.sqrt

/-- Value approximation by actual smooth compact spatial cutoffs. -/
theorem gaussianSpatialCutoff_value_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n))
    (hm : ∀ m, MemLp (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z)
      2 (complexGaussianMeasure n)) :
    Tendsto (fun m => (hm m).toLp (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z))
      atTop (𝓝 (hf.toLp f)) := by
  apply gaussianL2_toLp_tendsto_of_dominated_error _ _ hm hf (fun z => ‖f z‖)
  · exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  · intro m z
    have hχ := ginibreSpatialCutoff_mem_unit n m z
    have he : (ginibreSpatialCutoff n m z : ℂ) * f z - f z =
        ((ginibreSpatialCutoff n m z : ℂ) - 1) * f z := by ring
    rw [he, norm_mul]
    have hn : ‖(ginibreSpatialCutoff n m z : ℂ) - 1‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_of_le_one_left (norm_nonneg _) hn
  · intro z
    simpa using (Complex.continuous_ofReal.tendsto 1 |>.comp
      (ginibreSpatialCutoff_tendsto n z)).mul_const (f z)

theorem gaussianSpatialCutoff_value_memLp {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) (m : ℕ) :
    MemLp (fun z => (ginibreSpatialCutoff n m z : ℂ) * f z) 2 (complexGaussianMeasure n) := by
  apply hf.of_le_mul (c := 1) ((Complex.continuous_ofReal.comp
    (ginibreSpatialCutoff_smooth n m).continuous).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ginibreSpatialCutoff_mem_unit n m z).2

theorem gaussianSpatialCutoff_derivativeTerm_memLp {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) (m : ℕ) :
    MemLp (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * f z)
      2 (complexGaussianMeasure n) := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  apply hf.of_le_mul (c := M) ((Complex.continuous_ofReal.comp
    (((sobolevCutoff_smooth m).continuous_deriv (by simp)).comp
      contDiff_configurationNormSq.continuous)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))

theorem gaussianSpatialCutoff_derivativeTerm_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) :
    Tendsto (fun m => (gaussianSpatialCutoff_derivativeTerm_memLp f hf m).toLp
      (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * f z))
      atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  have hg : MemLp (fun _ : Configuration n => (0 : ℂ)) 2 (complexGaussianMeasure n) := MemLp.zero'
  have ht := gaussianL2_toLp_tendsto_of_dominated_error
    (fun m z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * f z)
    (fun _ => 0) (gaussianSpatialCutoff_derivativeTerm_memLp f hf) hg
    (fun z => M * ‖f z‖) ?_ ?_ ?_
  · simpa using ht
  · have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    simpa [mul_pow] using hi.const_mul (M ^ 2)
  · intro m z
    simp only [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
  · intro z
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp
      (sobolevCutoff_tendsto (configurationNormSq z)).2).mul_const (f z)

/-- Smooth finite-energy functions whose coordinate products are square
 integrable have compact C∞ graph approximations. -/
theorem gaussianSpatialCutoff_graph_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hfs : ContDiff ℝ ∞ f)
    (hf : MemLp f 2 (complexGaussianMeasure n))
    (hD : ∀ j : Fin n, MemLp (dbarComponent f j) 2 (complexGaussianMeasure n))
    (hZ : ∀ j : Fin n, MemLp (fun z => z j * f z) 2 (complexGaussianMeasure n)) :
    let F := fun m z => (ginibreSpatialCutoff n m z : ℂ) * f z
    ∃ (hF : ∀ m, ContDiff ℝ 1 (F m)) (hcF : ∀ m, HasCompactSupport (F m)),
      Tendsto (fun m => smoothCompactL2 (F m) (hF m) (hcF m)) atTop (𝓝 (hf.toLp f)) ∧
      ∀ j, Tendsto (fun m => smoothDbarComponentL2 (F m) (hF m) (hcF m) j)
        atTop (𝓝 ((hD j).toLp (dbarComponent f j))) := by
  let F := fun m z => (ginibreSpatialCutoff n m z : ℂ) * f z
  have hF (m : ℕ) : ContDiff ℝ 1 (F m) :=
    (Complex.ofRealCLM.contDiff.comp ((ginibreSpatialCutoff_smooth n m).of_le (by simp))).mul
      (hfs.of_le (by simp))
  have hcF (m : ℕ) : HasCompactSupport (F m) :=
    ((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right
  refine ⟨hF, hcF, ?_, ?_⟩
  · have he (m : ℕ) : smoothCompactL2 (F m) (hF m) (hcF m) =
        (gaussianSpatialCutoff_value_memLp f hf m).toLp (F m) := by
      apply Lp.ext
      exact (smoothCompactL2_coeFn (F m) (hF m) (hcF m)).trans
        (gaussianSpatialCutoff_value_memLp f hf m).coeFn_toLp.symm
    exact (gaussianSpatialCutoff_value_tendsto f hf
      (gaussianSpatialCutoff_value_memLp f hf)).congr (fun m => (he m).symm)
  · intro j
    let A := fun m => (gaussianSpatialCutoff_value_memLp (dbarComponent f j) (hD j) m).toLp
      (fun z => (ginibreSpatialCutoff n m z : ℂ) * dbarComponent f j z)
    let B := fun m => (gaussianSpatialCutoff_derivativeTerm_memLp (fun z => z j * f z) (hZ j)
        m).toLp
      (fun z => ((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ) * (z j * f z))
    have he (m : ℕ) : smoothDbarComponentL2 (F m) (hF m) (hcF m) j = A m + B m := by
      apply Lp.ext
      filter_upwards [smoothDbarComponentL2_coeFn (F m) (hF m) (hcF m) j,
        Lp.coeFn_add (A m) (B m),
        (gaussianSpatialCutoff_value_memLp (dbarComponent f j) (hD j) m).coeFn_toLp,
        (gaussianSpatialCutoff_derivativeTerm_memLp (fun z => z j * f z) (hZ j) m).coeFn_toLp]
        with z hz hab ha hb
      rw [hz, hab]
      change dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) * f w) j z = A m z + B m z
      have hχd : Differentiable ℝ (fun w : Configuration n => (ginibreSpatialCutoff n m w : ℂ)) :=
        (Complex.ofRealCLM.contDiff.comp ((ginibreSpatialCutoff_smooth n m).of_le (by simp) :
          ContDiff ℝ 1 (ginibreSpatialCutoff n m))).differentiable (by norm_num)
      rw [dbarComponent_mul hχd (hfs.differentiable (by simp)), dbarComponent_gaussianSpatialCutoff]
      change A m z = _ at ha
      change B m z = _ at hb
      rw [ha, hb]
      ring
    have hA := gaussianSpatialCutoff_value_tendsto (dbarComponent f j) (hD j)
      (gaussianSpatialCutoff_value_memLp (dbarComponent f j) (hD j))
    have hB := gaussianSpatialCutoff_derivativeTerm_tendsto (fun z => z j * f z) (hZ j)
    exact (show Tendsto (fun m => A m + B m) atTop
      (𝓝 ((hD j).toLp (dbarComponent f j))) by simpa [A, B] using hA.add hB).congr
        (fun m => (he m).symm)

/-- Actual compact smooth value/antiholomorphic derivative tuples. -/
def gaussianCompactSmoothDbarGraph (n : ℕ) :
    Set (Lp ℂ 2 (complexGaussianMeasure n) × (Fin n → Lp ℂ 2 (complexGaussianMeasure n))) :=
  {p | ∃ f : Configuration n → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (p.1 : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] f ∧
    ∀ j, (p.2 j : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] dbarComponent f j}

theorem gaussian_smooth_pair_mem_compactDbarGraph_closure {n : ℕ}
    (f : Configuration n → ℂ) (hfs : ContDiff ℝ ∞ f)
    (hf : MemLp f 2 (complexGaussianMeasure n))
    (hD : ∀ j : Fin n, MemLp (dbarComponent f j) 2 (complexGaussianMeasure n))
    (hZ : ∀ j : Fin n, MemLp (fun z => z j * f z) 2 (complexGaussianMeasure n)) :
    (hf.toLp f, fun j => (hD j).toLp (dbarComponent f j)) ∈
      closure (gaussianCompactSmoothDbarGraph n) := by
  let F := fun m z => (ginibreSpatialCutoff n m z : ℂ) * f z
  obtain ⟨hF, hcF, hv, hd⟩ := gaussianSpatialCutoff_graph_tendsto f hfs hf hD hZ
  let p := fun m => (smoothCompactL2 (F m) (hF m) (hcF m),
    fun j => smoothDbarComponentL2 (F m) (hF m) (hcF m) j)
  apply isClosed_closure.mem_of_tendsto (hv.prodMk_nhds (tendsto_pi_nhds.mpr hd))
  apply Eventually.of_forall
  intro m
  apply subset_closure
  refine ⟨F m, ?_, hcF m, smoothCompactL2_coeFn (F m) (hF m) (hcF m), ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hfs
  · intro j
    exact smoothDbarComponentL2_coeFn (F m) (hF m) (hcF m) j

theorem contDiff_finiteHermiteFunction_smooth (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) : ContDiff ℝ ∞ (finiteHermiteFunction n hn c) := by
  classical
  unfold finiteHermiteFunction
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [show (∑ pq ∈ c.support,
    c pq • multivariateNormalized n hn pq.1 pq.2) =
      (fun z => ∑ pq ∈ c.support,
        c pq • multivariateNormalized n hn pq.1 pq.2 z) by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply]]
  exact ContDiff.sum fun pq _ =>
    (contDiff_multivariateNormalized_real_smooth n hn pq.1 pq.2).const_smul (c pq)

theorem memLp_coordinate_mul_finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    MemLp (fun z => z j * finiteHermiteFunction n hn c z) 2 (complexGaussianMeasure n) := by
  classical
  have he : (fun z => z j * finiteHermiteFunction n hn c z) =
      (fun z => ∑ pq ∈ c.support, c pq * (z j * multivariateNormalized n hn pq.1 pq.2 z)) := by
    funext z
    simp only [finiteHermiteFunction, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pq hpq
    ring
  rw [he]
  exact memLp_finsetSum _ (fun pq _ =>
    (memLp_two_coordinate_mul_multivariateNormalized n hn pq.1 pq.2 j).const_mul (c pq))

theorem gaussian_finiteHermite_mem_compactDbarGraph_closure (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (finiteHermiteCombination n hn c, fun j => finiteDbarComponentL2 n hn c j) ∈
      closure (gaussianCompactSmoothDbarGraph n) := by
  let f := finiteHermiteFunction n hn c
  have hf : MemLp f 2 (complexGaussianMeasure n) :=
    (Lp.memLp (finiteHermiteCombination n hn c)).ae_eq (finiteHermiteCombination_coeFn n hn c)
  have hd (j : Fin n) : MemLp (dbarComponent f j) 2 (complexGaussianMeasure n) :=
    (Lp.memLp (finiteDbarComponentL2 n hn c j)).ae_eq (finiteDbarComponentL2_coeFn n hn c j)
  have hv : hf.toLp f = finiteHermiteCombination n hn c :=
    Lp.ext (hf.coeFn_toLp.trans (finiteHermiteCombination_coeFn n hn c).symm)
  have hder (j : Fin n) : (hd j).toLp (dbarComponent f j) = finiteDbarComponentL2 n hn c j :=
    Lp.ext ((hd j).coeFn_toLp.trans (finiteDbarComponentL2_coeFn n hn c j).symm)
  have he := gaussian_smooth_pair_mem_compactDbarGraph_closure f
    (contDiff_finiteHermiteFunction_smooth n hn c) hf hd
    (memLp_coordinate_mul_finiteHermiteFunction n hn c)
  simpa only [hv, hder] using he

/-- Every actual Gaussian weak derivative tuple lies in the closure of the
 actual compact C∞ derivative graph. -/
theorem gaussianWeakDbar_mem_compactSmoothGraph_closure {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    (u, D) ∈ closure (gaussianCompactSmoothDbarGraph n) := by
  obtain ⟨hv, hd⟩ := gaussianWeakDbar_finiteHermite_approximation hn u D hu
  apply isClosed_closure.mem_of_tendsto (hv.prodMk_nhds (tendsto_pi_nhds.mpr hd))
  exact Eventually.of_forall fun s => gaussian_finiteHermite_mem_compactDbarGraph_closure n hn _

/-- Full identification of the actual compact smooth graph completion with
 the independently defined weak Gaussian derivative domain. -/
theorem closure_gaussianCompactSmoothDbarGraph {n : ℕ} (hn : 0 < n) :
    closure (gaussianCompactSmoothDbarGraph n) =
      {p | ∀ j, IsGaussianWeakDbar n p.1 (p.2 j) j} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨f, hf, hc, hv, hd⟩ j
      exact gaussian_smooth_weak_dbar hn j p.1 (p.2 j) f (hf.of_le (by simp)) hv (hd j)
    · have he : {p : Lp ℂ 2 (complexGaussianMeasure n) ×
          (Fin n → Lp ℂ 2 (complexGaussianMeasure n)) | ∀ j, IsGaussianWeakDbar n p.1 (p.2 j) j} =
          ⋂ j, {p | IsGaussianWeakDbar n p.1 (p.2 j) j} := by ext p; simp
      rw [he]
      apply isClosed_iInter
      intro j
      let T := fun p : Lp ℂ 2 (complexGaussianMeasure n) ×
        (Fin n → Lp ℂ 2 (complexGaussianMeasure n)) => (p.1, p.2 j)
      have hT : Continuous T := continuous_fst.prodMk
        ((continuous_apply j).comp continuous_snd)
      exact (isClosed_gaussianWeakDbar_graph n j).preimage hT
  · rintro p hp
    exact gaussianWeakDbar_mem_compactSmoothGraph_closure hn p.1 p.2 hp

/-- The compact C∞ core is dense in the maximal ordinary Schwartz
 distributional antiholomorphic derivative graph, with all derivatives
 converging simultaneously in the concrete weighted L² spaces. -/
theorem closure_gaussianCompactSmoothDbarGraph_schwartz {n : ℕ} (hn : 0 < n) :
    closure (gaussianCompactSmoothDbarGraph n) =
      {p | ∀ j, IsGaussianSchwartzDbar n p.1 (p.2 j) j} := by
  rw [closure_gaussianCompactSmoothDbarGraph hn]
  ext p
  simp only [Set.mem_ofPred_eq]
  exact forall_congr' (fun j => (gaussianSchwartzDbar_iff_weak hn p.1 (p.2 j) j).symm)

end
end GinibrePoincare

