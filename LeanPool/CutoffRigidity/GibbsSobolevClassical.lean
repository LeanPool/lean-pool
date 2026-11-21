/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolev

/-!
# Actual C² L² functions with L² gradients belong to the closed energy domain

Compact cutoff graph approximation identifies the closed weak gradient with
the actual classical gradient. This is a domain bridge, not an assumed
regularity or self-adjointness identification.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal LinearPMap

/-- Actual L² dominated convergence, proved from the actual squared-norm
integral and scalar dominated convergence. -/
theorem tendsto_toL2_of_dominated_sq
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure α} {f : α → F} {fn : ℕ → α → F}
    (hf : MemLp f 2 μ) (hfn : ∀ n, MemLp (fn n) 2 μ) (g : α → ℝ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fn n x - f x‖ ^ 2 ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)) := by
  have hInt : Tendsto (fun n => ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖fn n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ)) g ?_ hg ?_ ?_
    · simpa using hh
    · intro n
      exact (((hfn n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2)
    · intro n
      filter_upwards [hbound n] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖fn n x - f x‖)]
      exact hx
    · filter_upwards [hlim] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2)
  have hnorm (n : ℕ) : ‖(hfn n).toLp (fn n) - hf.toLp f‖ ^ 2 = ∫ x, ‖fn n x - f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hfn n).toLp (fn n)) (hf.toLp f),
      (hfn n).coeFn_toLp, hf.coeFn_toLp] with x hsub hn hf'
    rw [hsub, Pi.sub_apply, hn, hf', real_inner_self_eq_norm_sq]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hInt
  simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual compact C² functions and their actual gradients belong to the
closed gradient graph, independent of the selected compact representative. -/
theorem compact_function_mem_closedGibbsGradient_graph {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    (hfLp.toLp f, hgLp.toLp (gradient f)) ∈ (closedGibbsGradient hV hprob).graph := by
  let u : compactGibbsGeneratorDomain V := ⟨hfLp.toLp f, f, hf, hfc, hfLp.coeFn_toLp.symm⟩
  have hr : f = compactGibbsRepresentative V u :=
    compactGibbsRepresentative_unique hV.continuous u hf.continuous hfLp.coeFn_toLp.symm
  have hout : compactGibbsGradient hV.continuous hprob u = hgLp.toLp (gradient f) := by
    apply Lp.ext
    filter_upwards [(compactGibbsGradient_memLp hprob u).coeFn_toLp, hgLp.coeFn_toLp] with x hu hx
    change (compactGibbsGradient_memLp hprob u).toLp _ x = _
    rw [hu, hx, ← hr]
  have hg := (compactGibbsGradient hV.continuous hprob).mem_graph u
  rw [hout] at hg
  exact LinearPMap.le_graph_of_le (compactGibbsGradient hV.continuous hprob).le_closure hg

/-- Actual C² functions with actual L² gradients lie in the closed weighted
H¹ graph. Compact cutoff approximation proves both components in L². -/
theorem c2_function_mem_closedGibbsGradient_graph {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    (hfLp.toLp f, hgLp.toLp (gradient f)) ∈ (closedGibbsGradient hV hprob).graph := by
  let μ := gibbsMeasure volume V
  let := hprob
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let fn (n : ℕ) (x : E) := χ n x ^ 2 * f x
  have hfn (n : ℕ) : ContDiff ℝ 2 (fn n) := ((hχ n).pow 2).mul hf
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := by
    have hc := (hχc n).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    simpa only [fn, Pi.mul_def, Function.comp_def] using hc.mul_right (f' := f)
  have hfnLp (n : ℕ) : MemLp (fn n) 2 μ := (hfn n).continuous.memLp_of_hasCompactSupport (hfnc n)
  have hGfn (n : ℕ) : Continuous (gradient (fn n)) :=
    continuous_gradient_of_c1 ((hfn n).of_le (by norm_num))
  have hgfnLp (n : ℕ) : MemLp (gradient (fn n)) 2 μ := by
    have hc := ((hfnc n).fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
    exact (hGfn n).memLp_of_hasCompactSupport hc
  have hGχlim := cutoff_gradient_tendsto_zero hχgrad
  have hχlim (x : E) : Tendsto (fun n => χ n x) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((hχone x).mono (fun n hn => hn.symm))
  have hGχbound := cutoff_gradient_le hC0 hχgrad
  have hsqχ (n : ℕ) (x : E) : 0 ≤ χ n x ^ 2 ∧ χ n x ^ 2 ≤ 1 := by
    have hb := hχbounds n x
    exact ⟨sq_nonneg _, by nlinarith⟩
  have hflim : Tendsto (fun n => (hfnLp n).toLp (fn n)) atTop (𝓝 (hfLp.toLp f)) := by
    apply tendsto_toL2_of_dominated_sq hfLp hfnLp (fun x => ‖f x‖ ^ 2) hfLp.norm.integrable_sq
    · intro n
      filter_upwards with x
      have hb := hsqχ n x
      dsimp only [fn]
      rw [Real.norm_eq_abs]
      have heq : χ n x ^ 2 * f x - f x = (χ n x ^ 2 - 1) * f x := by ring
      rw [heq, abs_mul, mul_pow, sq_abs, sq_abs]
      have hcoef : (χ n x ^ 2 - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (χ n x ^ 2)]
      calc
        _ ≤ 1 * f x ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ = _ := by simp [Real.norm_eq_abs]
    · filter_upwards with x
      simpa only [fn, one_pow, one_mul] using ((hχlim x).pow 2).mul_const (f x)
  have hgradformula (n : ℕ) (x : E) : gradient (fn n) x =
      χ n x ^ 2 • gradient f x + (2 * χ n x * f x) • gradient (χ n) x :=
    gradient_cutoff_square_mul ((hχ n).differentiable (by norm_num)) (hf.differentiable
      (by norm_num)) x
  have hglim : Tendsto (fun n => (hgfnLp n).toLp (gradient (fn n))) atTop
      (𝓝 (hgLp.toLp (gradient f))) := by
    let bound (x : E) := 2 * ‖gradient f x‖ ^ 2 + 8 * C ^ 2 * ‖f x‖ ^ 2
    have hboundInt : Integrable bound μ :=
      (hgLp.norm.integrable_sq.const_mul 2).add (hfLp.norm.integrable_sq.const_mul (8 * C ^ 2))
    apply tendsto_toL2_of_dominated_sq hgLp hgfnLp bound hboundInt
    · intro n
      filter_upwards with x
      have hb := hχbounds n x
      have hs := hsqχ n x
      have hA : |χ n x ^ 2 - 1| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
      have hB : |2 * χ n x * f x| ≤ 2 * |f x| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hb.1]
        nlinarith [abs_nonneg (f x)]
      have heq : gradient (fn n) x - gradient f x =
          (χ n x ^ 2 - 1) • gradient f x + (2 * χ n x * f x) • gradient (χ n) x := by
        rw [hgradformula]
        module
      have hn : ‖gradient (fn n) x - gradient f x‖ ≤ ‖gradient f x‖ + 2 * C * ‖f x‖ := by
        rw [heq]
        calc
          _ ≤ ‖(χ n x ^ 2 - 1) • gradient f x‖ + ‖(2 * χ n x * f x) • gradient (χ n) x‖
            := norm_add_le _ _
          _ = |χ n x ^ 2 - 1| * ‖gradient f x‖ + |2 * χ n x * f x| * ‖gradient (χ n) x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 * ‖gradient f x‖ + (2 * |f x|) * C := by gcongr; exact hGχbound n x
          _ = _ := by rw [Real.norm_eq_abs]; ring
      have hf0 := norm_nonneg (f x)
      have hg0 := norm_nonneg (gradient f x)
      have hn0 := norm_nonneg (gradient (fn n) x - gradient f x)
      dsimp only [bound]
      nlinarith [sq_nonneg (‖gradient f x‖ - 2 * C * ‖f x‖)]
    · filter_upwards with x
      have hh := (((hχlim x).pow 2).smul (tendsto_const_nhds (x := gradient f x))).add
        ((((hχlim x).const_mul 2).mul_const (f x)).smul (hGχlim x))
      simpa only [hgradformula, one_pow, one_smul, smul_zero, add_zero] using hh
  have hpairlim := hflim.prodMk_nhds hglim
  apply (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto hpairlim
  exact Filter.Eventually.of_forall (fun n => compact_function_mem_closedGibbsGradient_graph
    hV hprob (hfn n) (hfnc n) (hfnLp n) (hgfnLp n))

/-- Actual C² L² functions with L² gradients, as genuine elements of weighted H¹. -/
@[expose] noncomputable def c2GibbsSobolevLift {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) : gibbsSobolevGraph hV hprob :=
  ⟨WithLp.toLp 2 (hfLp.toLp f, hgLp.toLp (gradient f)),
    c2_function_mem_closedGibbsGradient_graph hV hprob hf hfLp hgLp⟩

theorem c2GibbsSobolevLift_inclusion {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    gibbsSobolevInclusion hV hprob (c2GibbsSobolevLift hV hprob hf hfLp hgLp) = hfLp.toLp f := rfl

theorem c2GibbsSobolevLift_derivative {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    gibbsSobolevDerivative hV hprob (c2GibbsSobolevLift hV hprob hf hfLp hgLp) =
      hgLp.toLp (gradient f) := rfl

/-- Caccioppoli supplies actual gradient L² membership for every classical eigenclass. -/
theorem classicalEigenRepresentative_gradient_memLp {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (u : classicalL2Eigenspace V ρ) :
    MemLp (gradient (classicalEigenRepresentative V ρ u)) 2 (gibbsMeasure volume V) :=
  eigenfunction_gradient_memLp_two hV (classicalEigenRepresentative_spec V ρ u).1
    (classicalEigenRepresentative_memLp V ρ u) ρ hρ (classicalEigenRepresentative_spec V ρ u).2.1

/-- Every actual classical eigenclass has a genuine closed-form-domain lift. -/
@[expose] noncomputable def classicalEigenSobolevLift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) : gibbsSobolevGraph hV hprob :=
  c2GibbsSobolevLift hV hprob (classicalEigenRepresentative_spec V ρ u).1
    (classicalEigenRepresentative_memLp V ρ u) (classicalEigenRepresentative_gradient_memLp hV ρ hρ
      u)

/-- Its inclusion is the original actual L² eigenclass. -/
theorem classicalEigenSobolevLift_inclusion {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) :
    gibbsSobolevInclusion hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u) =
      (u : E →₂[gibbsMeasure volume V] ℝ) := by
  apply Lp.ext
  filter_upwards [(classicalEigenRepresentative_memLp V ρ u).coeFn_toLp,
    (classicalEigenRepresentative_spec V ρ u).2.2] with x hx hu
  exact hx.trans hu

/-- The genuine actual gradient pairing against every compact-domain test. -/
theorem classicalEigen_compactGradient_pairing {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) (v : compactGibbsGeneratorDomain V) :
    inner ℝ (gibbsSobolevDerivative hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u))
      (compactGibbsGradient hV.continuous hprob v) =
      ρ * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (v : E →₂[gibbsMeasure volume V] ℝ) := by
  have hgrad : inner ℝ
      (gibbsSobolevDerivative hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u))
      (compactGibbsGradient hV.continuous hprob v) =
      ∫ x, inner ℝ (gradient (classicalEigenRepresentative V ρ u) x)
        (gradient (compactGibbsRepresentative V v) x) ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(classicalEigenRepresentative_gradient_memLp hV ρ hρ u).coeFn_toLp,
      (compactGibbsGradient_memLp hprob v).coeFn_toLp] with x hu hv
    change inner ℝ ((classicalEigenRepresentative_gradient_memLp hV ρ hρ u).toLp _ x)
      ((compactGibbsGradient_memLp hprob v).toLp _ x) = _
    rw [hu, hv]
  have hscalar : inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (v : E →₂[gibbsMeasure volume V] ℝ) =
      ∫ x, classicalEigenRepresentative V ρ u x * compactGibbsRepresentative V v x
        ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
      (compactGibbsRepresentative_spec V v).2.2] with x hu hv
    rw [← hu, ← hv, Real.inner_apply]
  have he := compact_test_gibbs_energy hV
    ((compactGibbsRepresentative_spec V v).1.of_le (by norm_num))
    (classicalEigenRepresentative_spec V ρ u).1 (compactGibbsRepresentative_spec V v).2.1
  have hl : (∫ x, compactGibbsRepresentative V v x *
      langevinDifferentialOperator V (classicalEigenRepresentative V ρ u) x ∂gibbsMeasure volume V)
        =
      -ρ * (∫ x, classicalEigenRepresentative V ρ u x * compactGibbsRepresentative V v x
        ∂gibbsMeasure volume V) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [(classicalEigenRepresentative_spec V ρ u).2.1]
    ring
  rw [hl] at he
  have hcomm : (∫ x, inner ℝ (gradient (compactGibbsRepresentative V v) x)
      (gradient (classicalEigenRepresentative V ρ u) x) ∂gibbsMeasure volume V) =
      ∫ x, inner ℝ (gradient (classicalEigenRepresentative V ρ u) x)
        (gradient (compactGibbsRepresentative V v) x) ∂gibbsMeasure volume V :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
  rw [hcomm] at he
  rw [hgrad, hscalar]
  linarith

/-- The actual classical eigenclass satisfies the weak eigenfunction
identity against every member of the genuine closed energy domain. -/
theorem classicalEigenSobolevLift_weak_eigenfunction {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) (v : gibbsSobolevGraph hV hprob) :
    gibbsDirichletEnergy hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u) v =
      ρ * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) := by
  let G := compactGibbsGradient hV.continuous hprob
  let gu := gibbsSobolevDerivative hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u)
  let S : Set ((E →₂[gibbsMeasure volume V] ℝ) × (E →₂[gibbsMeasure volume V] E)) :=
    {p | inner ℝ gu p.2 = ρ * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) p.1}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner continuous_snd)
    ((continuous_const.inner continuous_fst).const_mul ρ)
  have hinit : (G.graph : Set _) ⊆ S := by
    intro p hp
    obtain ⟨w, hwf, hwg⟩ := G.mem_graph_iff.mp hp
    change inner ℝ gu p.2 = ρ * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) p.1
    rw [← hwf, ← hwg]
    exact classicalEigen_compactGradient_pairing hV hprob ρ hρ u w
  exact closure_minimal hinit hS
    (gibbsSobolev_mem_closure_compactGradient hV hprob v)

/-- The variational resolvent acts on each actual classical eigenclass with
the expected shifted eigenvalue. This supplies a graph witness for the
canonical closed-form realization, without essential self-adjointness. -/
theorem gibbsL2Resolvent_classicalEigen {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u : classicalL2Eigenspace V ρ) :
    gibbsL2Resolvent hV hprob ((1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ)) =
      (u : E →₂[gibbsMeasure volume V] ℝ) := by
  have heq : classicalEigenSobolevLift hV hprob ρ hρ u =
      gibbsWeakResolvent hV hprob ((1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ)) := by
    apply ext_inner_right ℝ
    intro v
    calc
      _ = inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) +
          ρ * inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (gibbsSobolevInclusion hV hprob v) := by
        have hi := gibbsSobolev_inner hV hprob (classicalEigenSobolevLift hV hprob ρ hρ u) v
        have hj := classicalEigenSobolevLift_inclusion hV hprob ρ hρ u
        have he := classicalEigenSobolevLift_weak_eigenfunction hV hprob ρ hρ u v
        rw [hj] at hi
        linarith
      _ = inner ℝ ((1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ))
          (gibbsSobolevInclusion hV hprob v) := by rw [real_inner_smul_left]; ring
      _ = _ := (ContinuousLinearMap.adjoint_inner_left (gibbsSobolevInclusion hV hprob) v
        ((1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ))).symm
  change gibbsSobolevInclusion hV hprob
    (gibbsWeakResolvent hV hprob ((1 + ρ) • (u : E →₂[gibbsMeasure volume V] ℝ))) = _
  rw [← heq, classicalEigenSobolevLift_inclusion hV hprob ρ hρ u]

end CutoffRigidity
