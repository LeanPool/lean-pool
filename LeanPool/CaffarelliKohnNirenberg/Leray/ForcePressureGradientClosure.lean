/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOrthogonality
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge

/-!
# The force-pressure gradient is a limit of test-function gradients

The gradients of smooth compactly supported functions span a subspace of
spatial L² whose orthogonal complement consists of weakly divergence-free
fields. By the orthogonality of (I - ℙ) f to those fields, the gradient
field of `lem:force-pressure` lies in the closure of the test gradients.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The classical gradient of a whole-space test function, as a coordinate
vector field. -/
@[expose]
def forcePressureTestGradient (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    Vec3 → Vec3 :=
  fun x i => φ.partialDeriv i x

/-- The gradient of a test function is continuous. -/
theorem forcePressureTestGradient_continuous
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    Continuous (forcePressureTestGradient φ) := by
  have hcont : Continuous (fderiv ℝ φ.toFun) :=
    φ.contDiff.continuous_fderiv (by simp)
  exact continuous_pi fun i => hcont.clm_apply continuous_const

/-- The gradient of a test function has compact support. -/
theorem forcePressureTestGradient_hasCompactSupport
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    HasCompactSupport (forcePressureTestGradient φ) := by
  let g : (Vec3 →L[ℝ] ℝ) → Vec3 := fun L i => L (basisVec i)
  have hg : g 0 = 0 := by
    funext i
    simp [g]
  exact φ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left hg

/-- The gradient of a test function is square integrable. -/
theorem forcePressureTestGradient_memLp
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    MemLp (forcePressureTestGradient φ) 2 volume :=
  (forcePressureTestGradient_continuous φ).memLp_of_hasCompactSupport
    (forcePressureTestGradient_hasCompactSupport φ)

/-- The gradient of a test function as a real spatial L² field. -/
@[expose]
def forcePressureTestGradientL2 (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    RealVectorL2 :=
  realVectorL2OfCoordinateFunction (forcePressureTestGradient φ)
    (forcePressureTestGradient_memLp φ)

/-- The coordinate representative evaluates the Hilbert field at the
corresponding point. -/
theorem realVectorL2Representative_apply (u : RealVectorL2) (x : Vec3) :
    realVectorL2Representative u x = WithLp.ofLp (u (WithLp.toLp 2 x)) :=
  rfl

/-- The coordinate representative of a real spatial L² field is square
integrable on the coordinate carrier. -/
theorem realVectorL2Representative_memLp_two (u : RealVectorL2) :
    MemLp (realVectorL2Representative u) (2 : ℝ≥0∞) (volume : Measure Vec3) := by
  have hcoord : MemLp (fun x : Vec3 => u (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp u).comp_measurePreserving vec3ToL2Vec3_measurePreserving
  exact hcoord.continuousLinearMap_comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap

/-- The coordinate representative is linear up to null sets. -/
theorem realVectorL2Representative_linearCombination_ae (a b : ℝ)
    (u v : RealVectorL2) :
    realVectorL2Representative (a • u + b • v) =ᵐ[volume]
      a • realVectorL2Representative u + b • realVectorL2Representative v := by
  have hsum := Lp.coeFn_add (a • u) (b • v)
  have hsu := Lp.coeFn_smul a u
  have hsv := Lp.coeFn_smul b v
  have h := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae
    (hsum.and (hsu.and hsv))
  filter_upwards [h] with x hx
  obtain ⟨h1, h2, h3⟩ := hx
  simp only [realVectorL2Representative_apply, Pi.add_apply, Pi.smul_apply]
  rw [h1, Pi.add_apply, h2, h3]
  rfl

/-- The sum of two whole-space test functions. -/
@[expose]
def forcePressureTestAdd (φ ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    WeakTestFunction (Set.univ : Set Vec3) where
  toFun := fun x => φ x + ψ x
  contDiff := φ.contDiff.add ψ.contDiff
  hasCompactSupport := φ.hasCompactSupport.add ψ.hasCompactSupport
  tsupport_subset := Set.subset_univ _

/-- A scalar multiple of a whole-space test function. -/
@[expose]
def forcePressureTestSmul (c : ℝ) (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    WeakTestFunction (Set.univ : Set Vec3) where
  toFun := fun x => c * φ x
  contDiff := contDiff_const.mul φ.contDiff
  hasCompactSupport := φ.hasCompactSupport.mul_left
  tsupport_subset := Set.subset_univ _

/-- The zero whole-space test function. -/
@[expose]
def forcePressureTestZero : WeakTestFunction (Set.univ : Set Vec3) where
  toFun := fun _ => 0
  contDiff := contDiff_const
  hasCompactSupport := HasCompactSupport.zero
  tsupport_subset := Set.subset_univ _

/-- The gradient of a sum of test functions is the sum of the gradients. -/
theorem forcePressureTestGradient_add (φ ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    forcePressureTestGradient (forcePressureTestAdd φ ψ) =
      forcePressureTestGradient φ + forcePressureTestGradient ψ := by
  funext x i
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    (φ.contDiff.differentiable (by simp)) x
  have hψ : DifferentiableAt ℝ ψ.toFun x :=
    (ψ.contDiff.differentiable (by simp)) x
  simp only [forcePressureTestGradient, WeakTestFunction.partialDeriv,
    forcePressureTestAdd, Pi.add_apply]
  change (fderiv ℝ (fun y => φ.toFun y + ψ.toFun y) x) (basisVec i) = _
  exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
    (hφ.hasFDerivAt.add hψ.hasFDerivAt).fderiv

/-- The gradient of a scalar multiple of a test function. -/
theorem forcePressureTestGradient_smul (c : ℝ)
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    forcePressureTestGradient (forcePressureTestSmul c φ) =
      c • forcePressureTestGradient φ := by
  funext x i
  have hφ : DifferentiableAt ℝ φ.toFun x :=
    (φ.contDiff.differentiable (by simp)) x
  simp only [forcePressureTestGradient, WeakTestFunction.partialDeriv,
    forcePressureTestSmul, Pi.smul_apply, smul_eq_mul]
  change (fderiv ℝ (fun y => c • φ.toFun y) x) (basisVec i) = _
  exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
    (hφ.hasFDerivAt.const_smul c).fderiv

private theorem forcePressureTestGradientL2_rep
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    realVectorL2Representative (forcePressureTestGradientL2 φ) =ᵐ[volume]
      forcePressureTestGradient φ :=
  realVectorL2OfCoordinateFunction_rep _ _

private theorem forcePressureTestGradientL2_add
    (φ ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    forcePressureTestGradientL2 (forcePressureTestAdd φ ψ) =
      forcePressureTestGradientL2 φ + forcePressureTestGradientL2 ψ := by
  apply realVectorL2Representative_injective_ae
  filter_upwards [forcePressureTestGradientL2_rep (forcePressureTestAdd φ ψ),
    forcePressureTestGradientL2_rep φ, forcePressureTestGradientL2_rep ψ,
    (show realVectorL2Representative
            (forcePressureTestGradientL2 φ + forcePressureTestGradientL2 ψ) =ᵐ[volume]
          realVectorL2Representative (forcePressureTestGradientL2 φ) +
            realVectorL2Representative (forcePressureTestGradientL2 ψ) by
      simpa only [one_smul] using realVectorL2Representative_linearCombination_ae 1 1
        (forcePressureTestGradientL2 φ) (forcePressureTestGradientL2 ψ))]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, forcePressureTestGradient_add, Pi.add_apply]

private theorem forcePressureTestGradientL2_smul (c : ℝ)
    (φ : WeakTestFunction (Set.univ : Set Vec3)) :
    forcePressureTestGradientL2 (forcePressureTestSmul c φ) =
      c • forcePressureTestGradientL2 φ := by
  apply realVectorL2Representative_injective_ae
  filter_upwards [forcePressureTestGradientL2_rep (forcePressureTestSmul c φ),
    forcePressureTestGradientL2_rep φ,
    (show realVectorL2Representative (c • forcePressureTestGradientL2 φ) =ᵐ[volume]
          c • realVectorL2Representative (forcePressureTestGradientL2 φ) by
      simpa only [zero_smul, add_zero] using realVectorL2Representative_linearCombination_ae
        c 0 (forcePressureTestGradientL2 φ) (forcePressureTestGradientL2 φ))]
    with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, forcePressureTestGradient_smul, Pi.smul_apply]

/-- The zero test function has zero gradient field. -/
theorem forcePressureTestGradientL2_zero :
    forcePressureTestGradientL2 forcePressureTestZero = 0 := by
  have h := forcePressureTestGradientL2_smul 0 forcePressureTestZero
  rw [zero_smul] at h
  have hz : forcePressureTestSmul 0 forcePressureTestZero = forcePressureTestZero := by
    simp only [forcePressureTestSmul, forcePressureTestZero, zero_mul]
  rw [hz] at h
  exact h

/-- The real subspace spanned by the gradients of whole-space test
functions. -/
@[expose]
def forcePressureTestGradientSpan : Submodule ℝ RealVectorL2 :=
  Submodule.span ℝ (Set.range forcePressureTestGradientL2)

/-- Every element of the span of the test gradients is the gradient of one
test function. -/
theorem forcePressureTestGradientSpan_mem_range {u : RealVectorL2}
    (hu : u ∈ forcePressureTestGradientSpan) :
    ∃ φ : WeakTestFunction (Set.univ : Set Vec3), forcePressureTestGradientL2 φ = u := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨forcePressureTestZero, forcePressureTestGradientL2_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, rfl⟩ := hx
    obtain ⟨ψ, rfl⟩ := hy
    exact ⟨forcePressureTestAdd φ ψ, forcePressureTestGradientL2_add φ ψ⟩
  | smul c x _ hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨forcePressureTestSmul c φ, forcePressureTestGradientL2_smul c φ⟩

/-- The pairing of a test gradient with a real spatial L² field is the
integral of the coordinate dot product. -/
theorem inner_forcePressureTestGradientL2_eq_integral
    (φ : WeakTestFunction (Set.univ : Set Vec3)) (w : RealVectorL2) :
    inner ℝ (forcePressureTestGradientL2 φ) w =
      ∫ x : Vec3, ∑ i : Fin 3, realVectorL2Representative w x i *
        φ.partialDeriv i x := by
  rw [L2.inner_def]
  rw [← vec3ToL2Vec3_measurePreserving.integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [forcePressureTestGradientL2_rep φ] with x hx
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hxi := congrFun hx i
  rw [realVectorL2Representative_apply] at hxi
  simp only [realVectorL2Representative_apply]
  change inner ℝ (WithLp.ofLp (forcePressureTestGradientL2 φ (WithLp.toLp 2 x)) i)
    (WithLp.ofLp (w (WithLp.toLp 2 x)) i) = _
  rw [hxi]
  simp [forcePressureTestGradient]

/-- A field orthogonal to all test gradients has a weakly divergence-free
representative. -/
theorem isWeakDivFree_of_mem_orthogonal_testGradientSpan {w : RealVectorL2}
    (hw : w ∈ forcePressureTestGradientSpanᗮ) :
    CKN.IsWeakDivFreeL2 (realVectorL2Representative w) := by
  refine ⟨realVectorL2Representative_memLp_two w, ?_⟩
  intro ψ
  have hmem : forcePressureTestGradientL2 ψ ∈ forcePressureTestGradientSpan :=
    Submodule.subset_span ⟨ψ, rfl⟩
  have h0 := (Submodule.mem_orthogonal _ _).1 hw _ hmem
  rw [inner_forcePressureTestGradientL2_eq_integral] at h0
  exact h0

/-- The force-pressure gradient field (I - ℙ) f of `lem:force-pressure` lies
in the closure of the test gradients. -/
theorem forcePressureGradientL2_mem_topologicalClosure (v : RealVectorL2) :
    forcePressureGradientL2 v ∈ forcePressureTestGradientSpan.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro w hw
  rw [real_inner_comm]
  exact forcePressureGradientL2_inner_eq_zero v w
    (isWeakDivFree_of_mem_orthogonal_testGradientSpan hw)

/-- The force-pressure gradient field (I - ℙ) f of `lem:force-pressure` is
an L² limit of gradients of test functions. -/
theorem exists_testGradient_tendsto_forcePressureGradientL2 (v : RealVectorL2) :
    ∃ φ : ℕ → WeakTestFunction (Set.univ : Set Vec3),
      Tendsto (fun n => forcePressureTestGradientL2 (φ n)) atTop
        (𝓝 (forcePressureGradientL2 v)) := by
  have hclosure := forcePressureGradientL2_mem_topologicalClosure v
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hclosure
  obtain ⟨u, hu, hlim⟩ := hclosure
  choose φ hφ using fun n => forcePressureTestGradientSpan_mem_range (hu n)
  refine ⟨φ, ?_⟩
  simpa only [hφ] using hlim

end CKN.Leray
