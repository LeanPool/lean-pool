/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselIteratedLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierPotentialBase
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Smooth L² representatives and distributional derivatives

Integration by parts against Schwartz functions identifies classical
square-integrable derivatives with derivatives of their tempered
L² distributions.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap LineDeriv Laplacian
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The coordinate orthonormal basis of the Euclidean spatial `L²` carrier. -/
@[expose]
def regularisedL2CoordinateBasis : OrthonormalBasis (Fin 3) ℝ L2Vec3 :=
  OrthonormalBasis.mk (v := fun i : Fin 3 => PiLp.basisFun 2 ℝ (Fin 3) i) (by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [PiLp.basisFun_apply, PiLp.single, PiLp.inner_apply]
    simp [Pi.single_apply]) (by
    change ⊤ ≤ Submodule.span ℝ
      (Set.range (fun i : Fin 3 => PiLp.basisFun 2 ℝ (Fin 3) i))
    exact (PiLp.basisFun 2 ℝ (Fin 3)).span_eq.ge)

/-- Its basis vectors are the canonical spatial coordinate directions. -/
@[simp]
theorem regularisedL2CoordinateBasis_apply (i : Fin 3) :
    regularisedL2CoordinateBasis i = WithLp.toLp 2 (CKN.basisVec i) := by
  simp [regularisedL2CoordinateBasis, CKN.basisVec,
    PiLp.basisFun_apply, PiLp.toLp_single]

private theorem regularised_smooth_coordinate_integral
    (a : L2Vec3 → ℂ) (g : L2Vec3 → ComplexVec3)
    (hg : Integrable (fun x => a x • g x) volume) (i : Fin 3) :
    (∫ x, a x • g x ∂volume).ofLp i = ∫ x, a x * g x i ∂volume := by
  let P : ComplexVec3 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) i
  change P (∫ x, a x • g x ∂volume) = _
  rw [← P.integral_comp_comm hg]
  simp [P, PiLp.proj_apply, smul_eq_mul]

/-- A smooth L² vector field with an L² directional derivative has that
classical derivative as its tempered-distribution derivative. -/
theorem regularised_smooth_L2_lineDerivative
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : L2Vec3)
    (hfL2 : MemLp f (2 : ℝ≥0∞) volume)
    (hDfL2 : MemLp (fun x => fderiv ℝ f x v) (2 : ℝ≥0∞) volume) :
    ∂_{v} ((hfL2.toLp f : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      ((hDfL2.toLp (fun x => fderiv ℝ f x v) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) := by
  ext ψ i
  have hψ : MemLp (ψ : L2Vec3 → ℂ) 2 volume := ψ.memLp 2 volume
  have hψ' : MemLp (fun x : L2Vec3 => fderiv ℝ ψ x v) 2 volume := by
    convert (∂_{v} ψ).memLp 2 volume using 1
    funext x
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ x
  have hA : Integrable
      (fun x : L2Vec3 => (fderiv ℝ ψ x v) • f x) volume :=
    (memLp_one_iff_integrable).mp (hψ'.smul hfL2)
  have hB : Integrable
      (fun x : L2Vec3 => ψ x • fderiv ℝ f x v) volume :=
    (memLp_one_iff_integrable).mp (hψ.smul hDfL2)
  have hC : Integrable
      (fun x : L2Vec3 => ψ x • f x) volume :=
    (memLp_one_iff_integrable).mp (hψ.smul hfL2)
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := fun x : L2Vec3 => ψ x) (g := f)
    (v := v) hA hB hC
    (fun x hx => (ψ.smooth ⊤).differentiable (by norm_num) x)
    (fun x hx => hf.differentiable (by norm_num) x)
  have hIBPcoord :
      ∫ x : L2Vec3, ψ x * fderiv ℝ f x v i ∂volume =
        -∫ x : L2Vec3, fderiv ℝ ψ x v * f x i ∂volume := by
    have hproj := congrArg (fun z : ComplexVec3 => z.ofLp i) hIBP
    calc
      ∫ x : L2Vec3, ψ x * fderiv ℝ f x v i ∂volume =
          (∫ x : L2Vec3, ψ x • fderiv ℝ f x v ∂volume).ofLp i :=
            (regularised_smooth_coordinate_integral ψ
              (fun x => fderiv ℝ f x v) hB i).symm
      _ = (-∫ x : L2Vec3, fderiv ℝ ψ x v • f x ∂volume).ofLp i := hproj
      _ = -∫ x : L2Vec3, fderiv ℝ ψ x v * f x i ∂volume := by
            change -((∫ x : L2Vec3, fderiv ℝ ψ x v • f x ∂volume).ofLp i) = _
            rw [regularised_smooth_coordinate_integral
              (fun x => fderiv ℝ ψ x v) f hA i]
  have hLpA : Integrable
      (fun x : L2Vec3 => fderiv ℝ ψ x v • (hfL2.toLp f) x) volume :=
    (memLp_one_iff_integrable).mp (hψ'.smul (Lp.memLp (hfL2.toLp f)))
  have hLpB : Integrable
      (fun x : L2Vec3 => ψ x •
        (hDfL2.toLp (fun x => fderiv ℝ f x v)) x) volume :=
    (memLp_one_iff_integrable).mp
      (hψ.smul (Lp.memLp (hDfL2.toLp (fun x => fderiv ℝ f x v))))
  have hLpANeg : Integrable
      (fun x : L2Vec3 => (-∂_{v} ψ) x • (hfL2.toLp f) x) volume := by
    convert hLpA.neg using 1
    funext x
    change -((∂_{v} ψ) x) • (hfL2.toLp f) x =
      -((fderiv ℝ ψ x v) • (hfL2.toLp f) x)
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ x]
    rw [neg_smul]
  calc
    ((∂_{v} ((hfL2.toLp f : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3))) ψ).ofLp i =
        (((hfL2.toLp f : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) (-∂_{v} ψ)).ofLp i := by
            rw [TemperedDistribution.lineDerivOp_apply_apply]
    _ = (∫ x : L2Vec3, (-∂_{v} ψ) x • (hfL2.toLp f) x ∂volume).ofLp i := by
          rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    _ = -∫ x : L2Vec3, fderiv ℝ ψ x v * f x i ∂volume := by
          rw [regularised_smooth_coordinate_integral (fun x => (-∂_{v} ψ) x)
            (fun x => (hfL2.toLp f) x) hLpANeg i]
          calc
            ∫ x : L2Vec3, (-∂_{v} ψ) x * ((hfL2.toLp f) x).ofLp i ∂volume =
                ∫ x : L2Vec3, -(fderiv ℝ ψ x v * ((hfL2.toLp f) x).ofLp i) ∂volume := by
                  apply integral_congr_ae
                  filter_upwards [] with x
                  rw [show (-∂_{v} ψ) x = -(fderiv ℝ ψ x v) by
                    change -((∂_{v} ψ) x) = _
                    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ x]]
                  ring
            _ = -∫ x : L2Vec3, fderiv ℝ ψ x v * ((hfL2.toLp f) x).ofLp i ∂volume :=
                  integral_neg _
            _ = -∫ x : L2Vec3, fderiv ℝ ψ x v * f x i ∂volume := by
                  congr 1
                  apply integral_congr_ae
                  filter_upwards [hfL2.coeFn_toLp] with x hx
                  rw [hx]
    _ = ∫ x : L2Vec3, ψ x * fderiv ℝ f x v i ∂volume := by
          exact hIBPcoord.symm
    _ = (∫ x : L2Vec3, ψ x •
        (hDfL2.toLp (fun x => fderiv ℝ f x v)) x ∂volume).ofLp i := by
          rw [regularised_smooth_coordinate_integral ψ
            (fun x => (hDfL2.toLp (fun x => fderiv ℝ f x v)) x) hLpB i]
          apply integral_congr_ae
          filter_upwards [hDfL2.coeFn_toLp] with x hx
          rw [hx]
    _ = (((hDfL2.toLp (fun x => fderiv ℝ f x v) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) ψ).ofLp i := by
          rw [MeasureTheory.Lp.toTemperedDistribution_apply]

/-- The pointwise classical spatial Laplacian on the Hilbert carrier. -/
@[expose]
def regularisedL2ClassicalLaplacian
    (f : L2Vec3 → ComplexVec3) : L2Vec3 → ComplexVec3 := fun x =>
  ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ f y (regularisedL2CoordinateBasis i)) x
      (regularisedL2CoordinateBasis i)

private theorem regularised_smooth_fderiv_contDiff
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : L2Vec3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) := by
  exact (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousLinearMap_comp
    (ContinuousLinearMap.apply ℝ ComplexVec3 v)

private theorem regularised_smooth_secondFderiv_contDiff
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v w : L2Vec3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) := by
  exact regularised_smooth_fderiv_contDiff
    (fun x => fderiv ℝ f x v)
    (regularised_smooth_fderiv_contDiff f hf v) w

private theorem regularisedL2ClassicalLaplacian_contDiff
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (regularisedL2ClassicalLaplacian f) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ f y (regularisedL2CoordinateBasis i)) x
      (regularisedL2CoordinateBasis i))
  exact ContDiff.sum (s := Finset.univ) (fun i hi =>
    regularised_smooth_secondFderiv_contDiff f hf
      (regularisedL2CoordinateBasis i) (regularisedL2CoordinateBasis i))

private theorem regularisedL2ClassicalLaplacian_iterate_contDiff
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((regularisedL2ClassicalLaplacian^[j]) f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact regularisedL2ClassicalLaplacian_contDiff _ ih

/-- The distributional Laplacian of a smooth L² field agrees with the
L² class of its classical Laplacian when its first and diagonal second
derivatives are square-integrable. -/
theorem regularised_smooth_L2_laplacian
    (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : MemLp f (2 : ℝ≥0∞) volume)
    (hD1 : ∀ i : Fin 3,
      MemLp (fun x => fderiv ℝ f x (regularisedL2CoordinateBasis i))
        (2 : ℝ≥0∞) volume)
    (hD2 : ∀ i : Fin 3,
      MemLp (fun x => fderiv ℝ
        (fun y => fderiv ℝ f y (regularisedL2CoordinateBasis i)) x
          (regularisedL2CoordinateBasis i)) (2 : ℝ≥0∞) volume) :
    Laplacian.laplacian
      ((hfL2.toLp f : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
    (((memLp_finsetSum Finset.univ (fun i _ => hD2 i)).toLp
      (regularisedL2ClassicalLaplacian f) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) := by
  let d1 : Fin 3 → L2Vec3 → ComplexVec3 := fun i x =>
    fderiv ℝ f x (regularisedL2CoordinateBasis i)
  let d2 : Fin 3 → L2Vec3 → ComplexVec3 := fun i x =>
    fderiv ℝ (d1 i) x (regularisedL2CoordinateBasis i)
  let q : L2Vec3 → ComplexVec3 := fun x => ∑ i : Fin 3, d2 i x
  have hq : MemLp q (2 : ℝ≥0∞) volume := by
    exact memLp_finsetSum Finset.univ (fun i _ => hD2 i)
  have hfirst (i : Fin 3) :
      ∂_{regularisedL2CoordinateBasis i}
        ((hfL2.toLp f : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
      (((hD1 i).toLp (d1 i) : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) := by
    exact regularised_smooth_L2_lineDerivative f hf
      (regularisedL2CoordinateBasis i) hfL2 (hD1 i)
  have hsecond (i : Fin 3) :
      ∂_{regularisedL2CoordinateBasis i}
        (((hD1 i).toLp (d1 i) : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) =
      (((hD2 i).toLp (d2 i) : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) := by
    exact regularised_smooth_L2_lineDerivative (d1 i)
      (regularised_smooth_fderiv_contDiff f hf (regularisedL2CoordinateBasis i))
      (regularisedL2CoordinateBasis i) (hD1 i) (hD2 i)
  have hclass :
      (hq.toLp q : ComplexVectorL2) =
        ∑ i : Fin 3, (hD2 i).toLp (d2 i) := by
    apply Lp.ext
    filter_upwards [hq.coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ
        (fun i : Fin 3 => (hD2 i).toLp (d2 i)),
      ae_all_iff.2 (fun i => (hD2 i).coeFn_toLp)] with x hqrep hsum hD2rep
    rw [hqrep, hsum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hD2rep i).symm
  have hMapSum :
      (∑ i : Fin 3,
        (((hD2 i).toLp (d2 i) : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3))) =
       (((∑ i : Fin 3, (hD2 i).toLp (d2 i) : ComplexVectorL2) :
          ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) := by
    let T : ComplexVectorL2 →L[ℂ] 𝓢'(L2Vec3, ComplexVec3) :=
      MeasureTheory.Lp.toTemperedDistributionCLM ComplexVec3 volume 2
    change ∑ i : Fin 3, T ((hD2 i).toLp (d2 i)) =
      T (∑ i : Fin 3, (hD2 i).toLp (d2 i))
    exact (map_sum T _ _).symm
  calc
    Laplacian.laplacian
        ((hfL2.toLp f : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
        ∑ i : Fin 3,
          ∂_{regularisedL2CoordinateBasis i}
            (∂_{regularisedL2CoordinateBasis i}
              ((hfL2.toLp f : ComplexVectorL2) :
                𝓢'(L2Vec3, ComplexVec3))) := by
          rw [TemperedDistribution.laplacian_eq_sum regularisedL2CoordinateBasis]
    _ = ∑ i : Fin 3,
          (((hD2 i).toLp (d2 i) : ComplexVectorL2) :
            𝓢'(L2Vec3, ComplexVec3)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hfirst i, hsecond i]
    _ = (((∑ i : Fin 3, (hD2 i).toLp (d2 i) : ComplexVectorL2) :
          ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) := hMapSum
    _ = ((hq.toLp q : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) := by
          exact congrArg (fun z : ComplexVectorL2 =>
            (z : 𝓢'(L2Vec3, ComplexVec3))) hclass.symm

/-- Smooth fields with all classical Laplacian iterates and their first
two coordinate derivatives in L² have the matching even-order Bessel lift. -/
theorem regularised_smooth_L2_even_lift_of_classical_iterates
    (k : ℕ) (f : L2Vec3 → ComplexVec3) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hLp : ∀ j : ℕ,
      MemLp ((regularisedL2ClassicalLaplacian^[j]) f)
        (2 : ℝ≥0∞) volume)
    (hD1 : ∀ j : ℕ, ∀ i : Fin 3,
      MemLp (fun x => fderiv ℝ
        ((regularisedL2ClassicalLaplacian^[j]) f) x
          (regularisedL2CoordinateBasis i)) (2 : ℝ≥0∞) volume)
    (hD2 : ∀ j : ℕ, ∀ i : Fin 3,
      MemLp (fun x => fderiv ℝ
        (fun y => fderiv ℝ ((regularisedL2ClassicalLaplacian^[j]) f) y
          (regularisedL2CoordinateBasis i)) x
            (regularisedL2CoordinateBasis i)) (2 : ℝ≥0∞) volume) :
    ∃ b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2,
      regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity) b = (hLp 0).toLp f := by
  let L : (L2Vec3 → ComplexVec3) → (L2Vec3 → ComplexVec3) :=
    regularisedL2ClassicalLaplacian
  let D : 𝓢'(L2Vec3, ComplexVec3) → 𝓢'(L2Vec3, ComplexVec3) :=
    Laplacian.laplacian
  let fL2 : ComplexVectorL2 := (hLp 0).toLp f
  have hrep (j : ℕ) :
      (D^[j]) (fL2 : 𝓢'(L2Vec3, ComplexVec3)) =
        (((hLp j).toLp ((L^[j]) f) : ComplexVectorL2) :
          𝓢'(L2Vec3, ComplexVec3)) := by
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        rw [ih]
        have hstep := regularised_smooth_L2_laplacian
          ((L^[j]) f) (regularisedL2ClassicalLaplacian_iterate_contDiff f hf j)
          (hLp j) (hD1 j) (hD2 j)
        have hclass :
            (memLp_finsetSum Finset.univ (fun i _ => hD2 j i)).toLp
                (L ((L^[j]) f)) =
              (hLp (j + 1)).toLp ((L^[j + 1]) f) := by
          apply MemLp.toLp_congr
          filter_upwards [] with x
          simp [Function.iterate_succ_apply']
        change Laplacian.laplacian
            (((hLp j).toLp ((L^[j]) f) : ComplexVectorL2) :
              𝓢'(L2Vec3, ComplexVec3)) =
          (((hLp (j + 1)).toLp ((L^[j + 1]) f) : ComplexVectorL2) :
            𝓢'(L2Vec3, ComplexVec3))
        rw [hstep]
        exact congrArg (fun z : ComplexVectorL2 =>
          (z : 𝓢'(L2Vec3, ComplexVec3))) hclass
  exact regularised_bessel_even_lift_of_iterated_laplacian_L2 k fL2
    (fun j hj => ⟨(hLp j).toLp ((L^[j]) f), by
      simpa [D, fL2, L] using hrep j⟩)

end CKN.Leray

end
