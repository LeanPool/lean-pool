/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.HistoryMajorization
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.CenteredEnergyIdentity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# High-contrast homogenization: Entry.Response.Core.SkewShearCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The skew-shear congruence of the coarse block

This file develops the skew-shear congruence that removes the skew part of the coarse block matrix
in the proof of `adapted_response_core`: it shows the shear conjugation subtracts exactly the skew
component, expresses the sheared block-matrix-vector product and block energy density in terms of
the unsheared ones, and proves the shear preserves the admissible class of Radon measures. It also
proves the helper facts the response-imbalance comparison needs: monotonicity of the canonical
imbalance, the index bound `j* < s` at a raw sample, and the elementary inequalities relating the
determinant ratio to the scale factor. The congruence serves the response transfer
`p.response.transfer`; the imbalance helpers serve the comparison `e.response.imbalance.comparison`.
-/

section
/-!
## The skew-shear congruence and response-imbalance helpers

This file develops the skew-shear congruence for the coarse block matrix in the proof of
`adapted_response_core`, together with the admissible-class lemmas it rests on and the helper
lemmas for the response-imbalance comparison.
-/

open HCPolySupport.HighContrast (CoeffSpace aspectRatio matSqrt matSqrt_spec)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The skew-shear congruence

The identity `coarseBlockMatrix U (fun x => a x - g) = blockCongr (1, 0, g, 1) (coarseBlockMatrix
U a)`
for a constant skew matrix `g` (`p.response.transfer`), together with the admissible-class
lemmas it rests on.  It is the mathematical content of `annealedBlockOf_respCoeffMinus_eq`,
proved here from the CoarseGraining primitives. -/

private theorem memVectorL2_const_matVecMul {d : ℕ} {U : Set (Vec d)}
    (g : Mat d) {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x ↦ matVecMul g (f x)) := by
  rw [MemVectorL2, MeasureTheory.memLp_pi_iff] at hf ⊢
  intro i
  simpa [matVecMul] using MeasureTheory.memLp_finsetSum Finset.univ
    (fun j _ ↦ (hf j).const_mul (g i j))

private theorem memScalarL2_euclideanCoordDeriv {d : ℕ}
    (U : Set (Vec d)) (i : Fin d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u) :
    MemScalarL2 U (euclideanCoordDeriv i u) := by
  simpa [MemScalarL2, volumeMeasureOn] using
    ((contDiff_euclideanCoordDeriv hu i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hu_supp i)).restrict U

private theorem hasCompactSupport_finset_sum
    {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β]
    (s : Finset ι) (f : ι → α → β)
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simpa using! (HasCompactSupport.zero : HasCompactSupport (fun _ : α ↦ (0 : β)))
  · intro a s has hs hf
    have ha : HasCompactSupport (f a) := hf a (by simp [has])
    have hs' : HasCompactSupport (fun x ↦ ∑ i ∈ s, f i x) := by
      exact hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert has] using! ha.add hs'

private theorem smooth_skew_gradient_pairing_zero {d : ℕ} {U : Set (Vec d)}
    (g : Mat d) (hg : matTranspose g = -g) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ U) (v : H1Function U) :
    ∫ x in U, vecDot (matVecMul g (euclideanGradient u x)) (v.grad x)
      ∂MeasureTheory.volume = 0 := by
  classical
  let ψ : Fin d → Vec d → ℝ := fun i x ↦
    ∑ j : Fin d, g i j * euclideanCoordDeriv j u x
  have hψ_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    intro i
    exact ContDiff.sum fun j _ ↦
      contDiff_const.mul (contDiff_euclideanCoordDeriv hu j)
  have hψ_compact : ∀ i, HasCompactSupport (ψ i) := by
    intro i
    exact hasCompactSupport_finset_sum Finset.univ _ fun j _ ↦
      (hasCompactSupport_euclideanCoordDeriv hu_supp j).mul_left
  have hψ_sub : ∀ i, tsupport (ψ i) ⊆ U := by
    intro i x hx
    by_contra hxU
    have hxT : x ∉ tsupport u := fun h ↦ hxU (hu_sub h)
    exact hxU <| hu_sub <| by
      apply closure_minimal _ isClosed_closure hx
      intro y hy
      contrapose! hy
      have hyT : y ∉ tsupport u := hy
      simp [ψ, euclideanCoordDeriv,
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hyT]
  have hweak : ∀ i, ∫ x in U, v.toFun x * euclideanCoordDeriv i (ψ i) x
        ∂MeasureTheory.volume = -∫ x in U, v.grad x i * ψ i x ∂MeasureTheory.volume := by
    intro i
    simpa [euclideanCoordDeriv] using
      v.hasWeakGradient i (ψ i) (hψ_smooth i) (hψ_compact i) (hψ_sub i)
  rw [show (fun x ↦ vecDot (matVecMul g (euclideanGradient u x)) (v.grad x)) =
      fun x ↦ ∑ i : Fin d, ψ i x * v.grad x i by
        funext x
        simp [vecDot, matVecMul, euclideanGradient, ψ]]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      ∑ i : Fin d, ∫ x in U, ψ i x * v.grad x i ∂MeasureTheory.volume =
          -∑ i : Fin d, ∫ x in U, v.toFun x * euclideanCoordDeriv i (ψ i) x
              ∂MeasureTheory.volume := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _
            have hw := hweak i
            have hcomm : (∫ x in U, ψ i x * v.grad x i ∂MeasureTheory.volume) =
                ∫ x in U, v.grad x i * ψ i x ∂MeasureTheory.volume := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with x
              ring
            rw [hcomm]
            linarith only [hw]
      _ = 0 := by
        suffices hpoint : (fun x ↦ ∑ i : Fin d, euclideanCoordDeriv i (ψ i) x) = 0 by
          rw [← MeasureTheory.integral_finsetSum]
          · rw [neg_eq_zero]
            apply MeasureTheory.integral_eq_zero_of_ae
            filter_upwards [] with x
            rw [← Finset.mul_sum, congrFun hpoint x]
            simp
          · intro i _
            have hd : MemScalarL2 U (fun x ↦ euclideanCoordDeriv i (ψ i) x) := by
              exact ((contDiff_euclideanCoordDeriv (hψ_smooth i) i).continuous
                |>.memLp_of_hasCompactSupport
                  (hasCompactSupport_euclideanCoordDeriv (hψ_compact i) i)).restrict U
            exact v.memL2.integrable_mul hd
        funext x
        have hderiv : ∀ i : Fin d, euclideanCoordDeriv i (ψ i) x =
            ∑ j : Fin d, g i j * euclideanCoordSecondDeriv j i u x := by
          intro i
          unfold euclideanCoordDeriv
          change (fderiv ℝ (fun y ↦ ∑ j : Fin d, g i j * euclideanCoordDeriv j u y) x)
              (basisVec i) = _
          rw [fderiv_fun_sum]
          · simp only [_root_.sum_apply]
            apply Finset.sum_congr rfl
            intro j _
            rw [fderiv_const_mul]
            · rfl
            · exact (contDiff_euclideanCoordDeriv hu j).differentiable (by simp) x
          · intro j _
            exact (contDiff_const.mul (contDiff_euclideanCoordDeriv hu j)).differentiable
              (by simp) x
        simp_rw [hderiv]
        let S : ℝ := ∑ i : Fin d, ∑ j : Fin d,
          g i j * euclideanCoordSecondDeriv j i u x
        change S = 0
        have hneg : S = -S := by
          calc
            S = ∑ j : Fin d, ∑ i : Fin d,
                g i j * euclideanCoordSecondDeriv j i u x := by
                  exact Finset.sum_comm
            _ = ∑ j : Fin d, ∑ i : Fin d,
                -(g j i * euclideanCoordSecondDeriv i j u x) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  apply Finset.sum_congr rfl
                  intro i _
                  have hc := euclideanCoordSecondDeriv_comm hu j i x
                  have hgij := congrArg (fun A : Mat d ↦ A j i) hg
                  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at hgij
                  rw [hc]
                  rw [hgij]
                  ring
            _ = -∑ j : Fin d, ∑ i : Fin d,
                g j i * euclideanCoordSecondDeriv i j u x := by
                  simp only [Finset.sum_neg_distrib]
            _ = -S := by
                  congr 1
        linarith only [hneg]
  · intro i _
    exact (memScalarL2_coord_of_memVectorL2
      (memVectorL2_const_matVecMul g
        (memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hu hu_supp)) i).integrable_mul
      (v.gradMemL2 i)

private theorem isSolenoidalZeroNormalTraceOn_const_skew_mul_potential
    {d : ℕ} {U : Set (Vec d)} (g : Mat d) (hg : matTranspose g = -g)
    {f : Vec d → Vec d} (hf : IsPotentialZeroTraceOn U f) :
    IsSolenoidalZeroNormalTraceOn U (fun x ↦ matVecMul g (f x)) := by
  classical
  rcases hf with ⟨u, rfl⟩
  intro v
  let D : ℕ → Fin d → Vec d → ℝ := fun n j x ↦
    euclideanCoordDeriv j (u.approx n) x
  have hDL2 : ∀ n j, MemScalarL2 U (D n j) := by
    intro n j
    exact memScalarL2_euclideanCoordDeriv U j
      (u.approx_smooth n) (u.approx_hasCompactSupport n)
  have hDconv : ∀ j,
      Filter.Tendsto (fun n ↦ toScalarL2 (hDL2 n j)) Filter.atTop
        (nhds (toScalarL2 (u.toH1Function.gradMemL2 j))) := by
    intro j
    apply tendsto_toScalarL2_of_tendsto_eLpNorm
    simpa [D, euclideanCoordDeriv] using u.tendsto_approx_grad j
  have hpair : ∀ i j,
      Filter.Tendsto
        (fun n ↦ ∫ x in U, v.grad x i * D n j x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, v.grad x i * u.toH1Function.grad x j
          ∂MeasureTheory.volume)) := by
    intro i j
    exact tendsto_integral_mul_of_tendsto_toScalarL2
      (v.gradMemL2 i) (fun n ↦ hDL2 n j) (u.toH1Function.gradMemL2 j) (hDconv j)
  have hsum :
      Filter.Tendsto
        (fun n ↦ ∑ i : Fin d, ∑ j : Fin d,
          g i j * (∫ x in U, v.grad x i * D n j x ∂MeasureTheory.volume))
        Filter.atTop
        (nhds (∑ i : Fin d, ∑ j : Fin d,
          g i j * (∫ x in U, v.grad x i * u.toH1Function.grad x j
            ∂MeasureTheory.volume))) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact (hpair i j).const_mul (g i j)
  have hseq : (fun n ↦ ∑ i : Fin d, ∑ j : Fin d,
      g i j * (∫ x in U, v.grad x i * D n j x ∂MeasureTheory.volume)) =
      fun _ : ℕ ↦ (0 : ℝ) := by
    funext n
    have hz := smooth_skew_gradient_pairing_zero g hg
      (u.approx_smooth n) (u.approx_hasCompactSupport n) (u.approx_support_subset n) v
    rw [show (∫ x in U,
        vecDot (matVecMul g (euclideanGradient (u.approx n) x)) (v.grad x)
          ∂MeasureTheory.volume) =
        ∑ i : Fin d, ∑ j : Fin d,
          g i j * (∫ x in U, v.grad x i * D n j x ∂MeasureTheory.volume) by
      rw [show (fun x ↦
          vecDot (matVecMul g (euclideanGradient (u.approx n) x)) (v.grad x)) =
          fun x ↦ ∑ i : Fin d, ∑ j : Fin d,
            g i j * (v.grad x i * D n j x) by
        funext x
        simp only [vecDot, matVecMul, euclideanGradient, D, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [MeasureTheory.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [MeasureTheory.integral_const_mul]
        · intro j _
          exact (v.gradMemL2 i).integrable_mul (hDL2 n j) |>.const_mul (g i j)
      · intro i _
        exact MeasureTheory.integrable_finsetSum Finset.univ fun j _ ↦
          (v.gradMemL2 i).integrable_mul (hDL2 n j) |>.const_mul (g i j)] at hz
    exact hz
  have hzero_tendsto : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop
      (nhds (∑ i : Fin d, ∑ j : Fin d,
        g i j * (∫ x in U, v.grad x i * u.toH1Function.grad x j
          ∂MeasureTheory.volume))) := by
    simpa [hseq] using hsum
  have hlimit : (∑ i : Fin d, ∑ j : Fin d,
      g i j * (∫ x in U, v.grad x i * u.toH1Function.grad x j
        ∂MeasureTheory.volume)) = 0 := by
    exact tendsto_nhds_unique hzero_tendsto tendsto_const_nhds
  rw [show (∫ x in U, vecDot (matVecMul g (u.toH1Function.grad x)) (v.grad x)
      ∂MeasureTheory.volume) =
      ∑ i : Fin d, ∑ j : Fin d,
        g i j * (∫ x in U, v.grad x i * u.toH1Function.grad x j
          ∂MeasureTheory.volume) by
    rw [show (fun x ↦ vecDot (matVecMul g (u.toH1Function.grad x)) (v.grad x)) =
        fun x ↦ ∑ i : Fin d, ∑ j : Fin d,
          g i j * (v.grad x i * u.toH1Function.grad x j) by
      funext x
      simp only [vecDot, matVecMul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [MeasureTheory.integral_const_mul]
      · intro j _
        exact (v.gradMemL2 i).integrable_mul (u.toH1Function.gradMemL2 j)
          |>.const_mul (g i j)
    · intro i _
      exact MeasureTheory.integrable_finsetSum Finset.univ fun j _ ↦
        (v.gradMemL2 i).integrable_mul (u.toH1Function.gradMemL2 j)
          |>.const_mul (g i j)]
  exact hlimit

/-- Keep the potential of a block state and add `g` times that potential to its flux. -/
@[expose]
public def shearStateFluxAdd {d : ℕ} (g : Mat d) (X : BlockState d) : BlockState d :=
  { potential := X.potential
    flux := fun x ↦ X.flux x + matVecMul g (X.potential x) }

/-- Shear a block load by keeping its first component and adding `g` times that component to the
second. -/
@[expose]
public def shearLoad {d : ℕ} (g : Mat d) (P : BlockVec d) : BlockVec d :=
  (P.1, P.2 + matVecMul g P.1)

private theorem matVecMul_vec_sub {d : ℕ} (g : Mat d) (p q : Vec d) :
    matVecMul g (p - q) = matVecMul g p - matVecMul g q := by
  ext i
  unfold matVecMul
  simp only [Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem matVecMul_matrix_sub {d : ℕ} (A g : Mat d) (p : Vec d) :
    matVecMul (A - g) p = matVecMul A p - matVecMul g p := by
  ext i
  unfold matVecMul
  simp only [Matrix.sub_apply, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

private theorem blockEnergyDensity_sub_skew_shear {d : ℕ}
    (a : CoeffField d) (g : Mat d) (hg : matTranspose g = -g)
    (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (fun y ↦ a y - g) X x =
      blockEnergyDensity a (shearStateFluxAdd g X) x := by
  have hs : symmPart (a x - g) = symmPart (a x) := by
    ext i j
    have hij := congrArg (fun A : Mat d ↦ A i j) hg
    simp [symmPart, matTranspose] at hij ⊢
    linarith only [hij]
  have hk : skewPart (a x - g) = skewPart (a x) - g := by
    ext i j
    have hij := congrArg (fun A : Mat d ↦ A i j) hg
    simp [skewPart, matTranspose] at hij ⊢
    linarith only [hij]
  unfold blockEnergyDensity
  simp only [blockCoeffField, BlockState.eval, shearStateFluxAdd]
  rw [blockMatrixOfCoeff_quadratic_eq, blockMatrixOfCoeff_quadratic_eq]
  simp only [hs, hk]
  have hv : X.flux x - matVecMul (skewPart (a x) - g) (X.potential x) =
      X.flux x + matVecMul g (X.potential x) -
        matVecMul (skewPart (a x)) (X.potential x) := by
    rw [matVecMul_matrix_sub]
    abel
  rw [hv]

private theorem isBlockMuAdmissible_shear {d : ℕ} {U : Set (Vec d)}
    (g : Mat d) (hg : matTranspose g = -g) {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (shearLoad g P) (shearStateFluxAdd g X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [shearStateFluxAdd, shearLoad] using hX.1
  · simpa [shearStateFluxAdd, shearLoad] using hX.2.1
  · have hgp := memVectorL2_const_matVecMul g hX.1
    have hadd := hX.2.2.1.add hgp
    convert hadd using 1
    funext x
    simp only [shearStateFluxAdd, shearLoad, Pi.add_apply]
    rw [matVecMul_vec_sub]
    abel
  · have hgp := isSolenoidalZeroNormalTraceOn_const_skew_mul_potential
      g hg hX.2.1
    have hgpL2 := memVectorL2_const_matVecMul g hX.1
    have hadd := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
      hX.2.2.1 hgpL2 hX.2.2.2 hgp
    convert hadd using 1
    funext x
    simp only [shearStateFluxAdd, shearLoad, Pi.add_apply]
    rw [matVecMul_vec_sub]
    abel

private theorem shearStateFluxAdd_neg_shearStateFluxAdd {d : ℕ} (g : Mat d) (X : BlockState d) :
    shearStateFluxAdd (-g) (shearStateFluxAdd g X) = X := by
  apply BlockState.ext
  · rfl
  · funext x
    simp only [shearStateFluxAdd]
    rw [neg_matVecMul]
    abel

private theorem shearLoad_neg_shearLoad {d : ℕ} (g : Mat d) (P : BlockVec d) :
    shearLoad (-g) (shearLoad g P) = P := by
  apply Prod.ext
  · rfl
  · simp only [shearLoad]
    rw [neg_matVecMul]
    abel

private theorem muValueSet_sub_skew_shearLoad {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (g : Mat d) (hg : matTranspose g = -g) (P : BlockVec d) :
    muValueSet U P (fun x ↦ a x - g) = muValueSet U (shearLoad g P) a := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨shearStateFluxAdd g X, isBlockMuAdmissible_shear g hg hX, ?_⟩
    congr 1
    funext x
    exact blockEnergyDensity_sub_skew_shear a g hg X x
  · rintro ⟨Y, hY, rfl⟩
    let X := shearStateFluxAdd (-g) Y
    have hng : matTranspose (-g) = -(-g) := by
      rw [show matTranspose (-g) = -(matTranspose g) by
        ext i j
        simp [matTranspose]]
      rw [hg]
    have hX' := isBlockMuAdmissible_shear (-g) hng hY
    have hload : shearLoad (-g) (shearLoad g P) = P :=
      shearLoad_neg_shearLoad g P
    have hX : IsBlockMuAdmissible U P X := by
      rw [← hload]
      exact hX'
    refine ⟨X, hX, ?_⟩
    rw [show volumeAverage U (blockEnergyDensity a Y) =
        volumeAverage U (blockEnergyDensity a (shearStateFluxAdd g X)) by
      rw [show shearStateFluxAdd g X = Y by
        dsimp [X]
        simpa using shearStateFluxAdd_neg_shearStateFluxAdd (-g) Y]]
    congr 1
    funext x
    exact (blockEnergyDensity_sub_skew_shear a g hg X x).symm

theorem Mu_sub_skew_shearLoad {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (g : Mat d) (hg : matTranspose g = -g) (P : BlockVec d) :
    Mu U P (fun x ↦ a x - g) = Mu U (shearLoad g P) a := by
  unfold Mu
  rw [muValueSet_sub_skew_shearLoad U a g hg P]

theorem blockVecDot_blockCongr {d : ℕ} (G A : BlockMat d) (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (Multiscale.blockCongr G A) P) =
      blockVecDot (blockMatVecMul G P) (blockMatVecMul A (blockMatVecMul G P)) := by
  have hL : blockVecDot P (blockMatVecMul (Multiscale.blockCongr G A) P) =
      dotProduct (toFullBlockVec P)
        (Matrix.mulVec ((toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G)
          (toFullBlockVec P)) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
    simp only [Multiscale.blockCongr, toFullBlockMat_ofFullBlockMat]
  have hR : blockVecDot (blockMatVecMul G P) (blockMatVecMul A (blockMatVecMul G P)) =
      dotProduct (Matrix.mulVec (toFullBlockMat G) (toFullBlockVec P))
        (Matrix.mulVec (toFullBlockMat A)
          (Matrix.mulVec (toFullBlockMat G) (toFullBlockVec P))) := by
    rw [← dotProduct_toFullBlockVec]
    simp only [toFullBlockVec_blockMatVecMul]
  rw [hL, hR, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem blockMatVecMul_shear_eq_shearLoad {d : ℕ} (g : Mat d) (P : BlockVec d) :
    blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P = shearLoad g P := by
  rcases P with ⟨p, q⟩
  apply Prod.ext
  · change matVecMul (1 : Mat d) p + matVecMul (0 : Mat d) q = p
    change Matrix.mulVec (1 : Mat d) p + Matrix.mulVec (0 : Mat d) q = p
    rw [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  · change matVecMul g p + matVecMul (1 : Mat d) q = q + matVecMul g p
    change Matrix.mulVec g p + Matrix.mulVec (1 : Mat d) q = q + Matrix.mulVec g p
    rw [Matrix.one_mulVec]
    abel

theorem isSymmetricBlockMat_blockCongr {d : ℕ} (G : BlockMat d)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (Multiscale.blockCongr G A) := by
  rw [Multiscale.blockCongr]
  refine isSymmetricBlockMat_of_isSymm ?_
  change ((toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G)ᵀ =
    (toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (isSymm_toFullBlockMat hA).eq, Matrix.mul_assoc]

theorem coarseBlockMatrix_sub_skew_eq_blockCongr {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {g : Mat d}
    (hg : matTranspose g = -g) (hquad : HasQuadraticMu U a) :
    coarseBlockMatrix U (fun x ↦ a x - g) =
      Multiscale.blockCongr ⟨1, 0, g, 1⟩ (coarseBlockMatrix U a) := by
  have hcoarse : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix (exists_coarseBlockMatrix_of_hasQuadraticMu hquad)
  have hnew : IsCoarseBlockMatrix U (fun x ↦ a x - g)
      (Multiscale.blockCongr ⟨1, 0, g, 1⟩ (coarseBlockMatrix U a)) := by
    refine ⟨isSymmetricBlockMat_blockCongr _ hcoarse.1, ?_⟩
    intro P
    rw [Mu_sub_skew_shearLoad U a g hg P,
      Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hquad,
      blockVecDot_blockCongr, blockMatVecMul_shear_eq_shearLoad]
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hnew).symm

/-! ## Helpers for the response-imbalance comparison

These `private` lemmas supply the monotonicity of the canonical imbalance, the determinant and
eigenvalue estimates for positive-definite matrices, and the block positive-definiteness
criterion used in `e.response.imbalance.comparison`.
-/

/-- With the two premises `ε ∈ (0, S.eps0]` and `σ ∈ (0, ε]` that the paper's Step 2 uses, the
raw output gives `j_* < s`, which is what `Annealed.adaptedMean_antitone` needs for `E_t ≤ E_s`.
Without them `S.one_le_B0` is unavailable, `B` may be negative and `raw.hs_lo` is vacuous. -/
theorem jStar_lt_s_of_raw (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (ε σ Cglob Cprof Csrc Bresp : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    (jStar : ℤ) < s := by
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hB : (1 : ℝ) ≤ B :=
    le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
  have hPi := HCPolySupport.HighContrast.Annealed.aspectRatio_pos_and_three_le raw.ell
  have h3 : (3 : ℝ) ≤ 2 + aspectRatio E := hPi.2
  have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    refine (Real.le_logb_iff_rpow_le (by norm_num) (by linarith only [h3])).mpr ?_
    rw [Real.rpow_one]; linarith only [h3]
  have hprod : (0 : ℝ) < B * Real.logb 3 (2 + aspectRatio E) := by
    exact mul_pos (lt_of_lt_of_le zero_lt_one hB)
      (lt_of_lt_of_le zero_lt_one hlog)
  have hceil : (0 : ℤ) < ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ := by
    exact Int.lt_ceil.mpr (by exact_mod_cast hprod)
  have hs := raw.hs_lo
  omega

/-- The canonical imbalance is monotone for the Loewner order: `A ≤ B` implies `𝔡(A) ≤ 𝔡(B)`.

This is the Lean content of the middle inequality `κ_t ≤ κ_s` of
`e.response.imbalance.comparison`: `𝔡(B) ≤ c` unpacks to
`B ≤ c·𝐑B⁻¹𝐑` (`le_of_imbalance_le`), inverse antitonicity turns `A ≤ B` into
`𝐑B⁻¹𝐑 ≤ 𝐑A⁻¹𝐑`, and `imbalance_le_of_le` packs `A ≤ c·𝐑A⁻¹𝐑` back up. -/
theorem canonicalImbalance_mono {d : ℕ} {A Bm : BlockMat d}
    (hAs : IsSymmetricBlockMat A) (hA : Book.Ch02.BlockPosDef A)
    (hBs : IsSymmetricBlockMat Bm) (hB : Book.Ch02.BlockPosDef Bm)
    (hAB : toFullBlockMat A ≤ toFullBlockMat Bm) :
    canonicalImbalance A ≤ canonicalImbalance Bm := by
  have hApos : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hAs hA
  have hBpos : (toFullBlockMat Bm).PosDef := posDef_toFullBlockMat hBs hB
  have hcnn : (0 : ℝ) ≤ canonicalImbalance Bm := by
    simp only [canonicalImbalance, blockOpNorm]
    exact norm_nonneg _
  have h1 := le_of_imbalance_le hBpos (le_refl (canonicalImbalance Bm))
  have hinv : (toFullBlockMat Bm)⁻¹ ≤ (toFullBlockMat A)⁻¹ :=
    inv_le_inv_of_le hApos hBpos hAB
  have hRt : (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (swap_hermitian d).eq
  have h5 : toFullBlockMat (blockSwap d) * (toFullBlockMat Bm)⁻¹ * toFullBlockMat (blockSwap d)
      ≤ toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d) := by
    have h := Analysis.matrix_congr_le hinv (toFullBlockMat (blockSwap d))
    rwa [hRt] at h
  have h6 := smul_le_smul_left (c := canonicalImbalance Bm) hcnn h5
  exact imbalance_le_of_le hApos hcnn (hAB.trans (h1.trans h6))

/-- `1 ≤ 𝔡(A)` whenever the primal-adjoint order `𝐑A⁻¹𝐑 ≤ A` holds
(`e.matrix.annealed.sharp.order`, quoted at `e.response.imbalance.comparison`).
This is the first inequality of `e.response.imbalance.comparison`. -/
theorem one_le_canonicalImbalance {d : ℕ} (hd : 2 ≤ d) {A : BlockMat d}
    (hAs : IsSymmetricBlockMat A) (hA : Book.Ch02.BlockPosDef A)
    (hswap : toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d)
      ≤ toFullBlockMat A) :
    1 ≤ canonicalImbalance A := by
  have hApos : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hAs hA
  have hGpos : (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
      toFullBlockMat (blockSwap d)).PosDef := by
    simpa only [toFullBlockMat_ofFullBlockMat] using Analysis.swapConj_posDef hApos
  have hcnn : (0 : ℝ) ≤ canonicalImbalance A := by
    simp only [canonicalImbalance, blockOpNorm]
    exact norm_nonneg _
  have h1 := le_of_imbalance_le hApos (le_refl (canonicalImbalance A))
  -- a nonzero test vector
  set v : BlockCoord d → ℝ := fun _ => 1 with hv
  have hvne : v ≠ 0 := by
    intro hz
    have := congrFun hz (Sum.inl ⟨0, by omega⟩)
    simp [hv] at this
  have hq0 := Matrix.PosDef.dotProduct_mulVec_pos hGpos hvne
  have hq : 0 < v ⬝ᵥ (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ *
      toFullBlockMat (blockSwap d)) *ᵥ v := by
    simpa only [star_trivial] using hq0
  have hlo := (Matrix.le_iff.mp hswap).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hlo
  have hhi := (Matrix.le_iff.mp h1).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul] at hhi
  nlinarith only [hq, hlo, hhi]

/-- `1 ≤ X.det` whenever `X` is positive-definite and `1 ≤ X` (Loewner order): every eigenvalue
of `X` is at least `1`, and `det X` is the product of the eigenvalues. -/
private theorem one_le_det_of_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : X.PosDef) (h1 : (1 : Matrix n n ℝ) ≤ X) :
    1 ≤ X.det := by
  have heig : ∀ i, 1 ≤ hX.isHermitian.eigenvalues i := by
    intro i
    apply (algebraMap_le_iff_le_spectrum (a := X) (r := (1 : ℝ)) (ha := hX.isHermitian)).mp
      (by simpa only [map_one] using h1)
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.mem_range_self i
  rw [hX.isHermitian.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  simpa only [Finset.prod_const_one] using
    (Finset.prod_le_prod₀ (fun _ _ => (show (0 : ℝ) ≤ 1 by norm_num)) (fun i _ => heig i))

/-- `X ≤ X.det • 1` whenever `X` is positive-definite and `1 ≤ X`: each eigenvalue of `X` is at
most the product of all of them once every eigenvalue is `≥ 1`. -/
theorem le_det_smul_one_of_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : X.PosDef) (h1 : (1 : Matrix n n ℝ) ≤ X) :
    X ≤ X.det • (1 : Matrix n n ℝ) := by
  have heig : ∀ i, 1 ≤ hX.isHermitian.eigenvalues i := by
    intro i
    apply (algebraMap_le_iff_le_spectrum (a := X) (r := (1 : ℝ)) (ha := hX.isHermitian)).mp
      (by simpa only [map_one] using h1)
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.mem_range_self i
  have hdet : X.det = ∏ i, hX.isHermitian.eigenvalues i := by
    rw [hX.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hle : ∀ x ∈ spectrum ℝ X, x ≤ X.det := by
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩
    rw [hdet]
    have herase : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, hX.isHermitian.eigenvalues j := by
      simpa only [Finset.prod_const_one] using
        Finset.prod_le_prod₀ (fun j _ => (show (0 : ℝ) ≤ 1 by norm_num))
          (fun j _ => heig j)
    have hmul := le_mul_of_one_le_right (le_trans zero_le_one (heig i)) herase
    rwa [Finset.mul_prod_erase Finset.univ hX.isHermitian.eigenvalues
      (Finset.mem_univ i)] at hmul
  have hfin := (le_algebraMap_iff_spectrum_le (a := X) (r := X.det) (ha := hX.isHermitian)).mpr hle
  rwa [Algebra.algebraMap_eq_smul_one] at hfin

/-- A doubled block whose flattening is positive definite is block positive definite.
The converse of `posDef_toFullBlockMat`, needed to feed `Annealed.adaptedMean_posDef` into the
imbalance helpers (`e.response.imbalance.comparison`). -/
theorem blockPosDef_of_full {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) : Book.Ch02.BlockPosDef A := by
  intro X hX
  have hfull_ne : toFullBlockVec X ≠ 0 := by
    intro hfull
    apply hX
    rw [← ofFullBlockVec_toFullBlockVec X, hfull]
    rfl
  have hq := hA.dotProduct_mulVec_pos hfull_ne
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X), toFullBlockVec_blockMatVecMul]
  simpa only [star_trivial] using hq

/-- The determinant-ratio comparison of `p.response.transfer`: for positive
definite `A ≤ B` one has `1 ≤ det B / det A` and `B ≤ (det B / det A) • A`.

This is the step "bounding each eigenvalue of `E_t^{-1/2} E_s E_t^{-1/2}` by their product"
(`e.response.imbalance.comparison`): congruating `A ≤ B` by `A^{-1/2}` produces
`X = A^{-1/2} B A^{-1/2}` with `1 ≤ X` and `det X = det B / det A`, and
`one_le_det_of_one_le` / `le_det_smul_one_of_one_le` apply to `X`. -/
theorem le_detRatio_smul_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {A Bm : Matrix n n ℝ} (hA : A.PosDef) (hB : Bm.PosDef) (hAB : A ≤ Bm) :
    1 ≤ Bm.det / A.det ∧ Bm ≤ (Bm.det / A.det) • A := by
  have hSpd : (matSqrt A⁻¹).PosDef := matSqrt_inv_posDef_full hA
  have hSt : (matSqrt A⁻¹)ᵀ = matSqrt A⁻¹ := transpose_eq_of_psd hSpd.posSemidef
  have hSA : matSqrt A⁻¹ * A * matSqrt A⁻¹ = 1 :=
    matSqrt_inv_conj hA
  have hSS : matSqrt A⁻¹ * matSqrt A⁻¹ = A⁻¹ := (matSqrt_spec hA.inv.posSemidef).2
  have hSu : IsUnit (matSqrt A⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hSpd.isUnit
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have h1 : (1 : Matrix n n ℝ) ≤ matSqrt A⁻¹ * Bm * matSqrt A⁻¹ := by
    have h := Analysis.matrix_congr_le hAB (matSqrt A⁻¹)
    rwa [hSt, hSA] at h
  have hXpsd : (matSqrt A⁻¹ * Bm * matSqrt A⁻¹).PosSemidef := by
    have h := hB.posSemidef.conjTranspose_mul_mul_same (matSqrt A⁻¹)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hSt] at h
  have hXpd : (matSqrt A⁻¹ * Bm * matSqrt A⁻¹).PosDef :=
    posDef_of_le Matrix.PosDef.one hXpsd.isHermitian h1
  have hdet : (matSqrt A⁻¹ * Bm * matSqrt A⁻¹).det = Bm.det / A.det :=
    det_normalized_eq_div Bm A hA
  refine ⟨by rw [← hdet]; exact one_le_det_of_one_le hXpd h1, ?_⟩
  have hbound := le_det_smul_one_of_one_le hXpd h1
  rw [hdet] at hbound
  have h := Analysis.matrix_congr_le hbound (matSqrt A⁻¹)⁻¹
  have hSit : ((matSqrt A⁻¹)⁻¹)ᵀ = (matSqrt A⁻¹)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSt]
  have hiS : (matSqrt A⁻¹)⁻¹ * matSqrt A⁻¹ = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSi : matSqrt A⁻¹ * (matSqrt A⁻¹)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSu
  have hii : (matSqrt A⁻¹)⁻¹ * (matSqrt A⁻¹)⁻¹ = A := by
    rw [← Matrix.mul_inv_rev, hSS, Matrix.nonsing_inv_nonsing_inv A hAu]
  have hleft : (matSqrt A⁻¹)⁻¹ * (matSqrt A⁻¹ * Bm * matSqrt A⁻¹) * (matSqrt A⁻¹)⁻¹ = Bm := by
    calc (matSqrt A⁻¹)⁻¹ * (matSqrt A⁻¹ * Bm * matSqrt A⁻¹) * (matSqrt A⁻¹)⁻¹
        = ((matSqrt A⁻¹)⁻¹ * matSqrt A⁻¹) * Bm * (matSqrt A⁻¹ * (matSqrt A⁻¹)⁻¹) := by
          simp only [mul_assoc]
      _ = Bm := by rw [hiS, hSi, one_mul, mul_one]
  rw [hSit] at h
  simpa only [hleft, Matrix.mul_smul, Matrix.smul_mul, mul_one, hii] using h

end HCPolySupport.HighContrast.Multiscale
end
