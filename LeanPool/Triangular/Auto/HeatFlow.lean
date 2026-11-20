/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import LeanPool.Triangular.Auto.Gaussian
public import LeanPool.Triangular.Auto.MatrixEnergy
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Discrete Gaussian heat flow and the initial energy bound

Derived from the corresponding part of the upstream triangular Hilbert form proof.

The initial Gaussian energy estimate adapts `TwoCommuting/Auto/Sec4GaussianEnergies.lean`.
Joris Roos’s `lean-twocommuting` revision `33b69ccacc013c703a151421658187ea4d2029fb`
credits these Apache-2.0 Lean proofs to Claude.
-/

@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open Matrix MeasureTheory Filter Topology Real

namespace Triangular.Auto

noncomputable section

section GramWeight

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The complex diagonal matrix formed from real diagonal entries. -/
def rdiag (f : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => ((f i : ℝ) : ℂ)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma rdiag_isHermitian (f : ι → ℝ) :
    (rdiag f).IsHermitian := by
  simp [rdiag, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]

omit [Fintype κ] [DecidableEq κ] [Fintype ι] in
lemma rdiag_posSemidef {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : (rdiag f).PosSemidef := by
  rw [rdiag, Matrix.posSemidef_diagonal_iff]
  intro i; exact_mod_cast hf i

/-- The Gram matrix of the columns of `B` with row weights `f`. -/
def wGram (B : Matrix ι κ ℂ) (f : ι → ℝ) : Matrix κ κ ℂ := Bᴴ * rdiag f * B

omit [DecidableEq κ] [Fintype κ] in
lemma wGram_posSemidef (B : Matrix ι κ ℂ) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (wGram B f).PosSemidef := by
  exact (rdiag_posSemidef hf).conjTranspose_mul_mul_same B

omit [DecidableEq κ] [Fintype κ] in
lemma wGram_isHermitian (B : Matrix ι κ ℂ) (f : ι → ℝ) : (wGram B f).IsHermitian := by
  rw [wGram, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (rdiag_isHermitian f).eq, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq κ] [Fintype κ] in
lemma wGram_apply (B : Matrix ι κ ℂ) (f : ι → ℝ) (a b : κ) :
    wGram B f a b = ∑ i, star (B i a) * (f i : ℂ) * B i b := by
  rw [wGram, Matrix.mul_apply]
  simp only [rdiag, Matrix.mul_diagonal, Matrix.conjTranspose_apply]

omit [DecidableEq κ] [Fintype κ] in
lemma hasDerivAt_wGram (B : Matrix ι κ ℂ) {f : ℝ → ι → ℝ} {f' : ι → ℝ} {θ₀ : ℝ}
    (hf : ∀ i, HasDerivAt (fun θ => f θ i) (f' i) θ₀) :
    ∀ a b, HasDerivAt (fun θ => wGram B (f θ) a b) (wGram B f' a b) θ₀ := by
  intro a b
  simp only [wGram_apply]
  refine HasDerivAt.fun_sum fun i _ => ?_
  exact ((hf i).ofReal_comp.const_mul _).mul_const _

omit [DecidableEq κ] [Fintype κ] in
lemma wGram_smul (B : Matrix ι κ ℂ) (c : ℝ) (f : ι → ℝ) :
    wGram B (c • f) = (c : ℂ) • wGram B f := by
  simp only [wGram, rdiag, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [show (diagonal fun i => (c : ℂ) * (f i : ℂ)) = (c : ℂ) • diagonal fun i => (f i : ℂ) by
    ext i j; by_cases h : i = j <;> simp [h]]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The Gaussian weights of grid points at center `p` and variance `σ`, scaled by `h`. -/
def gweight (u : ι → ℝ) (h σ p : ℝ) : ι → ℝ := fun i => h * gaussian σ (u i - p)

omit [Fintype ι] [DecidableEq ι] in
lemma gweight_nonneg (u : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) (σ p : ℝ) (i : ι) :
    0 ≤ gweight u h σ p i := by
  unfold gweight gaussian
  positivity

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_gweight_p (u : ι → ℝ) (h σ p : ℝ) (i : ι) :
    HasDerivAt (fun q => gweight u h σ q i) (-(h * gaussianD 1 σ (u i - p))) p := by
  have := ((hasDerivAt_gaussianD 0 σ (u i - p)).comp p ((hasDerivAt_id p).const_sub (u
      i))).const_mul h
  convert this using 1
  · funext q; simp [gweight, gaussianD_zero, Function.comp]
  · simp only [zero_add]; ring

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_gweightD1_p (u : ι → ℝ) (h σ p : ℝ) (i : ι) :
    HasDerivAt (fun q => -(h * gaussianD 1 σ (u i - q))) (h * gaussianD 2 σ (u i - p)) p := by
  have := (((hasDerivAt_gaussianD 1 σ (u i - p)).comp p ((hasDerivAt_id p).const_sub (u
      i))).const_mul h).neg
  convert this using 1
  · funext q; simp [Function.comp]
  · simp only [show (1 + 1 : ℕ) = 2 from rfl]; ring

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_gweight_σ (u : ι → ℝ) (h p : ℝ) {σ : ℝ} (hσ : 0 < σ) (i : ι) :
    HasDerivAt (fun τ => gweight u h τ p i) (h * gaussianD 2 σ (u i - p) / 2) σ := by
  have := (hasDerivAt_gaussianD_variance 0 hσ (u i - p)).const_mul h
  convert this using 1
  · funext τ; simp [gweight, gaussianD_zero]
  · simp only [zero_add]; ring

theorem gram_heat_identity (C : Matrix κ κ ℂ) (hC : C.PosSemidef) (B : Matrix ι κ ℂ) (u : ι → ℝ)
    {h η σ : ℝ} (hh : 0 ≤ h) (hη : 0 < η) (hσ : 0 < σ) (p : ℝ) :
    HasDerivAt (fun q => energyReg η (C + wGram B (gweight u h σ q))) ((3 / 2) * ((CFC.sqrt (C +
      wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p)))).trace).re) p ∧ HasDerivAt (fun q => (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ
      q) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i - q)))).trace).re) ((matCost
      (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) (wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p))))).toReal + (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B
      (fun i => h * gaussianD 2 σ (u i - p))).trace).re) p ∧ HasDerivAt (fun τ => energyReg η (C +
      wGram B (gweight u h τ p))) ((3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) •
      1) * wGram B (fun i => h * gaussianD 2 σ (u i - p) / 2)).trace).re) σ := by
  have hPSD : ∀ q τ, (C + wGram B (gweight u h τ q)).PosSemidef := fun q τ =>
    hC.add (wGram_posSemidef B fun i => gweight_nonneg u hh τ q i)
  have hdp : ∀ i j, HasDerivAt (fun q => (C + wGram B (gweight u h σ q)) i j) (wGram B (fun i => -(h
      * gaussianD 1 σ (u i - p))) i j) p := by
    intro i j
    have := (hasDerivAt_wGram B (f := fun q => gweight u h σ q) (fun k => hasDerivAt_gweight_p u h σ
        p k) i j).const_add (C i j)
    simpa using this
  have hdU : ∀ i j, HasDerivAt (fun q => wGram B (fun i => -(h * gaussianD 1 σ (u i - q))) i j)
      (wGram B (fun i => h * gaussianD 2 σ (u i - p)) i j) p :=
    hasDerivAt_wGram B (f := fun q i => -(h * gaussianD 1 σ (u i - q))) (fun k =>
        hasDerivAt_gweightD1_p u h σ p k)
  refine ⟨?_, ?_, ?_⟩
  · exact hasDerivAt_energyReg hη (fun q => hPSD q σ) hdp
  · have hH := hasDerivAt_energy_hessian hη (fun q => hPSD q σ) hdp hdU (wGram_isHermitian B _)
    rwa [matCostBil_self (posDef_add_smul_one (hPSD p σ) hη)] at hH
  · have hdσ : ∀ i j, HasDerivAt (fun τ => (C + wGram B (gweight u h (max τ (σ / 2)) p)) i j) (wGram
        B (fun i => h * gaussianD 2 σ (u i - p) / 2) i j) σ := by
      intro i j
      have hmax : HasDerivAt (fun τ => max τ (σ / 2)) 1 σ := by
        refine (hasDerivAt_id σ).congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds (by linarith : σ / 2 < σ)] with τ hτ
        simp [max_eq_left hτ.le]
      have hw : ∀ k, HasDerivAt (fun τ => gweight u h (max τ (σ / 2)) p k) (h * gaussianD 2 σ (u k -
          p) / 2) σ := by
        intro k
        have := (hasDerivAt_gweight_σ u h p (σ := max σ (σ / 2)) (by positivity) k).comp σ hmax
        simp only [max_eq_left (by linarith : σ / 2 ≤ σ), mul_one] at this
        exact this
      have := (hasDerivAt_wGram B (f := fun τ => gweight u h (max τ (σ / 2)) p) hw i j).const_add (C
          i j)
      simpa using this
    have hE := hasDerivAt_energyReg hη (fun τ => hPSD p (max τ (σ / 2))) hdσ
    simp only [max_eq_left (by linarith : σ / 2 ≤ σ)] at hE
    refine hE.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (by linarith : σ / 2 < σ)] with τ hτ
    simp [max_eq_left hτ.le]

end GramWeight

section HeatMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The grid and three edge matrices used in the discrete Gaussian heat flow. -/
structure HeatData (ι : Type*) where
  /-- The real coordinate of each grid index. -/
  u : ι → ℝ
  /-- The grid spacing. -/
  h : ℝ
  /-- The three input matrices, indexed by the cyclic edge. -/
  A : Fin 3 → Matrix ι ι ℂ

namespace HeatData

variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

/-- The Gaussian weight at a vertex for the specified centers and variances. -/
def w (v : Fin 3) : ι → ℝ := gweight Hd.u Hd.h (σ v) (p v)

/-- The pointwise square root of the Gaussian weight. -/
def sqw (v : Fin 3) : ι → ℝ := fun i => √(Hd.w p σ v i)

/-- The edge matrix weighted by the square roots at its two endpoints. -/
def W (v : Fin 3) : Matrix ι ι ℂ := rdiag (Hd.sqw p σ v) * Hd.A v * rdiag (Hd.sqw p σ (v + 1))

/-- The horizontal row matrix containing the two weighted edges incident at `v`. -/
def R (v : Fin 3) : Matrix ι (ι ⊕ ι) ℂ := rowMat (Hd.W p σ v) (Hd.W p σ (v - 1))

/-- The column Gram matrix of the weighted row at `v`. -/
def T (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (Hd.R p σ v)ᴴ * Hd.R p σ v

/-- The row Gram matrix of the weighted row at `v`. -/
def S (v : Fin 3) : Matrix ι ι ℂ := Hd.R p σ v * (Hd.R p σ v)ᴴ

/-- The regularized spectral energy of the column Gram matrix at vertex `v`. -/
def e (η : ℝ) (v : Fin 3) : ℝ := energyReg η (Hd.T p σ v)

/-- The block-diagonal square-root weights for the two neighbors of `v`. -/
def Dc (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (rdiag (Hd.sqw p σ (v + 1))) 0 0 (rdiag (Hd.sqw p σ (v - 1)))

/-- The row matrix weighted at the two neighbors and unweighted at the shared vertex. -/
def Brow (v : Fin 3) : Matrix ι (ι ⊕ ι) ℂ := rowMat (Hd.A v) (Hd.A (v - 1)) * Hd.Dc p σ v

/-- The adjoint forward edge weighted at the shared vertex `v`. -/
def Bnext (v : Fin 3) : Matrix ι ι ℂ := (Hd.A v)ᴴ * rdiag (Hd.sqw p σ v)

/-- The backward edge weighted at the shared vertex `v`. -/
def Bprev (v : Fin 3) : Matrix ι ι ℂ := Hd.A (v - 1) * rdiag (Hd.sqw p σ v)

lemma rdiag_mul_rdiag (f g : ι → ℝ) :
    rdiag f * rdiag g = rdiag (f * g) := by
  simp [rdiag, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] in
lemma rdiag_conjTranspose (f : ι → ℝ) : (rdiag f)ᴴ = rdiag f := (rdiag_isHermitian f).eq

omit [Fintype ι] [DecidableEq ι] in
lemma sq_mul_sq (hh : 0 ≤ Hd.h) {v : Fin 3} :
    Hd.sqw p σ v * Hd.sqw p σ v = Hd.w p σ v := by
  funext i
  simp only [sqw, Pi.mul_apply]
  exact Real.mul_self_sqrt (gweight_nonneg _ hh _ _ i)

lemma R_eq (v : Fin 3) :
    Hd.R p σ v = rdiag (Hd.sqw p σ v) * rowMat (Hd.A v) (Hd.A (v - 1)) * Hd.Dc p σ v := by
  have hv : v - 1 + 1 = v := by abel
  simp only [R, W, rowMat, Dc, hv, Matrix.conjTranspose_mul, rdiag_conjTranspose]
  rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  simp [Matrix.mul_assoc]

lemma T_eq_wGram (hh : 0 ≤ Hd.h) {v : Fin 3} :
    Hd.T p σ v = wGram (Hd.Brow p σ v) (Hd.w p σ v) := by
  rw [T, R_eq, wGram, Brow, ← sq_mul_sq Hd p σ hh, ← rdiag_mul_rdiag]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]

lemma S_eq_wGram (hh : 0 ≤ Hd.h) {v : Fin 3} :
    Hd.S p σ v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram (Hd.Bprev p σ v) (Hd.w p σ (v
      - 1)) := by
  set D := rdiag (Hd.sqw p σ v)
  set A' := rowMat (Hd.A v) (Hd.A (v - 1))
  have hDc : Hd.Dc p σ v * (Hd.Dc p σ v)ᴴ =
      Matrix.fromBlocks (rdiag (Hd.w p σ (v + 1))) 0 0 (rdiag (Hd.w p σ (v - 1))) := by
    rw [Dc, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [rdiag_conjTranspose, rdiag_mul_rdiag, sq_mul_sq Hd p σ hh]
  have hA : ∀ X Y : Matrix ι ι ℂ, A' * Matrix.fromBlocks X 0 0 Y * A'ᴴ =
      Hd.A v * X * (Hd.A v)ᴴ + (Hd.A (v - 1))ᴴ * Y * Hd.A (v - 1) := by
    intro X Y
    simp only [A', rowMat]
    rw [show Matrix.fromCols (Hd.A v) (Hd.A (v - 1))ᴴ * Matrix.fromBlocks X 0 0 Y =
      Matrix.fromCols (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) from
        Matrix.fromCols_mul_fromBlocks _ _ _ _ _ _]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [show Matrix.fromCols (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) *
        Matrix.fromRows (Hd.A v)ᴴ (Hd.A (v - 1)) = (Hd.A v * X + (Hd.A (v - 1))ᴴ * 0) * (Hd.A v)ᴴ +
        (Hd.A v * 0 + (Hd.A (v - 1))ᴴ * Y) * Hd.A (v - 1) from
        Matrix.fromCols_mul_fromRows _ _ _ _]
    simp
  have hS : Hd.S p σ v = D * (A' * (Hd.Dc p σ v * (Hd.Dc p σ v)ᴴ) * A'ᴴ) * D := by
    rw [S, R_eq]
    simp only [D, A', Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]
  rw [hS, hDc, hA]
  simp only [wGram, Bnext, Bprev, Matrix.conjTranspose_mul, rdiag_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, D]

lemma e_eq_S (η : ℝ) (v : Fin 3) : Hd.e p σ η v = energyReg η (Hd.S p σ v) := by
  rw [e, T, S]
  exact energyReg_conjTranspose_mul_self_eq η (Hd.R p σ v)

/-- The first derivative of the vertex weight with respect to its center. -/
def dw (v : Fin 3) : ι → ℝ := fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - p v))

/-- The second derivative of the vertex weight with respect to its center. -/
def ddw (v : Fin 3) : ι → ℝ := fun i => Hd.h * gaussianD 2 (σ v) (Hd.u i - p v)

omit [Fintype ι] [DecidableEq ι] in
lemma dw_def (v : Fin 3) : Hd.dw p σ v = fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - p v)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma ddw_def (v : Fin 3) : Hd.ddw p σ v = fun i => Hd.h * gaussianD 2 (σ v) (Hd.u i - p v) := rfl

/-- The center derivative of the column Gram matrix. -/
def Ui (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (Hd.Brow p σ v) (Hd.dw p σ v)

/-- The derivative of the row Gram matrix from varying the next center. -/
def Pnext (v : Fin 3) : Matrix ι ι ℂ := wGram (Hd.Bnext p σ v) (Hd.dw p σ (v + 1))

/-- The derivative of the row Gram matrix from varying the previous center. -/
def Pprev (v : Fin 3) : Matrix ι ι ℂ := wGram (Hd.Bprev p σ v) (Hd.dw p σ (v - 1))

/-- The regularized matrix cost of the center derivative of the column Gram matrix. -/
def V (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.T p σ v + (η : ℂ) • 1) (Hd.Ui p σ v)).toReal

/-- The regularized matrix cost contributed by the next center. -/
def Ynext (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal

/-- The regularized matrix cost contributed by the previous center. -/
def Yprev (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal

/-- The polarized cost pairing the derivatives from the two neighboring centers. -/
def Z (η : ℝ) (v : Fin 3) : ℝ :=
  matCostBil (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v) (Hd.Pprev p σ v)

lemma fin3_ne_succ (v : Fin 3) : v ≠ v + 1 := by fin_cases v <;> decide

lemma fin3_ne_pred (v : Fin 3) : v ≠ v - 1 := by fin_cases v <;> decide

lemma fin3_succ_ne_pred (v : Fin 3) : v + 1 ≠ v - 1 := by fin_cases v <;> decide

omit [Fintype ι] [DecidableEq ι] in
lemma w_update_ne {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.w (Function.update p v q) σ k = Hd.w p σ k := by
  simp [w, Function.update_of_ne hk]

omit [Fintype ι] [DecidableEq ι] in
lemma w_update_ne_σ {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) k = Hd.w p σ k := by
  simp [w, Function.update_of_ne hk]

omit [Fintype ι] [DecidableEq ι] in
lemma w_update_self (v : Fin 3) (q : ℝ) :
    Hd.w (Function.update p v q) σ v = gweight Hd.u Hd.h (σ v) q := by
  simp [w]

omit [Fintype ι] [DecidableEq ι] in
lemma w_update_self_σ (v : Fin 3) (τ : ℝ) :
    Hd.w p (Function.update σ v τ) v = gweight Hd.u Hd.h τ (p v) := by
  simp [w]

omit [Fintype ι] [DecidableEq ι] in
lemma sq_update_ne {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.sqw (Function.update p v q) σ k = Hd.sqw p σ k := by
  unfold HeatData.sqw; rw [w_update_ne Hd p σ hk]

omit [Fintype ι] [DecidableEq ι] in
lemma sq_update_ne_σ {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.sqw p (Function.update σ v τ) k = Hd.sqw p σ k := by
  unfold HeatData.sqw; rw [w_update_ne_σ Hd p σ hk]

lemma Brow_update (v : Fin 3) (q : ℝ) : Hd.Brow (Function.update p v q) σ v = Hd.Brow p σ v := by
  simp [Brow, Dc, sq_update_ne Hd p σ (fin3_ne_succ v).symm,
    sq_update_ne Hd p σ (fin3_ne_pred v).symm]

lemma Brow_update_σ (v : Fin 3) (τ : ℝ) : Hd.Brow p (Function.update σ v τ) v = Hd.Brow p σ v := by
  simp [Brow, Dc, sq_update_ne_σ Hd p σ (fin3_ne_succ v).symm,
    sq_update_ne_σ Hd p σ (fin3_ne_pred v).symm]

lemma Bnext_update {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.Bnext (Function.update p k q) σ v = Hd.Bnext p σ v := by
  simp [Bnext, sq_update_ne Hd p σ hk.symm]

lemma Bnext_update_σ {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.Bnext p (Function.update σ k τ) v = Hd.Bnext p σ v := by
  simp [Bnext, sq_update_ne_σ Hd p σ hk.symm]

lemma Bprev_update {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.Bprev (Function.update p k q) σ v = Hd.Bprev p σ v := by
  simp [Bprev, sq_update_ne Hd p σ hk.symm]

lemma Bprev_update_σ {v k : Fin 3} (hk : k ≠ v) (τ : ℝ) :
    Hd.Bprev p (Function.update σ k τ) v = Hd.Bprev p σ v := by
  simp [Bprev, sq_update_ne_σ Hd p σ hk.symm]

lemma T_update (hh : 0 ≤ Hd.h) (v : Fin 3) (q : ℝ) :
    Hd.T (Function.update p v q) σ v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) q) := by
  rw [T_eq_wGram Hd _ σ hh, Brow_update, w_update_self, zero_add]

lemma T_update_σ (hh : 0 ≤ Hd.h) {v : Fin 3} {τ : ℝ} :
    Hd.T p (Function.update σ v τ) v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h τ (p v)) := by
  rw [T_eq_wGram Hd p _ hh, Brow_update_σ, w_update_self_σ, zero_add]

lemma S_update_next (hh : 0 ≤ Hd.h) (v : Fin 3) (q : ℝ) :
    Hd.S (Function.update p (v + 1) q) σ v = wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1)) + wGram
      (Hd.Bnext p σ v) (gweight Hd.u Hd.h (σ (v + 1)) q) := by
  rw [S_eq_wGram Hd _ σ hh, Bnext_update Hd p σ (fin3_ne_succ v).symm,
    Bprev_update Hd p σ (fin3_ne_succ v).symm, w_update_self,
    w_update_ne Hd p σ (fin3_succ_ne_pred v).symm, add_comm]

lemma S_update_next_σ (hh : 0 ≤ Hd.h) (v : Fin 3) {τ : ℝ} :
    Hd.S p (Function.update σ (v + 1) τ) v = wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1)) + wGram
      (Hd.Bnext p σ v) (gweight Hd.u Hd.h τ (p (v + 1))) := by
  rw [S_eq_wGram Hd p _ hh,
    Bnext_update_σ Hd p σ (fin3_ne_succ v).symm,
    Bprev_update_σ Hd p σ (fin3_ne_succ v).symm, w_update_self_σ,
    w_update_ne_σ Hd p σ (fin3_succ_ne_pred v).symm, add_comm]

lemma S_update_prev (hh : 0 ≤ Hd.h) (v : Fin 3) (q : ℝ) :
    Hd.S (Function.update p (v - 1) q) σ v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram
      (Hd.Bprev p σ v) (gweight Hd.u Hd.h (σ (v - 1)) q) := by
  rw [S_eq_wGram Hd _ σ hh, Bnext_update Hd p σ (fin3_ne_pred v).symm,
    Bprev_update Hd p σ (fin3_ne_pred v).symm, w_update_self,
    w_update_ne Hd p σ (fin3_succ_ne_pred v)]

lemma S_update_prev_σ (hh : 0 ≤ Hd.h) (v : Fin 3) {τ : ℝ} :
    Hd.S p (Function.update σ (v - 1) τ) v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram
      (Hd.Bprev p σ v) (gweight Hd.u Hd.h τ (p (v - 1))) := by
  rw [S_eq_wGram Hd p _ hh,
    Bnext_update_σ Hd p σ (fin3_ne_pred v).symm,
    Bprev_update_σ Hd p σ (fin3_ne_pred v).symm, w_update_self_σ,
    w_update_ne_σ Hd p σ (fin3_succ_ne_pred v)]

/-- The trace expression for the first variation of the regularized spectral energy. -/
def tr32 (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K : Matrix κ κ ℂ) :
    ℝ := (3 / 2) * ((CFC.sqrt (Γ + (η : ℂ) • 1) * K).trace).re

private theorem gram_heat_of_updates {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ ℂ) (hC : C.PosSemidef) (B : Matrix ι κ ℂ) (u : ι → ℝ)
    {h η σ p : ℝ} (hh : 0 ≤ h) (hη : 0 < η) (hσ : 0 < σ)
    (center centerDerivative variance : ℝ → Matrix κ κ ℂ)
    (hcenter : ∀ q, center q = C + wGram B (gweight u h σ q))
    (hderivative : ∀ q, centerDerivative q =
      wGram B (fun i => -(h * gaussianD 1 σ (u i - q))))
    (hvariance : ∀ τ, variance τ = C + wGram B (gweight u h τ p)) :
    HasDerivAt (fun q => energyReg η (center q)) (tr32 η (center p) (centerDerivative p)) p ∧
      HasDerivAt (fun q => tr32 η (center q) (centerDerivative q))
        ((matCost (center p + (η : ℂ) • 1) (centerDerivative p)).toReal +
          tr32 η (center p) (wGram B (fun i => h * gaussianD 2 σ (u i - p)))) p ∧
      HasDerivAt (fun τ => energyReg η (variance τ))
        (tr32 η (center p) (wGram B (fun i => h * gaussianD 2 σ (u i - p) / 2))) σ := by
  simpa only [hcenter, hderivative, hvariance, tr32] using
    gram_heat_identity C hC B u hh hη hσ p

theorem e_heat_row (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p v q) σ η v) (tr32 η (Hd.T p σ v) (Hd.Ui p σ v))
      (p v) ∧ HasDerivAt (fun q => tr32 η (Hd.T (Function.update p v q) σ v) (Hd.Ui
      (Function.update p v q) σ v)) (Hd.V p σ η v + tr32 η (Hd.T p σ v) (wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v))) (p v) ∧ HasDerivAt (fun τ => Hd.e p (Function.update σ v τ) η v) (tr32 η
      (Hd.T p σ v) (wGram (Hd.Brow p σ v) (fun i => Hd.ddw p σ v i / 2))) (σ v) := by
  have hP (q : ℝ) : Hd.Ui (Function.update p v q) σ v =
      wGram (Hd.Brow p σ v) (fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - q))) := by
    rw [Ui, Brow_update, dw_def]
    simp
  have derivatives := gram_heat_of_updates 0 Matrix.PosSemidef.zero (Hd.Brow p σ v) Hd.u
    hh hη (hσ v)
    (fun q => Hd.T (Function.update p v q) σ v)
    (fun q => Hd.Ui (Function.update p v q) σ v)
    (fun τ => Hd.T p (Function.update σ v τ) v)
    (T_update Hd p σ hh v) hP (fun _ => T_update_σ Hd p σ hh)
  simpa only [Function.update_eq_self, e, V, ddw_def] using derivatives

lemma S_psd (hh : 0 ≤ Hd.h) (v : Fin 3) (k : Fin 3) :
    (wGram (Hd.Bprev p σ v) (Hd.w p σ k)).PosSemidef ∧ (wGram (Hd.Bnext p σ v) (Hd.w p σ
      k)).PosSemidef :=
  ⟨wGram_posSemidef _ fun i => gweight_nonneg _ hh _ _ i,
    wGram_posSemidef _ fun i => gweight_nonneg _ hh _ _ i⟩

theorem e_heat_next (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p (v + 1) q) σ η v) (tr32 η (Hd.S p σ v)
      (Hd.Pnext p σ v)) (p (v + 1)) ∧ HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v + 1)
      q) σ v) (Hd.Pnext (Function.update p (v + 1) q) σ v)) (Hd.Ynext p σ η v + tr32 η (Hd.S p σ
      v) (wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)))) (p (v + 1)) ∧ HasDerivAt (fun τ => Hd.e p
      (Function.update σ (v + 1) τ) η v) (tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (fun i =>
      Hd.ddw p σ (v + 1) i / 2))) (σ (v + 1)) := by
  have hP (q : ℝ) : Hd.Pnext (Function.update p (v + 1) q) σ v =
      wGram (Hd.Bnext p σ v) (fun i => -(Hd.h * gaussianD 1 (σ (v + 1)) (Hd.u i - q))) := by
    rw [Pnext, Bnext_update Hd p σ (fin3_ne_succ v).symm, dw_def]
    simp
  have derivatives := gram_heat_of_updates _ (S_psd Hd p σ hh v (v - 1)).1 (Hd.Bnext p σ v) Hd.u
    hh hη (hσ (v + 1))
    (fun q => Hd.S (Function.update p (v + 1) q) σ v)
    (fun q => Hd.Pnext (Function.update p (v + 1) q) σ v)
    (fun τ => Hd.S p (Function.update σ (v + 1) τ) v)
    (S_update_next Hd p σ hh v) hP (fun _ => S_update_next_σ Hd p σ hh v)
  simpa only [Function.update_eq_self, e_eq_S, Ynext, ddw_def] using derivatives

theorem e_heat_prev (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p (v - 1) q) σ η v) (tr32 η (Hd.S p σ v)
      (Hd.Pprev p σ v)) (p (v - 1)) ∧ HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v - 1)
      q) σ v) (Hd.Pprev (Function.update p (v - 1) q) σ v)) (Hd.Yprev p σ η v + tr32 η (Hd.S p σ
      v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))) (p (v - 1)) ∧ HasDerivAt (fun τ => Hd.e p
      (Function.update σ (v - 1) τ) η v) (tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (fun i =>
      Hd.ddw p σ (v - 1) i / 2))) (σ (v - 1)) := by
  have hP (q : ℝ) : Hd.Pprev (Function.update p (v - 1) q) σ v =
      wGram (Hd.Bprev p σ v) (fun i => -(Hd.h * gaussianD 1 (σ (v - 1)) (Hd.u i - q))) := by
    rw [Pprev, Bprev_update Hd p σ (fin3_ne_pred v).symm, dw_def]
    simp
  have derivatives := gram_heat_of_updates _ (S_psd Hd p σ hh v (v + 1)).2 (Hd.Bprev p σ v) Hd.u
    hh hη (hσ (v - 1))
    (fun q => Hd.S (Function.update p (v - 1) q) σ v)
    (fun q => Hd.Pprev (Function.update p (v - 1) q) σ v)
    (fun τ => Hd.S p (Function.update σ (v - 1) τ) v)
    (S_update_prev Hd p σ hh v) hP (fun _ => S_update_prev_σ Hd p σ hh v)
  simpa only [Function.update_eq_self, e_eq_S, Yprev, ddw_def] using derivatives

theorem e_mixed (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v + 1) q) σ v) (Hd.Pprev
      (Function.update p (v + 1) q) σ v)) (Hd.Z p σ η v) (p (v + 1)) := by
  set C := wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1))
  set B := Hd.Bnext p σ v
  have hC := (S_psd Hd p σ hh v (v - 1)).1
  have hPd : ∀ i j, HasDerivAt (fun q => (C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) q)) i j) (wGram
      B (Hd.dw p σ (v + 1)) i j) (p (v + 1)) := by
    intro i j
    have := (hasDerivAt_wGram B (f := fun q => gweight Hd.u Hd.h (σ (v + 1)) q) (fun k =>
        hasDerivAt_gweight_p Hd.u Hd.h (σ (v + 1)) (p (v + 1)) k) i j).const_add (C i j)
    simpa [dw_def] using this
  have hPpsd : ∀ q, (C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) q)).PosSemidef := fun q =>
    hC.add (wGram_posSemidef B fun i => gweight_nonneg _ hh _ q i)
  have hPprev : ∀ q, Hd.Pprev (Function.update p (v + 1) q) σ v = Hd.Pprev p σ v := by
    intro q
    rw [Pprev, Pprev, Bprev_update Hd p σ (fin3_ne_succ v).symm, dw_def, dw_def,
      Function.update_of_ne (fin3_succ_ne_pred v).symm]
  have hH := hasDerivAt_energy_hessian (G := fun _ => Hd.Pprev p σ v) (G' := 0) hη hPpsd hPd (fun i
      j => hasDerivAt_const _ _) (wGram_isHermitian _ _)
  have hS0 : Hd.S p σ v = C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) (p (v + 1))) := by
    have := S_update_next Hd p σ hh v (p (v + 1))
    rwa [Function.update_eq_self] at this
  have e1 : (fun q => tr32 η (Hd.S (Function.update p (v + 1) q) σ v) (Hd.Pprev (Function.update p
      (v + 1) q) σ v)) = fun q => (3 / 2) * ((CFC.sqrt (C + wGram B (gweight Hd.u Hd.h (σ (v + 1))
      q) + (η : ℂ) • 1) *
          Hd.Pprev p σ v).trace).re := by
    funext q; rw [tr32, S_update_next Hd p σ hh, hPprev]
  rw [e1]
  refine hH.congr_deriv ?_
  simp [Z, hS0, Pnext, B]

end HeatData

end HeatMatrices

section BlockCost

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix embedding into the first summand of the block row's index type. -/
def ein1 : Matrix (ι ⊕ ι) ι ℂ := Matrix.fromRows 1 0

/-- The matrix embedding into the second summand of the block row's index type. -/
def ein2 : Matrix (ι ⊕ ι) ι ℂ := Matrix.fromRows 0 1

lemma fromBlocks_diag_eq (X Y : Matrix ι ι ℂ) :
    Matrix.fromBlocks X 0 0 Y = (ein1 : Matrix (ι ⊕ ι) ι ℂ) * X * (ein1 : Matrix (ι ⊕ ι) ι ℂ)ᴴ +
      (ein2 : Matrix (ι ⊕ ι) ι ℂ) * Y * (ein2 : Matrix (ι ⊕ ι) ι ℂ)ᴴ := by
  ext (a | a) (b | b) <;>
    simp [ein1, ein2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]

omit [DecidableEq ι] [Fintype ι] in
lemma fromBlocks_diag_posSemidef [Finite ι] {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) :
    (Matrix.fromBlocks X 0 0 Y).PosSemidef := by
  classical
  let := Fintype.ofFinite ι
  rw [fromBlocks_diag_eq]
  exact (hX.mul_mul_conjTranspose_same _).add (hY.mul_mul_conjTranspose_same _)

omit [DecidableEq ι] in
lemma sqrt_fromBlocks_diag {ι : Type*} [Fintype ι] {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) :
    open scoped Classical in CFC.sqrt (Matrix.fromBlocks P 0 0 Q) = Matrix.fromBlocks (CFC.sqrt
      P) 0 0 (CFC.sqrt Q) := by
  classical
  have hsP : (CFC.sqrt P).PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hsQ : (CFC.sqrt Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hnn : 0 ≤ Matrix.fromBlocks (CFC.sqrt P) 0 0 (CFC.sqrt Q) := (fromBlocks_diag_posSemidef hsP
      hsQ).nonneg
  refine CFC.sqrt_unique ?_ hnn
  rw [Matrix.fromBlocks_multiply]
  simp [CFC.sqrt_mul_sqrt_self P hP.nonneg, CFC.sqrt_mul_sqrt_self Q hQ.nonneg]

omit [DecidableEq ι] in
lemma trace_fromBlocks' (a b c d : Matrix ι ι ℂ) :
    (Matrix.fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

omit [DecidableEq ι] in
lemma costInt_fromBlocks_diag (A1 A2 K11 K12 K21 K22 X1 X2 : Matrix ι ι ℂ) :
    costInt (Matrix.fromBlocks A1 0 0 A2) (Matrix.fromBlocks K11 K12 K21 K22) (Matrix.fromBlocks
      X1 0 0 X2) = costInt A1 K11 X1 + costInt A2 K22 X2 := by
  classical
  simp only [costInt, hsRe, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    trace_fromBlocks']
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.conjTranspose_zero,
    Complex.add_re]
  ring

theorem matCost_fromBlocks_ge {P1 P2 : Matrix ι ι ℂ} (hP1 : P1.PosSemidef) (hP2 : P2.PosSemidef)
    (K11 K12 K21 K22 : Matrix ι ι ℂ) :
    matCost P1 K11 + matCost P2 K22 ≤ matCost (Matrix.fromBlocks P1 0 0 P2) (Matrix.fromBlocks
      K11 K12 K21 K22) := by
  rw [matCost, matCost]
  refine ENNReal.iSup_add_iSup_le fun X1 X2 => ?_
  rw [matCost, sqrt_fromBlocks_diag hP1 hP2]
  set c1 := costInt (CFC.sqrt P1) K11 X1
  set c2 := costInt (CFC.sqrt P2) K22 X2
  have h0 : ∀ A K : Matrix ι ι ℂ, costInt A K 0 = 0 := fun A K => by simp [costInt, hsRe]
  let Y1 : Matrix ι ι ℂ := if 0 ≤ c1 then X1 else 0
  let Y2 : Matrix ι ι ℂ := if 0 ≤ c2 then X2 else 0
  have e1 : costInt (CFC.sqrt P1) K11 Y1 = max c1 0 := by
    by_cases h : 0 ≤ c1
    · simp only [Y1, h, ite_true, max_eq_left h]; rfl
    · simp [Y1, h, h0, max_eq_right (le_of_not_ge h)]
  have e2 : costInt (CFC.sqrt P2) K22 Y2 = max c2 0 := by
    by_cases h : 0 ≤ c2
    · simp only [Y2, h, ite_true, max_eq_left h]; rfl
    · simp [Y2, h, h0, max_eq_right (le_of_not_ge h)]
  refine le_trans ?_ (le_iSup _ (Matrix.fromBlocks Y1 0 0 Y2))
  rw [costInt_fromBlocks_diag, e1, e2, mul_add,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _

end BlockCost

section Neighbor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma w_pos (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) (i : ι) : 0 < Hd.w p σ v i := by
  simp only [w, gweight, gaussian]
  have : 0 < √(2 * π * σ v) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- The diagonal matrix of logarithmic derivatives of the vertex weights. -/
def N (v : Fin 3) : Matrix ι ι ℂ := rdiag (fun i => Hd.dw p σ v i / Hd.w p σ v i)

lemma sqw_N_sqw (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    rdiag (Hd.sqw p σ v) * Hd.N p σ v * rdiag (Hd.sqw p σ v) = rdiag (Hd.dw p σ v) := by
  rw [N, rdiag_mul_rdiag, rdiag_mul_rdiag]
  congr 1
  funext i
  have hw := Hd.w_pos p σ hh hσ i
  have hs : Hd.sqw p σ v i * Hd.sqw p σ v i = Hd.w p σ v i := Real.mul_self_sqrt hw.le
  simp only [Pi.mul_apply]
  rw [mul_comm (Hd.sqw p σ v i * _), ← mul_assoc, hs]
  field_simp

lemma Ui_eq (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.Ui p σ v = (Hd.R p σ v)ᴴ * Hd.N p σ v * Hd.R p σ v := by
  rw [R_eq, Ui, wGram, Brow, ← Hd.sqw_N_sqw p σ hh hσ]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]

lemma Pprev_succ_eq (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.Pprev p σ (v + 1) = (Hd.W p σ v)ᴴ * Hd.N p σ v * Hd.W p σ v := by
  have hv : v + 1 - 1 = v := by abel
  rw [Pprev, Bprev, hv, wGram, W, ← Hd.sqw_N_sqw p σ hh hσ]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]

lemma Pnext_pred_eq (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.Pnext p σ (v - 1) = Hd.W p σ (v - 1) * Hd.N p σ v * (Hd.W p σ (v - 1))ᴴ := by
  have hv : v - 1 + 1 = v := by abel
  rw [Pnext, Bnext, hv, wGram, W, hv, ← Hd.sqw_N_sqw p σ hh hσ]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma S_eq_sum (v : Fin 3) :
    Hd.S p σ v = Hd.W p σ v * (Hd.W p σ v)ᴴ + (Hd.W p σ (v - 1))ᴴ * Hd.W p σ (v - 1) := by
  rw [S, R, rowMat, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_conjTranspose]

end HeatData

omit [Fintype ι] [DecidableEq ι] in
lemma fromBlocks_sub' (a b c d a' b' c' d' : Matrix ι ι ℂ) :
    Matrix.fromBlocks a b c d - Matrix.fromBlocks a' b' c' d' = Matrix.fromBlocks (a - a') (b -
      b') (c - c') (d - d') := by
  simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]

lemma two_blocks_sub_gram_posSemidef (A V : Matrix ι ι ℂ) {η : ℝ} (hη : 0 ≤ η) :
    (((2 : ℝ) : ℂ) • Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (V * Vᴴ + (η : ℂ) • 1) -
      ((rowMat A V)ᴴ * rowMat A V + (η : ℂ) • 1)).PosSemidef := by
  have heq : ((2 : ℝ) : ℂ) • Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (V * Vᴴ + (η : ℂ) • 1) -
      ((rowMat A V)ᴴ * rowMat A V + (η : ℂ) • 1) = (rowMat A (-V))ᴴ * rowMat A (-V) + (η : ℂ) • 1 :=
      by
    rw [rowMat_gram, rowMat_gram, ← Matrix.fromBlocks_one]
    simp only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, fromBlocks_sub']
    congr 1 <;>
      simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_zero,
        add_zero, zero_sub, Complex.ofReal_ofNat] <;> module
  rw [heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add (Matrix.PosSemidef.one.smul (by
      exact_mod_cast hη))

namespace HeatData

variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

theorem neighbor_cost_comparison (hh : 0 < Hd.h) {w : Fin 3} (hσ : 0 < σ w) {η : ℝ} (hη : 0 < η) :
    Hd.Yprev p σ η (w + 1) + Hd.Ynext p σ η (w - 1) ≤ √2 * Hd.V p σ η w := by
  set A := Hd.W p σ w
  set B := Hd.W p σ (w - 1)
  set Nm := Hd.N p σ w
  have hpd : ∀ X : Matrix ι ι ℂ, X.PosSemidef → (X + (η : ℂ) • 1).PosDef := fun X hX =>
    posDef_add_smul_one hX hη
  set Q := Matrix.fromBlocks (Aᴴ * A + (η : ℂ) • 1) 0 0 (B * Bᴴ + (η : ℂ) • 1)
  have hQ1 := hpd _ (Matrix.posSemidef_conjTranspose_mul_self A)
  have hQ2 := hpd _ (Matrix.posSemidef_self_mul_conjTranspose B)
  have hQ : Q.PosSemidef := fromBlocks_diag_posSemidef hQ1.posSemidef hQ2.posSemidef
  have hTQ : Hd.T p σ w + (η : ℂ) • 1 ≤ ((2 : ℝ) : ℂ) • Q := by
    rw [Matrix.le_iff]
    exact two_blocks_sub_gram_posSemidef A B hη.le
  have hcmp := matCost_comparison hQ two_pos hTQ (Hd.Ui p σ w)
  have hUi : Hd.Ui p σ w = Matrix.fromBlocks (Aᴴ * Nm * A) (Aᴴ * Nm * Bᴴ) (B * Nm * A) (B * Nm * Bᴴ)
      := by
    rw [Hd.Ui_eq p σ hh hσ]; exact rowMat_insert _ _ _
  have hdis := matCost_fromBlocks_ge hQ1.posSemidef hQ2.posSemidef (Aᴴ * Nm * A) (Aᴴ * Nm * Bᴴ) (B *
      Nm * A) (B * Nm * Bᴴ)
  rw [← hUi] at hdis
  have hS1 : Aᴴ * A + (η : ℂ) • 1 ≤ Hd.S p σ (w + 1) + (η : ℂ) • 1 := by
    rw [Matrix.le_iff, Hd.S_eq_sum p σ (w + 1), show w + 1 - 1 = w by abel,
        add_sub_add_right_eq_sub]
    convert Matrix.posSemidef_self_mul_conjTranspose (Hd.W p σ (w + 1)) using 1
    exact add_sub_cancel_right _ _
  have hS2 : B * Bᴴ + (η : ℂ) • 1 ≤ Hd.S p σ (w - 1) + (η : ℂ) • 1 := by
    rw [Matrix.le_iff, Hd.S_eq_sum p σ (w - 1), add_sub_add_right_eq_sub]
    convert Matrix.posSemidef_conjTranspose_mul_self (Hd.W p σ (w - 1 - 1)) using 1
    exact add_sub_cancel_left _ _
  have hSpsd : ∀ v, (Hd.S p σ v).PosSemidef := fun v =>
    Matrix.posSemidef_self_mul_conjTranspose _
  have hY1 := matCost_anti (hpd _ (hSpsd _)).posSemidef hS1 (Hd.Pprev p σ (w + 1))
  have hY2 := matCost_anti (hpd _ (hSpsd _)).posSemidef hS2 (Hd.Pnext p σ (w - 1))
  rw [← Hd.Pprev_succ_eq p σ hh hσ, ← Hd.Pnext_pred_eq p σ hh hσ] at hdis
  have hmain : matCost (Hd.S p σ (w + 1) + (η : ℂ) • 1) (Hd.Pprev p σ (w + 1)) +
      matCost (Hd.S p σ (w - 1) + (η : ℂ) • 1) (Hd.Pnext p σ (w - 1)) ≤
      ENNReal.ofReal √2 * matCost (Hd.T p σ w + (η : ℂ) • 1) (Hd.Ui p σ w) := by
    have h1 : ENNReal.ofReal √2 * ENNReal.ofReal (√2)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 two_pos), ENNReal.ofReal_one]
    calc _ ≤ matCost Q (Hd.Ui p σ w) := by
          refine le_trans (add_le_add hY1 hY2) ?_
          exact hdis
      _ = ENNReal.ofReal √2 * (ENNReal.ofReal (√2)⁻¹ * matCost Q (Hd.Ui p σ w)) := by
        rw [← mul_assoc, h1, one_mul]
      _ ≤ _ := by gcongr
  have hfin := matCost_ne_top (posDef_add_smul_one (Matrix.posSemidef_conjTranspose_mul_self (Hd.R p
      σ w)) hη) (Hd.Ui p σ w)
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmain
  rw [ENNReal.toReal_add (matCost_ne_top (hpd _ (hSpsd _)) _) (matCost_ne_top (hpd _ (hSpsd _)) _),
      ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  exact this

end HeatData

end Neighbor

section VarianceDerivatives

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

lemma tr32_add (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K L : Matrix κ κ ℂ) :
    tr32 η Γ (K + L) = tr32 η Γ K + tr32 η Γ L := by
  simp only [tr32, Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring

lemma tr32_smul (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K : Matrix κ κ ℂ) (c : ℝ) :
    tr32 η Γ ((c : ℂ) • K) = c * tr32 η Γ K := by
  simp only [tr32, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; ring

variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

/-- The square-root weights of the two neighbors on the disjoint union of their indices. -/
def dv (v : Fin 3) : ι ⊕ ι → ℝ := Sum.elim (Hd.sqw p σ (v + 1)) (Hd.sqw p σ (v - 1))

/-- The column Gram matrix weighted only at the shared vertex. -/
def X (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (rowMat (Hd.A v) (Hd.A (v - 1))) (Hd.w p σ v)

omit [Fintype ι] in
lemma Dc_eq (v : Fin 3) : Hd.Dc p σ v = rdiag (Hd.dv p σ v) := by
  rw [Dc, rdiag, rdiag, rdiag, Matrix.fromBlocks_diagonal]
  congr 1; funext a; rcases a with a | a <;> rfl

lemma T_eq_DXD (hh : 0 ≤ Hd.h) (v : Fin 3) :
    Hd.T p σ v = rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Hd.dv p σ v) := by
  have hw : Hd.sqw p σ v * Hd.sqw p σ v = Hd.w p σ v := by
    funext i
    simp only [sqw, Pi.mul_apply]
    exact Real.mul_self_sqrt (gweight_nonneg _ hh _ _ i)
  rw [T, R_eq, X, wGram, ← Dc_eq, ← hw, ← rdiag_mul_rdiag]
  have hD : (Hd.Dc p σ v)ᴴ = Hd.Dc p σ v := by
    rw [Dc_eq, rdiag_conjTranspose]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, hD, Matrix.mul_assoc]

lemma rdiag_mul_mul_rdiag_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (d d' : κ → ℝ)
    (M : Matrix κ κ ℂ) (a b : κ) :
    (rdiag d * M * rdiag d') a b = (d a : ℂ) * M a b * (d' b : ℂ) := by
  simp [rdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The variance derivative of the square root of a vertex weight. -/
def dsq (k : Fin 3) (i : ι) : ℝ := (Hd.ddw p σ k i / 2) / (2 * Hd.sqw p σ k i)

/-- The column Gram variation from differentiating the shared vertex variance. -/
def Mrow (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (Hd.Brow p σ v) (fun i => Hd.ddw p σ v
    i / 2)

/-- The column Gram variation from differentiating the next vertex variance. -/
def Mnext (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  rdiag (Sum.elim (Hd.dsq p σ (v + 1)) 0) * Hd.X p σ v * rdiag (Hd.dv p σ v) +
    rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Sum.elim (Hd.dsq p σ (v + 1)) 0)

/-- The column Gram variation from differentiating the previous vertex variance. -/
def Mprev (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  rdiag (Sum.elim 0 (Hd.dsq p σ (v - 1))) * Hd.X p σ v * rdiag (Hd.dv p σ v) +
    rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Sum.elim 0 (Hd.dsq p σ (v - 1)))

lemma Mrow_eq (v : Fin 3) :
    Hd.Mrow p σ v = rdiag (Hd.dv p σ v) * wGram (rowMat (Hd.A v) (Hd.A (v - 1))) (fun i =>
      Hd.ddw p σ v i / 2) * rdiag (Hd.dv p σ v) := by
  rw [Mrow, wGram, wGram, Brow, Dc_eq]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_w_curve {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ₀ : ℝ}
    (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀) (hσ : ∀ k, 0 < c θ₀ k) (k : Fin 3) (i : ι) :
    HasDerivAt (fun θ => Hd.w p (c θ) k i) (c' k * (Hd.ddw p (c θ₀) k i / 2)) θ₀ := by
  have := (hasDerivAt_gweight_σ Hd.u Hd.h (p k) (hσ k) i).comp θ₀ (hc k)
  exact this.congr_deriv (by simp only [ddw_def]; ring)

omit [DecidableEq ι] [Fintype ι] in
lemma hasDerivAt_sqw_curve (hh : 0 < Hd.h) {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ₀ : ℝ}
    (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀) (hσ : ∀ k, 0 < c θ₀ k) (k : Fin 3) (i : ι) :
    HasDerivAt (fun θ => Hd.sqw p (c θ) k i) (c' k * Hd.dsq p (c θ₀) k i) θ₀ := by
  classical
  have hpos : 0 < Hd.w p (c θ₀) k i := Hd.w_pos p (c θ₀) hh (hσ k) i
  have := (Hd.hasDerivAt_w_curve p hc hσ k i).sqrt hpos.ne'
  exact this.congr_deriv (by unfold HeatData.dsq HeatData.sqw; ring)

theorem hasDerivAt_e_curve (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {c : ℝ → Fin 3 → ℝ}
    {c' : Fin 3 → ℝ} {θ₀ : ℝ} (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀)
    (hσ : ∀ k, 0 < c θ₀ k) (v : Fin 3) :
    HasDerivAt (fun θ => Hd.e p (c θ) η v) (c' v * tr32 η (Hd.T p (c θ₀) v) (Hd.Mrow p (c θ₀) v)
      + c' (v + 1) * tr32 η (Hd.T p (c θ₀) v) (Hd.Mnext p (c θ₀) v) + c' (v - 1) * tr32 η (Hd.T p
      (c θ₀) v) (Hd.Mprev p (c θ₀) v)) θ₀ := by
  set σ₀ := c θ₀
  set P' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (c' v : ℂ) • Hd.Mrow p σ₀ v + (c' (v + 1) : ℂ) • Hd.Mnext p
      σ₀ v + (c' (v - 1) : ℂ) • Hd.Mprev p σ₀ v
  have hT : ∀ θ, (Hd.T p (c θ) v).PosSemidef := fun θ =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hdv : ∀ a, HasDerivAt (fun θ => Hd.dv p (c θ) v a) (Sum.elim (fun i => c' (v + 1) * Hd.dsq p
      σ₀ (v + 1) i) (fun i => c' (v - 1) * Hd.dsq p σ₀ (v - 1) i) a) θ₀ := by
    rintro (i | i)
    · exact Hd.hasDerivAt_sqw_curve p hh hc hσ (v + 1) i
    · exact Hd.hasDerivAt_sqw_curve p hh hc hσ (v - 1) i
  have hX : ∀ a b, HasDerivAt (fun θ => Hd.X p (c θ) v a b) (wGram (rowMat (Hd.A v) (Hd.A (v - 1)))
      (fun i => c' v * (Hd.ddw p σ₀ v i / 2)) a b)
      θ₀ := fun a b =>
    hasDerivAt_wGram _ (f := fun θ => Hd.w p (c θ) v) (fun i => Hd.hasDerivAt_w_curve p hc hσ v i) a
        b
  have hd : ∀ a b, HasDerivAt (fun θ => Hd.T p (c θ) v a b) (P' a b) θ₀ := by
    intro a b
    have e1 : (fun θ => Hd.T p (c θ) v a b) = fun θ =>
        (Hd.dv p (c θ) v a : ℂ) * Hd.X p (c θ) v a b * (Hd.dv p (c θ) v b : ℂ) := by
      funext θ; rw [T_eq_DXD Hd p _ hh.le, rdiag_mul_mul_rdiag_apply]
    rw [e1]
    have := (((hdv a).ofReal_comp).fun_mul (hX a b)).fun_mul (hdv b).ofReal_comp
    convert this using 1
    have hw2 : (fun i => c' v * (Hd.ddw p σ₀ v i / 2)) = c' v • fun i => Hd.ddw p σ₀ v i / 2 := by
      funext i; simp
    simp only [P', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Mrow_eq, Mnext, Mprev,
      rdiag_mul_mul_rdiag_apply, hw2, wGram_smul]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [dv] <;> ring
  have hE := hasDerivAt_energyReg hη hT hd
  refine hE.congr_deriv ?_
  change tr32 η (Hd.T p σ₀ v) P' = _
  simp only [P', tr32_add, tr32_smul]

lemma hasDerivAt_update_coord (σ : Fin 3 → ℝ) (k j : Fin 3) (x : ℝ) :
    HasDerivAt (fun τ => Function.update σ k τ j) ((Pi.single k (1 : ℝ) : Fin 3 → ℝ) j) x := by
  by_cases hj : j = k
  · subst hj; simpa using hasDerivAt_id' x
  · simp only [Function.update_of_ne hj, Pi.single_apply, hj, ite_false]
    exact hasDerivAt_const _ _

lemma update_pos {σ : Fin 3 → ℝ} (hσ : ∀ k, 0 < σ k) (k : Fin 3) :
    ∀ j, 0 < (fun τ => Function.update σ k τ) (σ k) j := by
  intro j; simp [hσ]

lemma tr32_Mnext_eq (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    tr32 η (Hd.T p σ v) (Hd.Mnext p σ v) = tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (fun i =>
      Hd.ddw p σ (v + 1) i / 2)) := by
  have h1 := Hd.hasDerivAt_e_curve p hh hη (c := fun τ => Function.update σ (v + 1) τ) (c' :=
      (Pi.single (v + 1) (1 : ℝ) : Fin 3 → ℝ)) (θ₀ := σ (v + 1)) (fun j => hasDerivAt_update_coord σ
      (v + 1) j _) (update_pos hσ (v + 1)) v
  simp only [Function.update_eq_self, Pi.single_eq_same,
    Pi.single_eq_of_ne (fin3_ne_succ v), Pi.single_eq_of_ne (fin3_succ_ne_pred v).symm,
    zero_mul, one_mul, zero_add, add_zero] at h1
  exact h1.unique (Hd.e_heat_next p σ hh.le hη hσ v).2.2

lemma tr32_Mprev_eq (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    tr32 η (Hd.T p σ v) (Hd.Mprev p σ v) = tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (fun i =>
      Hd.ddw p σ (v - 1) i / 2)) := by
  have h1 := Hd.hasDerivAt_e_curve p hh hη (c := fun τ => Function.update σ (v - 1) τ) (c' :=
      (Pi.single (v - 1) (1 : ℝ) : Fin 3 → ℝ)) (θ₀ := σ (v - 1)) (fun j => hasDerivAt_update_coord σ
      (v - 1) j _) (update_pos hσ (v - 1)) v
  simp only [Function.update_eq_self, Pi.single_eq_same,
    Pi.single_eq_of_ne (fin3_ne_pred v), Pi.single_eq_of_ne (fin3_succ_ne_pred v),
    zero_mul, one_mul, zero_add, add_zero] at h1
  exact h1.unique (Hd.e_heat_prev p σ hh.le hη hσ v).2.2

lemma tr32_wGram_half (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ : Matrix κ κ ℂ)
    (B : Matrix ι κ ℂ) (f : ι → ℝ) :
    tr32 η Γ (wGram B (fun i => f i / 2)) = tr32 η Γ (wGram B f) / 2 := by
  rw [show (fun i => f i / 2) = (1 / 2 : ℝ) • f by funext i; simp; ring, wGram_smul,
    tr32_smul]; ring

theorem e_heat_s (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα : ∀ k, 0 < α k)
    {s : ℝ} (hs : 0 < s) (v : Fin 3) :
    HasDerivAt (fun t => Hd.e p (fun k => α k * t) η v) ((α v * tr32 η (Hd.T p (fun k => α k *
      s) v) (wGram (Hd.Brow p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) v)) + α (v + 1) *
      tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bnext p (fun k => α k * s) v) (Hd.ddw p (fun
      k => α k * s) (v + 1))) + α (v - 1) * tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bprev
      p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) (v - 1)))) / 2) s := by
  have hσ : ∀ k, 0 < (fun k => α k * s) k := fun k => mul_pos (hα k) hs
  have h1 := Hd.hasDerivAt_e_curve p hh hη (c := fun t k => α k * t) (c' := α) (θ₀ := s) (fun k =>
      by simpa using (hasDerivAt_id s).const_mul (α k)) hσ v
  refine h1.congr_deriv ?_
  rw [Hd.tr32_Mnext_eq p _ hh hη hσ, Hd.tr32_Mprev_eq p _ hh hη hσ, Mrow, tr32_wGram_half,
    tr32_wGram_half, tr32_wGram_half]
  ring

end HeatData

end VarianceDerivatives

section MatContinuity

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma sqrt_hsSq_add_le (X Y : Matrix n n ℂ) : √(hsSq (X + Y)) ≤ √(hsSq X) + √(hsSq Y) := by
  have h1 : hsSq (X + Y) = hsSq X + hsSq Y + 2 * hsRe X Y := by
    rw [← hsRe_self, ← hsRe_self, ← hsRe_self, hsRe_add_right, hsRe_comm (X + Y) X,
      hsRe_comm (X + Y) Y, hsRe_add_right, hsRe_add_right, hsRe_comm Y X]; ring
  have h2 := (le_abs_self _).trans (abs_hsRe_le X Y)
  rw [Real.sqrt_le_left (by positivity), h1]
  have hX := Real.sq_sqrt (hsSq_nonneg X)
  have hY := Real.sq_sqrt (hsSq_nonneg Y)
  nlinarith

omit [DecidableEq n] in
lemma sqrt_hsSq_neg (X : Matrix n n ℂ) : hsSq (-X) = hsSq X := by simp [hsSq]

omit [DecidableEq n] in
lemma sqrt_hsSq_mul_le (X Y : Matrix n n ℂ) : √(hsSq (X * Y)) ≤ √(hsSq X) * √(hsSq Y) := by
  classical
  rw [← Real.sqrt_mul (hsSq_nonneg X)]
  exact Real.sqrt_le_sqrt (hsSq_mul_le X Y)

omit [DecidableEq n] in
lemma hsRe_mul_left_adj {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    hsRe X (A * Y) = hsRe (A * X) Y := by
  simp only [hsRe, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]

omit [DecidableEq n] in
lemma hsRe_mul_right_adj {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    hsRe X (Y * A) = hsRe (X * A) Y := by
  simp only [hsRe, Matrix.conjTranspose_mul, hA.eq]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

lemma sqrt_hsSq_sqrt_sub_le {Y₁ Y₂ : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (h₁ : (Y₁ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (h₂ : (Y₂ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    √(hsSq (CFC.sqrt Y₁ - CFC.sqrt Y₂)) ≤ √(hsSq (Y₁ - Y₂)) / (√η + √η) := by
  have hY₁ : 0 ≤ Y₁ := by
    have := h₁.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le : (0 : ℂ) ≤ η))
    simpa using this.nonneg
  have hY₂ : 0 ≤ Y₂ := by
    have := h₂.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le : (0 : ℂ) ≤ η))
    simpa using this.nonneg
  have e : CFC.sqrt Y₁ * (CFC.sqrt Y₁ - CFC.sqrt Y₂) + (CFC.sqrt Y₁ - CFC.sqrt Y₂) * CFC.sqrt Y₂ =
      Y₁ - Y₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, CFC.sqrt_mul_sqrt_self Y₁ hY₁,
      CFC.sqrt_mul_sqrt_self Y₂ hY₂]
    abel
  have := sqrt_hsSq_le_sylvester (by positivity : 0 < √η + √η) (sqrt_sub_posSemidef hη.le h₁)
      (sqrt_sub_posSemidef hη.le h₂) (CFC.sqrt Y₁ - CFC.sqrt Y₂)
  rwa [e] at this

lemma sqrt_hsSq_sylvSol_le {A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (hA : (A - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y : Matrix n n ℂ) :
    √(hsSq (sylvSol A Y)) ≤ √(hsSq Y) / (c + c) := by
  have := sqrt_hsSq_le_sylvester (by positivity : 0 < c + c) hA hA (sylvSol A Y)
  rwa [(sylvSol_spec hc hA Y).1] at this

lemma sqrt_hsSq_sylvSol_sub_le {A₁ A₂ : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : (A₁ - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (h₂ : (A₂ - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y₁ Y₂ : Matrix n n ℂ) :
    √(hsSq (sylvSol A₁ Y₁ - sylvSol A₂ Y₂)) ≤ (√(hsSq (Y₁ - Y₂)) + 2 * (√(hsSq (A₁ - A₂)) *
      (√(hsSq Y₂) / (c + c)))) / (c + c) := by
  set X₁ := sylvSol A₁ Y₁
  set X₂ := sylvSol A₂ Y₂
  have s₁ := (sylvSol_spec hc h₁ Y₁).1
  have s₂ := (sylvSol_spec hc h₂ Y₂).1
  have e : A₁ * (X₁ - X₂) + (X₁ - X₂) * A₁ = (Y₁ - Y₂) + -((A₁ - A₂) * X₂) + -(X₂ * (A₁ - A₂)) := by
    rw [← s₁, ← s₂]; noncomm_ring
  have h := sqrt_hsSq_le_sylvester (by positivity : 0 < c + c) h₁ h₁ (X₁ - X₂)
  rw [e] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have hX₂ := sqrt_hsSq_sylvSol_le hc h₂ Y₂
  refine (sqrt_hsSq_add_le _ _).trans ?_
  have t1 := sqrt_hsSq_add_le (Y₁ - Y₂) (-((A₁ - A₂) * X₂))
  rw [sqrt_hsSq_neg] at t1 ⊢
  have t2 := sqrt_hsSq_mul_le (A₁ - A₂) X₂
  have t3 := sqrt_hsSq_mul_le X₂ (A₁ - A₂)
  have hA0 := Real.sqrt_nonneg (hsSq (A₁ - A₂))
  have : √(hsSq (A₁ - A₂)) * √(hsSq X₂) ≤ √(hsSq (A₁ - A₂)) * (√(hsSq Y₂) / (c + c)) :=
    mul_le_mul_of_nonneg_left hX₂ hA0
  nlinarith [Real.sqrt_nonneg (hsSq X₂)]

omit [DecidableEq n] in
lemma tendsto_entry_of_hsSq {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : Tendsto (fun a => √(hsSq (f a - g))) l (𝓝 0)) :
    Tendsto f l (𝓝 g) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) h
  have := norm_entry_le_sqrt_hsSq (f a - g) i j
  simpa using this

omit [DecidableEq n] in
lemma tendsto_sqrt_hsSq_sub {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun a => √(hsSq (f a - g))) l (𝓝 0) := by
  have := tendsto_hsSq_sub (f := f) (g := g) fun i j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j
  simpa using this.sqrt

lemma ContinuousOn.sylvSol {Z : Type*} [TopologicalSpace Z] {A Y : Z → Matrix n n ℂ} {s : Set Z}
    (hA : ContinuousOn A s) (hY : ContinuousOn Y s) {c : ℝ} (hc : 0 < c)
    (hpos : ∀ z ∈ s, (A z - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    ContinuousOn (fun z => sylvSol (A z) (Y z)) s := by
  intro z hz
  refine tendsto_entry_of_hsSq ?_
  have hA0 := tendsto_sqrt_hsSq_sub (hA z hz)
  have hY0 := tendsto_sqrt_hsSq_sub (hY z hz)
  have h1 : Tendsto (fun a => (√(hsSq (Y a - Y z)) + 2 * (√(hsSq (A a - A z)) * (√(hsSq (Y z)) / (c
      + c)))) / (c + c)) (𝓝[s] z) (𝓝 0) := by
    have := ((hY0.add ((hA0.mul_const (√(hsSq (Y z)) / (c + c))).const_mul 2)).div_const (c + c))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => Real.sqrt_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact sqrt_hsSq_sylvSol_sub_le hc (hpos a ha) (hpos z hz) _ _

omit [DecidableEq n] in
lemma costInt_eq_complete {A K X₀ : Matrix n n ℂ} (hA : A.IsHermitian)
    (hK : A * X₀ + X₀ * A = K) (X : Matrix n n ℂ) :
    costInt A K X = hsRe K X₀ - hsRe (X - X₀) (A * (X - X₀) + (X - X₀) * A) := by
  classical
  have hsym : ∀ U W : Matrix n n ℂ, hsRe U (A * W + W * A) = hsRe (A * U + U * A) W := by
    intro U W
    rw [hsRe_add_right, hsRe_mul_left_adj hA, hsRe_mul_right_adj hA, hsRe_comm (A * U) W,
      hsRe_comm (U * A) W, hsRe_comm (A * U + U * A) W, hsRe_add_right]
  have hL : A * (X - X₀) + (X - X₀) * A = (A * X + X * A) - K := by
    rw [← hK]; noncomm_ring
  rw [hL, hsRe_sub_right, hsRe_comm (X - X₀), hsRe_comm (X - X₀), hsRe_sub_right,
    hsRe_sub_right, hsRe_comm (A * X + X * A) X, hsRe_comm (A * X + X * A) X₀, hsym X₀ X, hK,
    hsRe_comm K X₀, ← hK, hsym X₀ X₀, hK, costInt, hsRe_add_right]
  ring

theorem matCost_eq_sylv {P : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ENNReal.ofReal ((3 / 2) * hsRe K (sylvSol (CFC.sqrt P) K)) := by
  have hs := sqrt_sub_posSemidef hη.le hP
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  set A := CFC.sqrt P
  have hAh : A.IsHermitian := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  have hX := (sylvSol_spec hsη hs K).1
  set X₀ := sylvSol A K
  have hq : ∀ D : Matrix n n ℂ, 0 ≤ hsRe D (A * D + D * A) := by
    intro D
    have := sylvester_lower hs hs D
    have : 0 ≤ (√η + √η) * hsSq D := by have := hsSq_nonneg D; positivity
    linarith
  refine le_antisymm (iSup_le fun X => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [costInt_eq_complete hAh hX X]
    have := hq (X - X₀)
    nlinarith
  · refine le_trans (le_of_eq ?_) (le_iSup _ X₀)
    rw [costInt_eq_complete hAh hX X₀, sub_self]
    simp [hsRe]

end MatContinuity

section CoordIBP

theorem integral_mul_deriv_coord {n : ℕ} (i : Fin (n + 1)) {F G F' G' : (Fin (n + 1) → ℝ) → ℝ}
    (hF : ∀ p, HasDerivAt (fun x => F (Function.update p i x)) (F' p) (p i))
    (hG : ∀ p, HasDerivAt (fun x => G (Function.update p i x)) (G' p) (p i))
    (h1 : Integrable (fun p => F p * G' p)) (h2 : Integrable (fun p => F' p * G p))
    (h3 : Integrable (fun p => F p * G p)) :
    ∫ p, F p * G' p = -∫ p, F' p * G p := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hint : ∀ {f : (Fin (n + 1) → ℝ) → ℝ}, Integrable f →
      Integrable (fun z : ℝ × (Fin n → ℝ) => f (Fin.insertNth i z.1 z.2)) ((volume : Measure ℝ).prod
          volume) := by
    intro f hf
    exact (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  have hmain : ∀ {f : (Fin (n + 1) → ℝ) → ℝ}, Integrable f → ∫ p, f p =
      ∫ q : Fin n → ℝ, ∫ x : ℝ, f (Fin.insertNth i x q) := by
    intro f hf
    rw [← hmp.integral_comp' (g := f)]
    exact integral_prod_symm _ (hint hf)
  rw [hmain h1, hmain h2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [(hint h1).prod_left_ae, (hint h2).prod_left_ae, (hint h3).prod_left_ae]
    with q hq1 hq2 hq3
  have hu : ∀ x, HasDerivAt (fun y => F (Fin.insertNth i y q)) (F' (Fin.insertNth i x q)) x := by
    intro x
    have := hF (Fin.insertNth i x q)
    simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
    exact this
  have hv : ∀ x, HasDerivAt (fun y => G (Fin.insertNth i y q)) (G' (Fin.insertNth i x q)) x := by
    intro x
    have := hG (Fin.insertNth i x q)
    simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
    exact this
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    hq1 hq2 hq3

end CoordIBP

section GaussBounds

lemma abs_gaussianD_le_unif (j : ℕ) {σa σb : ℝ} (ha : 0 < σa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ t, |gaussianD j σ t| ≤ C * Real.exp (-(t ^ 2) / (4 *
      σb)) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j 0
  refine ⟨C * (√σa)⁻¹ ^ (j + 1), by positivity, fun σ hσ t => ?_⟩
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have h1 := h σ hσ0 t
  simp only [pow_zero, one_mul, mul_one] at h1
  have hs : (√σ)⁻¹ ≤ (√σa)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 ha) (Real.sqrt_le_sqrt hσ.1)
  have he : Real.exp (-(t ^ 2) / (4 * σ)) ≤ Real.exp (-(t ^ 2) / (4 * σb)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith [hσ.2])
  calc |gaussianD j σ t| ≤ C * (√σ)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σ)) := h1
    _ ≤ C * (√σa)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σb)) := by gcongr

lemma exp_shift_le (u q : ℝ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-((u - q) ^ 2) / (4 * c)) ≤ Real.exp (u ^ 2 / (4 * c)) * Real.exp (-(q ^ 2) / (8 *
      c)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : -((u - q) ^ 2) ≤ u ^ 2 - q ^ 2 / 2 := by nlinarith [sq_nonneg (2 * u - q)]
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by
      positivity)]
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 32 * c ^ 2)]

/-- A Gaussian decay envelope on an interval of heat scales. -/
def edec (b x : ℝ) : ℝ := Real.exp (-(x ^ 2) / (16 * b))

lemma edec_pos (b x : ℝ) : 0 < edec b x := Real.exp_pos _

lemma edec_le_one {b : ℝ} (hb : 0 < b) (x : ℝ) : edec b x ≤ 1 := by
  rw [edec, Real.exp_le_one_iff]
  have := sq_nonneg x
  rw [neg_div, neg_nonpos]; positivity

lemma edec_sq {b : ℝ} (x : ℝ) :
    edec b x ^ 2 = Real.exp (-(x ^ 2) / (8 * b)) := by
  rw [edec, sq, ← Real.exp_add]; congr 1; ring

lemma abs_gaussianD_nodes_le {ι : Type*} [Finite ι] (u : ι → ℝ) (j : ℕ) {σa σb : ℝ}
    (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ q i, |gaussianD j σ (u i - q)| ≤ C * edec σb q ^ 2 := by
  let := Fintype.ofFinite ι
  obtain ⟨C, hC, h⟩ := abs_gaussianD_le_unif j (σb := σb) ha
  have hb : 0 < σb := ha.trans_le hab
  refine ⟨C * ∑ i, Real.exp (u i ^ 2 / (4 * σb)), by positivity, fun σ hσ q i => ?_⟩
  rw [edec_sq]
  calc |gaussianD j σ (u i - q)| ≤ C * Real.exp (-((u i - q) ^ 2) / (4 * σb)) := h σ hσ _
    _ ≤ C * (Real.exp (u i ^ 2 / (4 * σb)) * Real.exp (-(q ^ 2) / (8 * σb))) := by
      gcongr; exact exp_shift_le _ _ hb
    _ ≤ C * ((∑ i, Real.exp (u i ^ 2 / (4 * σb))) * Real.exp (-(q ^ 2) / (8 * σb))) := by
      gcongr
      exact Finset.single_le_sum (f := fun i => Real.exp (u i ^ 2 / (4 * σb))) (fun _ _ =>
          (Real.exp_pos _).le) (Finset.mem_univ i)
    _ = _ := by ring

end GaussBounds

section HeatBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_wGram_le {κ : Type*} (B : Matrix ι κ ℂ) (f : ι → ℝ) {β γ : ℝ}
    (hB : ∀ i a, ‖B i a‖ ≤ β) (hf : ∀ i, |f i| ≤ γ) (a b : κ) :
    ‖wGram B f a b‖ ≤ Fintype.card ι * (β * γ * β) := by
  rw [wGram_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖star (B i a) * (f i : ℂ) * B i b‖ ≤ ∑ _i : ι, β * γ * β := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
        have hγ : 0 ≤ γ := (abs_nonneg _).trans (hf i)
        have hβ : 0 ≤ β := (norm_nonneg _).trans (hB i a)
        gcongr
        · exact hB i a
        · exact hf i
        · exact hB i b
    _ = _ := by simp

namespace HeatData

variable (Hd : HeatData ι)

/-- The sum of the norms of all entries in the three input matrices. -/
def MA : ℝ := ∑ k, ∑ i, ∑ j, ‖Hd.A k i j‖

omit [DecidableEq ι] in
lemma norm_A_le (k : Fin 3) (i j : ι) : ‖Hd.A k i j‖ ≤ Hd.MA := by
  unfold MA
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ i, ∑ j, ‖Hd.A k i j‖) (fun _ _ => by
      positivity) (Finset.mem_univ k))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖Hd.A k i j‖) (fun _ _ => by
      positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖Hd.A k i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)

omit [DecidableEq ι] in
lemma MA_nonneg : 0 ≤ Hd.MA := by unfold MA; positivity

omit [DecidableEq ι] in
lemma norm_rowMat_le (v : Fin 3) (i : ι) (a : ι ⊕ ι) :
    ‖rowMat (Hd.A v) (Hd.A (v - 1)) i a‖ ≤ Hd.MA := by
  rcases a with j | j
  · simpa [rowMat] using Hd.norm_A_le v i j
  · simpa [rowMat, Matrix.conjTranspose_apply] using Hd.norm_A_le (v - 1) j i

/-- The decay envelope at a vertex multiplied by the sum of its neighbors' envelopes. -/
def phi (b : ℝ) (v : Fin 3) (p : Fin 3 → ℝ) : ℝ :=
  edec b (p v) * (edec b (p (v + 1)) + edec b (p (v - 1)))

omit [Fintype ι] [DecidableEq ι] in
lemma phi_nonneg (b : ℝ) (v : Fin 3) (p : Fin 3 → ℝ) : 0 ≤ phi b v p := by
  unfold phi; have := edec_pos b (p v); have := edec_pos b (p (v + 1))
  have := edec_pos b (p (v - 1)); positivity

omit [DecidableEq ι] [Fintype ι] in
lemma weight_bounds [Finite ι] (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ k i, |Hd.w p σ k i| ≤ C *
      edec σb (p k) ^ 2 ∧ |Hd.dw p σ k i| ≤ C * edec σb (p k) ^ 2 ∧ |Hd.ddw p σ k i| ≤ C * edec σb
      (p k) ^ 2 ∧ Hd.sqw p σ k i ≤ √C * edec σb (p k) := by
  obtain ⟨C0, hC0, h0⟩ := abs_gaussianD_nodes_le Hd.u 0 ha hab
  obtain ⟨C1, hC1, h1⟩ := abs_gaussianD_nodes_le Hd.u 1 ha hab
  obtain ⟨C2, hC2, h2⟩ := abs_gaussianD_nodes_le Hd.u 2 ha hab
  set C := Hd.h * (C0 + C1 + C2)
  have hC : 0 ≤ C := by positivity
  have hE : ∀ x, 0 ≤ edec σb x ^ 2 := fun x => sq_nonneg _
  refine ⟨C, hC, fun p σ hσ k i => ?_⟩
  have hw : |Hd.w p σ k i| ≤ C * edec σb (p k) ^ 2 := by
    have := h0 (σ k) (hσ k) (p k) i
    rw [gaussianD_zero] at this
    simp only [w, gweight, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussian (σ k) (Hd.u i - p k)| ≤ Hd.h * (C0 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  refine ⟨hw, ?_, ?_, ?_⟩
  · have := h1 (σ k) (hσ k) (p k) i
    simp only [dw, abs_neg, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussianD 1 (σ k) (Hd.u i - p k)| ≤ Hd.h * (C1 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  · have := h2 (σ k) (hσ k) (p k) i
    simp only [ddw, abs_mul, abs_of_nonneg hh, C]
    calc Hd.h * |gaussianD 2 (σ k) (Hd.u i - p k)| ≤ Hd.h * (C2 * edec σb (p k) ^ 2) := by
          gcongr
      _ ≤ _ := by have := hE (p k); nlinarith [mul_nonneg hh this]
  · have hw0 : 0 ≤ Hd.w p σ k i := gweight_nonneg _ hh _ _ i
    rw [sqw, ← Real.sqrt_sq (edec_pos σb (p k)).le, ← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans hw)

end HeatData

end HeatBounds

section EntryBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

omit [Fintype ι] [DecidableEq ι] in
lemma sqw_nonneg (p σ : Fin 3 → ℝ) (k : Fin 3) (i : ι) : 0 ≤ Hd.sqw p σ k i := Real.sqrt_nonneg _

lemma entry_bounds (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ v, (∀ a b, ‖Hd.T p σ v a
      b‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Ui p σ v a b‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v) a b‖ ≤ C * phi σb v p ^ 2) ∧ (∀ i j, ‖Hd.S p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖Hd.Pnext p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Pprev p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)) i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Bprev p
      σ v) (Hd.ddw p σ (v - 1)) i j‖ ≤ C * phi σb v p ^ 2) := by
  obtain ⟨Cw, hCw, hw⟩ := Hd.weight_bounds hh ha hab
  set sC := √Cw
  have hsC : 0 ≤ sC := Real.sqrt_nonneg _
  set K := (Fintype.card ι : ℝ) * (Hd.MA * sC) ^ 2 * Cw
  have hK : 0 ≤ K := by have := Hd.MA_nonneg; positivity
  refine ⟨2 * K, by positivity, fun p σ hσ v => ?_⟩
  set E0 := edec σb (p v)
  set E1 := edec σb (p (v + 1))
  set E2 := edec σb (p (v - 1))
  have hE0 : 0 ≤ E0 := (edec_pos _ _).le
  have hE1 : 0 ≤ E1 := (edec_pos _ _).le
  have hE2 : 0 ≤ E2 := (edec_pos _ _).le
  have hphi : phi σb v p = E0 * (E1 + E2) := rfl
  have hMA := Hd.MA_nonneg
  have hBrow : ∀ i a, ‖Hd.Brow p σ v i a‖ ≤ Hd.MA * sC * (E1 + E2) := by
    intro i a
    rw [Brow, Dc_eq, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd : |Hd.dv p σ v a| ≤ sC * (E1 + E2) := by
      rcases a with j | j
      · simp only [dv, Sum.elim_inl]
        rw [abs_of_nonneg (Hd.sqw_nonneg _ _ _ _)]
        have := (hw p σ hσ (v + 1) j).2.2.2
        nlinarith
      · simp only [dv, Sum.elim_inr]
        rw [abs_of_nonneg (Hd.sqw_nonneg _ _ _ _)]
        have := (hw p σ hσ (v - 1) j).2.2.2
        nlinarith
    rw [mul_assoc]
    exact mul_le_mul (Hd.norm_rowMat_le v i a) hd (abs_nonneg _) hMA
  have hrow : ∀ f : ι → ℝ, (∀ i, |f i| ≤ Cw * E0 ^ 2) → ∀ a b,
      ‖wGram (Hd.Brow p σ v) f a b‖ ≤ 2 * K * phi σb v p ^ 2 := by
    intro f hf a b
    refine (norm_wGram_le _ f hBrow hf a b).trans ?_
    rw [hphi]
    have : (Fintype.card ι : ℝ) * (Hd.MA * sC * (E1 + E2) * (Cw * E0 ^ 2) * (Hd.MA * sC * (E1 +
        E2))) = K * (E0 * (E1 + E2)) ^ 2 := by
      simp only [K]; ring
    rw [this]
    have : 0 ≤ K * (E0 * (E1 + E2)) ^ 2 := by positivity
    linarith
  have hBn : ∀ j i, ‖Hd.Bnext p σ v j i‖ ≤ Hd.MA * sC * E0 := by
    intro j i
    rw [Bnext, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Hd.sqw_nonneg _ _ _ _), mul_assoc]
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact mul_le_mul (Hd.norm_A_le v i j) (hw p σ hσ v i).2.2.2 (Hd.sqw_nonneg _ _ _ _) hMA
  have hBp : ∀ j i, ‖Hd.Bprev p σ v j i‖ ≤ Hd.MA * sC * E0 := by
    intro j i
    rw [Bprev, rdiag, Matrix.mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Hd.sqw_nonneg _ _ _ _), mul_assoc]
    exact mul_le_mul (Hd.norm_A_le (v - 1) j i) (hw p σ hσ v i).2.2.2 (Hd.sqw_nonneg _ _ _ _)
      hMA
  have hcol : ∀ (B : Matrix ι ι ℂ) (E : ℝ), 0 ≤ E → E ≤ E1 + E2 → (∀ j i, ‖B j i‖ ≤ Hd.MA * sC * E0)
      → ∀ f : ι → ℝ, (∀ i, |f i| ≤ Cw * E ^ 2) →
      ∀ a b, ‖wGram B f a b‖ ≤ K * phi σb v p ^ 2 := by
    intro B E hE hEle hB f hf a b
    refine (norm_wGram_le _ f hB hf a b).trans ?_
    rw [hphi]
    have : (Fintype.card ι : ℝ) * (Hd.MA * sC * E0 * (Cw * E ^ 2) * (Hd.MA * sC * E0)) =
        K * (E0 * E) ^ 2 := by simp only [K]; ring
    rw [this]
    gcongr
  have h1 : E1 ≤ E1 + E2 := by linarith
  have h2 : E2 ≤ E1 + E2 := by linarith
  refine ⟨fun a b => ⟨?_, ?_, ?_⟩, fun i j => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [T_eq_wGram Hd p σ hh]
    exact hrow _ (fun i => (hw p σ hσ v i).1) a b
  · exact hrow _ (fun i => (hw p σ hσ v i).2.1) a b
  · exact hrow _ (fun i => (hw p σ hσ v i).2.2.1) a b
  · rw [S_eq_wGram Hd p σ hh, Matrix.add_apply]
    refine (norm_add_le _ _).trans ?_
    have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).1) i j
    have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).1) i j
    linarith
  · have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    rw [Pnext]; linarith
  · have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    rw [Pprev]; linarith
  · have := hcol _ E1 hE1 h1 hBn _ (fun i => (hw p σ hσ (v + 1) i).2.2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    linarith
  · have := hcol _ E2 hE2 h2 hBp _ (fun i => (hw p σ hσ (v - 1) i).2.2.1) i j
    have : 0 ≤ K * phi σb v p ^ 2 := by positivity
    linarith

end HeatData

end EntryBounds

section MatBounds

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
lemma hsSq_le_of_entry_le (K : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖K a b‖ ≤ c) :
    hsSq K ≤ (Fintype.card κ : ℝ) ^ 2 * c ^ 2 := by
  unfold hsSq
  calc ∑ a, ∑ b, ‖K a b‖ ^ 2 ≤ ∑ _a : κ, ∑ _b : κ, c ^ 2 := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (h a b) 2
    _ = _ := by simp; ring

omit [DecidableEq κ] in
lemma sqrt_hsSq_le_of_entry_le (K : Matrix κ κ ℂ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ a b, ‖K a b‖ ≤ c) :
    √(hsSq K) ≤ Fintype.card κ * c := by
  rw [Real.sqrt_le_left (by positivity)]
  have := hsSq_le_of_entry_le K h
  nlinarith

omit [DecidableEq κ] in
lemma re_trace_le_of_entry_le (Γ : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖Γ a b‖ ≤ c) :
    Γ.trace.re ≤ Fintype.card κ * c := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ a, (Γ a a).re ≤ ∑ _a : κ, c :=
        Finset.sum_le_sum fun a _ => (Complex.re_le_norm _).trans (h a a)
    _ = _ := by simp

omit [DecidableEq κ] in
lemma hsSq_sqrt_eq {κ : Type*} [Fintype κ] {P : Matrix κ κ ℂ} (hP : 0 ≤ P) :
    open scoped Classical in hsSq (CFC.sqrt P) = P.trace.re := by
  classical
  rw [← hsRe_self, hsRe, (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self P hP]

lemma HeatData.abs_tr32_le {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) {η : ℝ} (hη : 0 ≤ η)
    (K : Matrix κ κ ℂ) :
    |HeatData.tr32 η Γ K| ≤ (3 / 2) * √(Γ.trace.re + Fintype.card κ * η) * √(hsSq K) := by
  have hP : 0 ≤ Γ + (η : ℂ) • (1 : Matrix κ κ ℂ) := (hΓ.add (Matrix.PosSemidef.one.smul (by
      exact_mod_cast hη))).nonneg
  have e1 : ((CFC.sqrt (Γ + (η : ℂ) • 1) * K).trace).re = hsRe (CFC.sqrt (Γ + (η : ℂ) • 1)) K := by
    rw [hsRe, (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq]
  have e2 : (Γ + (η : ℂ) • (1 : Matrix κ κ ℂ)).trace.re = Γ.trace.re + Fintype.card κ * η := by
    simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]; ring
  rw [HeatData.tr32, e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), mul_assoc]
  gcongr
  refine (abs_hsRe_le _ _).trans ?_
  rw [hsSq_sqrt_eq hP, e2]

lemma matCost_toReal_le_hsSq {P : Matrix κ κ ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef) (K : Matrix κ κ ℂ) :
    (matCost P K).toReal ≤ (3 / 4) * hsSq K / √η := by
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  rw [matCost_eq_sylv hη hP, ENNReal.toReal_ofReal']
  have hX := sqrt_hsSq_sylvSol_le hsη (sqrt_sub_posSemidef hη.le hP) K
  have h1 := (le_abs_self _).trans (abs_hsRe_le K (sylvSol (CFC.sqrt P) K))
  have hK := Real.sq_sqrt (hsSq_nonneg K)
  have hK0 := Real.sqrt_nonneg (hsSq K)
  refine max_le ?_ (by have := hsSq_nonneg K; positivity)
  have : √(hsSq K) * √(hsSq (sylvSol (CFC.sqrt P) K)) ≤ √(hsSq K) * (√(hsSq K) / (√η + √η)) :=
    mul_le_mul_of_nonneg_left hX hK0
  have e3 : √(hsSq K) * (√(hsSq K) / (√η + √η)) = hsSq K / (2 * √η) := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (hsSq_nonneg K)]; ring
  rw [e3] at this
  calc 3 / 2 * hsRe K (sylvSol (CFC.sqrt P) K) ≤ 3 / 2 * (hsSq K / (2 * √η)) := by linarith
    _ = _ := by field_simp; ring

lemma rpow_three_halves {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = √y ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2) * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hy,
    ← Real.sqrt_eq_rpow]

lemma three_halves_sub_le {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) ≤ 2 * x * √(x + η) := by
  rw [rpow_three_halves (by positivity), rpow_three_halves hη]
  set a := √(x + η)
  set b := √η
  have ha : a ^ 2 = x + η := Real.sq_sqrt (by positivity)
  have hb : b ^ 2 = η := Real.sq_sqrt hη
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hx' : x = a ^ 2 - b ^ 2 := by linarith
  rw [hx']
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hb0 hb0),
    mul_nonneg (sub_nonneg.2 hab) (mul_nonneg hb0 (hb0.trans hab))]

lemma three_halves_sub_nonneg {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    0 ≤ (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) := by
  rw [sub_nonneg]
  exact Real.rpow_le_rpow hη (by linarith) (by norm_num)

lemma energyReg_bounds {P : Matrix κ κ ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ energyReg η P ∧ energyReg η P ≤ 2 * P.trace.re * √(P.trace.re + η) := by
  set L := P.trace.re
  have hL : L = ∑ i, hP.1.eigenvalues i := by
    simp only [L]
    rw [hP.1.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  have hev : ∀ i, 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg
  have hevL : ∀ i, hP.1.eigenvalues i ≤ L := fun i => by
    rw [hL]; exact Finset.single_le_sum (fun j _ => hev j) (Finset.mem_univ i)
  rw [energyReg, trF_eq_sum _ hP.1]
  refine ⟨Finset.sum_nonneg fun i _ => three_halves_sub_nonneg (hev i) hη, ?_⟩
  calc ∑ i, ((hP.1.eigenvalues i + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ))
      ≤ ∑ i, 2 * hP.1.eigenvalues i * √(L + η) := by
        refine Finset.sum_le_sum fun i _ => (three_halves_sub_le (hev i) hη).trans ?_
        gcongr
        · exact mul_nonneg zero_le_two (hev i)
        · exact hevL i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, ← hL]

end MatBounds

section EnergyBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

omit [Fintype ι] [DecidableEq ι] in
lemma phi_le_two {b : ℝ} (hb : 0 < b) (v : Fin 3) (p : Fin 3 → ℝ) : phi b v p ≤ 2 := by
  unfold phi
  have h0 := edec_le_one hb (p v)
  have h1 := edec_le_one hb (p (v + 1))
  have h2 := edec_le_one hb (p (v - 1))
  have := edec_pos b (p v)
  have := edec_pos b (p (v + 1))
  have := edec_pos b (p (v - 1))
  nlinarith

lemma gram_scalar_bounds {κ : Type*} [Fintype κ] [DecidableEq κ] {N C₀ φ η : ℝ}
    (hN : (Fintype.card κ : ℝ) ≤ N) (hC₀ : 0 ≤ C₀) (hφ : 0 ≤ φ) (hφ2 : φ ≤ 2) (hη : 0 < η)
    {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) (hΓb : ∀ a b, ‖Γ a b‖ ≤ C₀ * φ ^ 2) :
    (∀ K : Matrix κ κ ℂ, (∀ a b, ‖K a b‖ ≤ C₀ * φ ^ 2) → |tr32 η Γ K| ≤ (3 / 2) * √(N * (4 * C₀)
      + N * η) * N * C₀ * φ ^ 2 ∧ |(matCost (Γ + (η : ℂ) • 1) K).toReal| ≤ (3 / 4) * N ^ 2 * (4 *
      C₀) * C₀ / √η * φ ^ 2) ∧ |energyReg η Γ| ≤ 2 * N * C₀ * √(N * (4 * C₀) + η) * φ ^ 2 := by
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hN
  have hQ : C₀ * φ ^ 2 ≤ 4 * C₀ := by nlinarith [mul_le_mul hφ2 hφ2 hφ (by norm_num : (0:ℝ) ≤ 2)]
  have hQ0 : 0 ≤ C₀ * φ ^ 2 := by positivity
  have htr : Γ.trace.re ≤ N * (C₀ * φ ^ 2) := (re_trace_le_of_entry_le Γ hΓb).trans
      (mul_le_mul_of_nonneg_right hN hQ0)
  have htr4 : Γ.trace.re ≤ N * (4 * C₀) := htr.trans (mul_le_mul_of_nonneg_left hQ hN0)
  have htr0 : 0 ≤ Γ.trace.re := re_trace_nonneg_of_posSemidef hΓ
  refine ⟨fun K hK => ⟨?_, ?_⟩, ?_⟩
  · refine (abs_tr32_le hΓ hη.le K).trans ?_
    have hs : √(hsSq K) ≤ N * (C₀ * φ ^ 2) := (sqrt_hsSq_le_of_entry_le K hQ0 hK).trans
        (mul_le_mul_of_nonneg_right hN hQ0)
    have hr : √(Γ.trace.re + Fintype.card κ * η) ≤ √(N * (4 * C₀) + N * η) :=
      Real.sqrt_le_sqrt (add_le_add htr4 (mul_le_mul_of_nonneg_right hN hη.le))
    calc 3 / 2 * √(Γ.trace.re + Fintype.card κ * η) * √(hsSq K)
        ≤ 3 / 2 * √(N * (4 * C₀) + N * η) * (N * (C₀ * φ ^ 2)) := by gcongr
      _ = _ := by ring
  · have hcost := matCost_toReal_le_hsSq hη (add_smul_one_sub_posSemidef hΓ η) K
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    refine hcost.trans ?_
    have hs := hsSq_le_of_entry_le K hK
    have hs' : hsSq K ≤ N ^ 2 * ((4 * C₀) * (C₀ * φ ^ 2)) := by
      refine hs.trans ?_
      have : (C₀ * φ ^ 2) ^ 2 ≤ (4 * C₀) * (C₀ * φ ^ 2) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hQ hQ0
      have hN2 : (Fintype.card κ : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      exact mul_le_mul hN2 this (sq_nonneg _) (sq_nonneg _)
    have hsη : 0 < √η := Real.sqrt_pos.2 hη
    calc 3 / 4 * hsSq K / √η ≤ 3 / 4 * (N ^ 2 * ((4 * C₀) * (C₀ * φ ^ 2))) / √η := by gcongr
      _ = _ := by ring
  · obtain ⟨h0, h1⟩ := energyReg_bounds hΓ hη.le
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    have hr : √(Γ.trace.re + η) ≤ √(N * (4 * C₀) + η) := Real.sqrt_le_sqrt (by linarith)
    calc 2 * Γ.trace.re * √(Γ.trace.re + η) ≤ 2 * (N * (C₀ * φ ^ 2)) * √(N * (4 * C₀) + η) := by
          gcongr
      _ = _ := by ring

/-- The energies, trace derivatives and costs associated with one vertex. -/
inductive VertexQuantity
  | energy | centerTrace | centerSecondTrace | nextTrace | previousTrace
  | nextSecondTrace | previousSecondTrace | centerCost | nextCost | previousCost | mixedCost

/-- Evaluate a vertex quantity at fixed centers, variances and regularization. -/
def vertexValue (p σ : Fin 3 → ℝ) (η : ℝ) (v : Fin 3) : VertexQuantity → ℝ
  | .energy => Hd.e p σ η v
  | .centerTrace => tr32 η (Hd.T p σ v) (Hd.Ui p σ v)
  | .centerSecondTrace => tr32 η (Hd.T p σ v) (wGram (Hd.Brow p σ v) (Hd.ddw p σ v))
  | .nextTrace => tr32 η (Hd.S p σ v) (Hd.Pnext p σ v)
  | .previousTrace => tr32 η (Hd.S p σ v) (Hd.Pprev p σ v)
  | .nextSecondTrace => tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)))
  | .previousSecondTrace => tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))
  | .centerCost => Hd.V p σ η v
  | .nextCost => Hd.Ynext p σ η v
  | .previousCost => Hd.Yprev p σ η v
  | .mixedCost => Hd.Z p σ η v

theorem scalar_bounds (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) {σa σb : ℝ} (ha : 0 < σa)
    (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) →
      ∀ v term, |Hd.vertexValue p σ η v term| ≤ C * phi σb v p ^ 2 := by
  obtain ⟨C₀, hC₀, hent⟩ := Hd.entry_bounds hh ha hab
  have hb : 0 < σb := ha.trans_le hab
  set N : ℝ := Fintype.card (ι ⊕ ι) + Fintype.card ι
  have hN1 : (Fintype.card (ι ⊕ ι) : ℝ) ≤ N := by
    simp only [N]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  have hN2 : (Fintype.card ι : ℝ) ≤ N := by
    simp only [N]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι ⊕ ι))]
  set A1 := (3 / 2) * √(N * (4 * C₀) + N * η) * N * C₀
  set A2 := (3 / 4) * N ^ 2 * (4 * C₀) * C₀ / √η
  set A3 := 2 * N * C₀ * √(N * (4 * C₀) + η)
  have hN0 : 0 ≤ N := by positivity
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  have hA3 : 0 ≤ A3 := by positivity
  refine ⟨A1 + A2 + A3, by positivity, fun p σ hσ v term => ?_⟩
  obtain ⟨hT, hS⟩ := hent p σ hσ v
  set φ := phi σb v p
  have hφ : 0 ≤ φ := phi_nonneg _ _ _
  have hφ2 : φ ≤ 2 := phi_le_two hb v p
  have hφsq : 0 ≤ φ ^ 2 := sq_nonneg _
  have hTpsd : (Hd.T p σ v).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hSpsd : (Hd.S p σ v).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  obtain ⟨gT, eT⟩ := gram_scalar_bounds hN1 hC₀ hφ hφ2 hη hTpsd (fun a b => (hT a b).1)
  obtain ⟨gS, -⟩ := gram_scalar_bounds hN2 hC₀ hφ hφ2 hη hSpsd (fun a b => (hS a b).1)
  have w1 : ∀ x, x ≤ A1 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have w2 : ∀ x, x ≤ A2 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have w3 : ∀ x, x ≤ A3 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have hY1 := (gS _ fun a b => (hS a b).2.1).2
  have hY2 := (gS _ fun a b => (hS a b).2.2.1).2
  cases term with
  | energy => exact w3 _ eT
  | centerTrace => exact w1 _ (gT _ fun a b => (hT a b).2.1).1
  | centerSecondTrace => exact w1 _ (gT _ fun a b => (hT a b).2.2).1
  | nextTrace => exact w1 _ (gS _ fun a b => (hS a b).2.1).1
  | previousTrace => exact w1 _ (gS _ fun a b => (hS a b).2.2.1).1
  | nextSecondTrace => exact w1 _ (gS _ fun a b => (hS a b).2.2.2.1).1
  | previousSecondTrace => exact w1 _ (gS _ fun a b => (hS a b).2.2.2.2).1
  | centerCost => exact w2 _ (gT _ fun a b => (hT a b).2.1).2
  | nextCost => exact w2 _ hY1
  | previousCost => exact w2 _ hY2
  | mixedCost =>
    have hPD := posDef_add_smul_one hSpsd hη
    have hZ := abs_matCostBil_le hPD (Hd.Pnext p σ v) (Hd.Pprev p σ v)
    refine w2 _ (hZ.trans ?_)
    have e1 : 0 ≤ (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal :=
      ENNReal.toReal_nonneg
    have e2 : 0 ≤ (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal :=
      ENNReal.toReal_nonneg
    rw [abs_of_nonneg e1] at hY1
    rw [abs_of_nonneg e2] at hY2
    calc √(matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal *
          √(matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal
        ≤ √(A2 * φ ^ 2) * √(A2 * φ ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt hY1) (Real.sqrt_le_sqrt hY2) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
      _ = A2 * φ ^ 2 := Real.mul_self_sqrt (by positivity)

end HeatData

end EnergyBounds

section HeatContinuity

lemma continuousOn_gaussianD_joint (j : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => gaussianD j z.1 z.2) {z | 0 < z.1} := by
  have h : ContinuousOn (fun z : ℝ × ℝ => (√(2 * π))⁻¹ * (√z.1)⁻¹ ^ (j + 1) *
      gaussProfileD j ((√z.1)⁻¹ * z.2)) {z | 0 < z.1} := by
    have hs : ContinuousOn (fun z : ℝ × ℝ => (√z.1)⁻¹) {z | 0 < z.1} := (Real.continuous_sqrt.comp
        continuous_fst).continuousOn.inv₀ fun z hz =>
        (Real.sqrt_pos.2 hz).ne'
    exact (continuousOn_const.mul (hs.pow _)).mul ((contDiff_gaussProfileD
        j).continuous.comp_continuousOn (hs.mul continuous_snd.continuousOn))
  refine h.congr fun z hz => ?_
  exact gaussianD_eq_profile j hz z.2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]

lemma continuous_gaussianD_comp (j : ℕ) {σ t : X → ℝ} (hσ : Continuous σ) (ht : Continuous t)
    (hpos : ∀ x, 0 < σ x) :
    Continuous (fun x => gaussianD j (σ x) (t x)) := (continuousOn_gaussianD_joint
        j).comp_continuous (hσ.prodMk ht) hpos

omit [Fintype ι] in
lemma continuous_rdiag {f : X → ι → ℝ} (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => rdiag (f x) :=
  Continuous.matrix_diagonal (continuous_pi fun i => Complex.continuous_ofReal.comp (hf i))

lemma continuous_wGram {κ : Type*} {B : X → Matrix ι κ ℂ} {f : X → ι → ℝ} (hB : Continuous B)
    (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => wGram (B x) (f x) := by
  exact (hB.matrix_conjTranspose.matrix_mul (continuous_rdiag hf)).matrix_mul hB

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_re_trace {κ : Type*} [Fintype κ] {M : X → Matrix κ κ ℂ} (hM : Continuous M) :
    Continuous fun x => (M x).trace.re :=
  Complex.continuous_re.comp hM.matrix_trace

namespace HeatData

variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_w (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k) (k : Fin 3)
    (i : ι) :
    Continuous fun x => Hd.w (p x) (σ x) k i := by
  have := continuous_gaussianD_comp 0 ((continuous_apply k).comp hσ) (continuous_const.sub
      ((continuous_apply k).comp hp)) (fun x => hpos x k) (t := fun x =>
      Hd.u i - p x k)
  simp only [gaussianD_zero] at this
  exact continuous_const.mul this

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_dw (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.dw (p x) (σ x) k i := (continuous_const.mul (continuous_gaussianD_comp 1
        ((continuous_apply k).comp hσ) (continuous_const.sub ((continuous_apply k).comp hp)) (fun x
        => hpos x k))).neg

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_ddw (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.ddw (p x) (σ x) k i :=
  continuous_const.mul (continuous_gaussianD_comp 2 ((continuous_apply k).comp hσ)
      (continuous_const.sub ((continuous_apply k).comp hp)) (fun x => hpos x k))

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_sqw (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.sqw (p x) (σ x) k i :=
  Real.continuous_sqrt.comp (Hd.continuous_w hp hσ hpos k i)

lemma continuous_mats (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (v : Fin 3) :
    Continuous (fun x => Hd.T (p x) (σ x) v) ∧ Continuous (fun x => Hd.S (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Ui (p x) (σ x) v) ∧ Continuous (fun x => Hd.Pnext (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Pprev (p x) (σ x) v) ∧ Continuous (fun x => wGram (Hd.Brow (p x) (σ
      x) v) (Hd.ddw (p x) (σ x) v)) ∧ Continuous (fun x => wGram (Hd.Bnext (p x) (σ x) v) (Hd.ddw
      (p x) (σ x) (v + 1))) ∧ Continuous (fun x => wGram (Hd.Bprev (p x) (σ x) v) (Hd.ddw (p x) (σ
      x) (v - 1))) := by
  have hsq := Hd.continuous_sqw hp hσ hpos
  have hW : ∀ k, Continuous fun x => Hd.W (p x) (σ x) k := fun k =>
    ((continuous_rdiag (hsq k)).matrix_mul continuous_const).matrix_mul (continuous_rdiag (hsq _))
  have hR : Continuous fun x => Hd.R (p x) (σ x) v := by
    refine continuous_matrix fun i a => ?_
    rcases a with j | j
    · simpa [R, rowMat] using (hW v).matrix_elem i j
    · simpa [R, rowMat] using (hW (v - 1)).matrix_conjTranspose.matrix_elem i j
  have hDc : Continuous fun x => Hd.Dc (p x) (σ x) v :=
    Continuous.matrix_fromBlocks (continuous_rdiag (hsq _)) continuous_const continuous_const
        (continuous_rdiag (hsq _))
  have hBrow : Continuous fun x => Hd.Brow (p x) (σ x) v := continuous_const.matrix_mul hDc
  have hBn : Continuous fun x => Hd.Bnext (p x) (σ x) v :=
    continuous_const.matrix_mul (continuous_rdiag (hsq v))
  have hBp : Continuous fun x => Hd.Bprev (p x) (σ x) v :=
    continuous_const.matrix_mul (continuous_rdiag (hsq v))
  exact ⟨hR.matrix_conjTranspose.matrix_mul hR, hR.matrix_mul hR.matrix_conjTranspose,
    continuous_wGram hBrow (Hd.continuous_dw hp hσ hpos v),
    continuous_wGram hBn (Hd.continuous_dw hp hσ hpos _),
    continuous_wGram hBp (Hd.continuous_dw hp hσ hpos _),
    continuous_wGram hBrow (Hd.continuous_ddw hp hσ hpos v),
    continuous_wGram hBn (Hd.continuous_ddw hp hσ hpos _),
    continuous_wGram hBp (Hd.continuous_ddw hp hσ hpos _)⟩

end HeatData

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma continuous_sqrt_add {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    Continuous fun x => CFC.sqrt (Γ x + (η : ℂ) • 1) := by
  exact CFC.continuousOn_sqrt.comp_continuous (hΓ.add continuous_const) fun x =>
    ((hpsd x).add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη))).nonneg

lemma continuous_tr32 {Γ K : X → Matrix κ κ ℂ} (hΓ : Continuous Γ) (hK : Continuous K)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => HeatData.tr32 η (Γ x) (K x) :=
  continuous_const.mul (continuous_re_trace ((continuous_sqrt_add hΓ hpsd hη.le).matrix_mul hK))

lemma continuous_energyReg {Γ : X → Matrix κ κ ℂ} (hΓ : Continuous Γ)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => energyReg η (Γ x) := by
  have : (fun x => energyReg η (Γ x)) = fun x =>
      (((Γ x + (η : ℂ) • 1) * CFC.sqrt (Γ x + (η : ℂ) • 1)).trace).re -
        η ^ (3 / 2 : ℝ) * Fintype.card κ := by
    funext x; exact energyReg_eq_trace (hpsd x) hη.le
  rw [this]
  exact (continuous_re_trace ((hΓ.add continuous_const).matrix_mul (continuous_sqrt_add hΓ hpsd
      hη.le))).sub continuous_const

lemma continuous_matCost {Γ K : X → Matrix κ κ ℂ} (hΓ : Continuous Γ) (hK : Continuous K)
    (hpsd : ∀ x, (Γ x).PosSemidef) {η : ℝ} (hη : 0 < η) :
    Continuous fun x => (matCost (Γ x + (η : ℂ) • 1) (K x)).toReal := by
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  have hP : ∀ x, (Γ x + (η : ℂ) • 1 - (η : ℂ) • (1 : Matrix κ κ ℂ)).PosSemidef := fun x =>
    add_smul_one_sub_posSemidef (hpsd x) η
  have : (fun x => (matCost (Γ x + (η : ℂ) • 1) (K x)).toReal) = fun x =>
      max ((3 / 2) * hsRe (K x) (sylvSol (CFC.sqrt (Γ x + (η : ℂ) • 1)) (K x))) 0 := by
    funext x
    rw [matCost_eq_sylv hη (hP x), ENNReal.toReal_ofReal']
  rw [this]
  have hS := continuous_sqrt_add hΓ hpsd hη.le
  have hX : Continuous fun x => sylvSol (CFC.sqrt (Γ x + (η : ℂ) • 1)) (K x) := by
    rw [← continuousOn_univ]
    exact ContinuousOn.sylvSol hS.continuousOn hK.continuousOn hsη fun x _ =>
      sqrt_sub_posSemidef hη.le (hP x)
  refine (continuous_const.mul ?_).max continuous_const
  exact continuous_re_trace (hK.matrix_conjTranspose.matrix_mul hX)

namespace HeatData

variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}

theorem continuous_scalars (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    {η : ℝ} (hη : 0 < η) (v : Fin 3) (term : VertexQuantity) :
    Continuous (fun x => Hd.vertexValue (p x) (σ x) η v term) := by
  obtain ⟨hT, hS, hU, hPn, hPp, hM1, hM2, hM3⟩ := Hd.continuous_mats hp hσ hpos v
  have hTp : ∀ x, (Hd.T (p x) (σ x) v).PosSemidef := fun x =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hSp : ∀ x, (Hd.S (p x) (σ x) v).PosSemidef := fun x =>
    Matrix.posSemidef_self_mul_conjTranspose _
  cases term with
  | energy => exact continuous_energyReg hT hTp hη
  | centerTrace => exact continuous_tr32 hT hU hTp hη
  | centerSecondTrace => exact continuous_tr32 hT hM1 hTp hη
  | nextTrace => exact continuous_tr32 hS hPn hSp hη
  | previousTrace => exact continuous_tr32 hS hPp hSp hη
  | nextSecondTrace => exact continuous_tr32 hS hM2 hSp hη
  | previousSecondTrace => exact continuous_tr32 hS hM3 hSp hη
  | centerCost => exact continuous_matCost hT hU hTp hη
  | nextCost => exact continuous_matCost hS hPn hSp hη
  | previousCost => exact continuous_matCost hS hPp hSp hη
  | mixedCost =>
    exact ((continuous_matCost hS (hPn.add hPp) hSp hη).sub
      (continuous_matCost hS (hPn.sub hPp) hSp hη)).div_const 4

end HeatData

end HeatContinuity

section GaussianCenterIntegration

/-- The `m`th Gaussian derivative at the sum of the centers, with variance `β * s`. -/
def Gm (β : ℝ) (m : ℕ) (s : ℝ) (p : Fin 3 → ℝ) : ℝ := gaussianD m (β * s) (p 0 + p 1 + p 2)

/-- The product Gaussian decay envelope in the three center coordinates. -/
def gdom (ε : ℝ) (p : Fin 3 → ℝ) : ℝ := ∏ k, Real.exp (-ε * p k ^ 2)

lemma gdom_eq (ε : ℝ) (p : Fin 3 → ℝ) :
    gdom ε p = Real.exp (-ε * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2)) := by
  rw [gdom, Fin.prod_univ_three, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma integrable_gdom {ε : ℝ} (hε : 0 < ε) : Integrable (gdom ε) :=
  Integrable.fintype_prod (f := fun _ x => Real.exp (-ε * x ^ 2))
    fun _ => integrable_exp_neg_mul_sq hε

lemma exp_pair_le (a b c : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-(a ^ 2 + b ^ 2) * x) * Real.exp (-(a + b + c) ^ 2 * y) ≤ Real.exp (-(min x y / 4)
      * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  set m := min x y
  have hm : 0 < m := lt_min hx hy
  have hmx : m ≤ x := min_le_left _ _
  have hmy : m ≤ y := min_le_right _ _
  set S := a + b + c
  have hc : c ^ 2 ≤ 3 * (S ^ 2 + a ^ 2 + b ^ 2) := by
    have : c = S - a - b := by simp only [S]; ring
    rw [this]; nlinarith [sq_nonneg (S + a), sq_nonneg (S + b), sq_nonneg (a - b)]
  have h1 : m * (a ^ 2 + b ^ 2) ≤ x * (a ^ 2 + b ^ 2) :=
    mul_le_mul_of_nonneg_right hmx (by positivity)
  have h2 : m * S ^ 2 ≤ y * S ^ 2 := mul_le_mul_of_nonneg_right hmy (by positivity)
  nlinarith

lemma sum_three_eq (v : Fin 3) (p : Fin 3 → ℝ) :
    p 0 + p 1 + p 2 = p v + p (v + 1) + p (v - 1) ∧ p 0 + p 1 + p 2 = p v + p (v - 1) + p (v +
      1) ∧ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = p v ^ 2 + p (v + 1) ^ 2 + p (v - 1) ^ 2 ∧ p 0 ^ 2 + p 1 ^
      2 + p 2 ^ 2 = p v ^ 2 + p (v - 1) ^ 2 + p (v + 1) ^ 2 := by
  have : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
  rcases this with rfl | rfl | rfl
  · have h1 : (0 : Fin 3) + 1 = 1 := rfl
    have h2 : (0 : Fin 3) - 1 = 2 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩
  · have h1 : (1 : Fin 3) + 1 = 2 := rfl
    have h2 : (1 : Fin 3) - 1 = 0 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩
  · have h1 : (2 : Fin 3) + 1 = 0 := rfl
    have h2 : (2 : Fin 3) - 1 = 1 := rfl
    rw [h1, h2]; exact ⟨by ring, by ring, by ring, by ring⟩

lemma phi_sq_mul_exp_le {σb τb : ℝ} (hσ : 0 < σb) (hτ : 0 < τb) (v : Fin 3) (p : Fin 3 → ℝ) :
    HeatData.phi σb v p ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ 4 * gdom (min (1 /
      (8 * σb)) (1 / (4 * τb)) / 4) p := by
  set E0 := edec σb (p v)
  set E1 := edec σb (p (v + 1))
  set E2 := edec σb (p (v - 1))
  set ε := min (1 / (8 * σb)) (1 / (4 * τb)) / 4
  have hx : 0 < 1 / (8 * σb) := by positivity
  have hy : 0 < 1 / (4 * τb) := by positivity
  obtain ⟨hs1, hs2, hq1, hq2⟩ := sum_three_eq v p
  have hG : Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) =
      Real.exp (-(p 0 + p 1 + p 2) ^ 2 * (1 / (4 * τb))) := by congr 1; ring
  have hE : ∀ x, edec σb x ^ 2 = Real.exp (-(x ^ 2) * (1 / (8 * σb))) := fun x => by
    rw [edec_sq]; congr 1; ring
  have t1 : (E0 * E1) ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ gdom ε p := by
    rw [mul_pow, hE, hE, ← Real.exp_add, hG, gdom_eq, hs1, hq1]
    have := exp_pair_le (p v) (p (v + 1)) (p (v - 1)) hx hy
    convert this using 2
    ring_nf
  have t2 : (E0 * E2) ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) ≤ gdom ε p := by
    rw [mul_pow, hE, hE, ← Real.exp_add, hG, gdom_eq, hs2, hq2]
    have := exp_pair_le (p v) (p (v - 1)) (p (v + 1)) hx hy
    convert this using 2
    ring_nf
  have hphi : HeatData.phi σb v p ^ 2 ≤ 2 * (E0 * E1) ^ 2 + 2 * (E0 * E2) ^ 2 := by
    simp only [HeatData.phi, E0, E1, E2]
    nlinarith [sq_nonneg (edec σb (p v) * edec σb (p (v + 1)) -
      edec σb (p v) * edec σb (p (v - 1)))]
  have hexp := (Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb))).le
  calc HeatData.phi σb v p ^ 2 * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb))
      ≤ (2 * (E0 * E1) ^ 2 + 2 * (E0 * E2) ^ 2) *
          Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * τb)) :=
        mul_le_mul_of_nonneg_right hphi hexp
    _ ≤ 4 * gdom ε p := by nlinarith

lemma abs_Gm_le (m : ℕ) {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc sa sb, ∀ p, |Gm β m s p| ≤ C * Real.exp (-(p 0 + p 1 + p 2) ^
      2 / (4 * (β * sb))) := by
  obtain ⟨C, hC, h⟩ := abs_gaussianD_le_unif m (σa := β * sa) (σb := β * sb) (by positivity)
  refine ⟨C, hC, fun s hs p => ?_⟩
  have := h (β * s) ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩ (p 0 + p 1 + p 2)
  simpa [Gm, neg_div] using this

lemma integrable_of_le_gdom {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ p, |f p| ≤ C * gdom ε p) :
    Integrable f := ((integrable_gdom hε).const_mul C).mono' hf.aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p)

lemma integrable_prod_of_le_gdom {f : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb : ℝ} (hsa : 0 < sa)
    (hf : ContinuousOn f (Set.Ioi 0 ×ˢ Set.univ)) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s ∈ Set.Ioc sa sb, ∀ p, |f (s, p)| ≤ C * gdom ε p) :
    Integrable f ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
  have hμ : (volume.restrict (Set.Ioc sa sb)).prod (volume : Measure (Fin 3 → ℝ)) = ((volume :
      Measure ℝ).prod volume).restrict (Set.Ioc sa sb ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hg : Integrable (fun z : ℝ × (Fin 3 → ℝ) => C * gdom ε z.2) ((volume.restrict (Set.Ioc sa
      sb)).prod volume) := by
    have := (integrable_const (1 : ℝ) (μ := volume.restrict (Set.Ioc sa sb))).mul_prod
        ((integrable_gdom hε).const_mul C)
    simpa using this
  refine hg.mono' ?_ ?_
  · rw [hμ]
    refine (hf.mono ?_).aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
    exact Set.prod_mono (fun s hs => hsa.trans hs.1) le_rfl
  · rw [hμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    rw [Real.norm_eq_abs]
    exact hb z.1 hz.1 z.2

end GaussianCenterIntegration

section DifferentiationUnderIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuousOn_Gm (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Gm β m z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  let rescale : ℝ × (Fin 3 → ℝ) → ℝ × ℝ := fun z => (β * z.1, z.2 0 + z.2 1 + z.2 2)
  have hcoord (i : Fin 3) : Continuous (fun z : ℝ × (Fin 3 → ℝ) => z.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hvariance : Continuous (fun z : ℝ × (Fin 3 → ℝ) => β * z.1) :=
    continuous_const.mul continuous_fst
  have hmap : Continuous rescale := hvariance.prodMk (((hcoord 0).add (hcoord 1)).add (hcoord 2))
  have hpositive : Set.MapsTo rescale (Set.Ioi 0 ×ˢ Set.univ) {z : ℝ × ℝ | 0 < z.1} :=
    fun _ hz => mul_pos hβ hz.1
  have composed := (continuousOn_gaussianD_joint m).comp' hmap.continuousOn hpositive
  simpa only [Gm, rescale] using composed

lemma continuous_slice {Q : ℝ × (Fin 3 → ℝ) → ℝ} (hQ : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    {s : ℝ} (hs : 0 < s) :
    Continuous fun p => Q (s, p) :=
  hQ.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩

lemma hasDerivAt_Gm_coord (β : ℝ) (m : ℕ) (s : ℝ) (i : Fin 3) (p : Fin 3 → ℝ) :
    HasDerivAt (fun x => Gm β m s (Function.update p i x)) (Gm β (m + 1) s p) (p i) := by
  have hin : HasDerivAt (fun x => Function.update p i x 0 + Function.update p i x 1 +
      Function.update p i x 2) 1 (p i) := by
    have := ((HeatData.hasDerivAt_update_coord p i 0 (p i)).add (HeatData.hasDerivAt_update_coord p
        i 1 (p i))).add (HeatData.hasDerivAt_update_coord p i
          2 (p i))
    convert this using 1
    have : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases this with rfl | rfl | rfl <;> simp
  have hval : Function.update p i (p i) 0 + Function.update p i (p i) 1 +
      Function.update p i (p i) 2 = p 0 + p 1 + p 2 := by simp
  have hg := hasDerivAt_gaussianD m (β * s) (p 0 + p 1 + p 2)
  rw [← hval] at hg
  have := hg.comp (p i) hin
  rw [hval, mul_one] at this
  exact this

lemma good_integrable {Q : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb σb β : ℝ} (hsa : 0 < sa) (hσb : 0 < σb)
    (hβ : 0 < β) (v : Fin 3) (hc : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    (hb : ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p, |Q (s, p)| ≤ C * HeatData.phi σb v p ^ 2) (m : ℕ) :
    (∀ s ∈ Set.Icc sa sb, Integrable (fun p => Gm β m s p * Q (s, p))) ∧ Integrable (fun z : ℝ ×
      (Fin 3 → ℝ) => Gm β m z.1 z.2 * Q z) ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
  obtain ⟨CQ, hCQ⟩ := hb
  have hsb : 0 < sb ∨ sb < sa := by
    rcases lt_or_ge 0 sb with h | h
    · exact Or.inl h
    · right; linarith
  rcases hsb with hsb | hsb
  swap
  · refine ⟨fun s hs => absurd (hs.1.trans hs.2) (not_le.2 hsb), ?_⟩
    have : Set.Ioc sa sb = ∅ := Set.Ioc_eq_empty (not_lt.2 hsb.le)
    simp [this]
  obtain ⟨Cg, hCg0, hCg⟩ := abs_Gm_le m hβ hsa (sb := sb)
  set ε := min (1 / (8 * σb)) (1 / (4 * (β * sb))) / 4
  have hε : 0 < ε := by positivity
  have hτ : 0 < β * sb := by positivity
  have hbound : ∀ s ∈ Set.Icc sa sb, ∀ p, |Gm β m s p * Q (s, p)| ≤ (Cg * |CQ| * 4) * gdom ε p := by
    intro s hs p
    have h1 := hCg s hs p
    have h2 := hCQ s hs p
    have h3 := phi_sq_mul_exp_le hσb hτ v p
    rw [abs_mul]
    have hφ := sq_nonneg (HeatData.phi σb v p)
    have hE := (Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))).le
    calc |Gm β m s p| * |Q (s, p)|
        ≤ (Cg * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))) * (|CQ| * HeatData.phi σb v p ^
            2) := by
          refine mul_le_mul h1 (h2.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hφ
      _ = Cg * |CQ| * (HeatData.phi σb v p ^ 2 *
            Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))) := by ring
      _ ≤ Cg * |CQ| * (4 * gdom ε p) := by gcongr
      _ = _ := by ring
  have hGc := continuousOn_Gm β hβ m
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs0 : 0 < s := hsa.trans_le hs.1
    exact integrable_of_le_gdom ((continuous_slice hGc hs0).mul (continuous_slice hc hs0)) hε
        (hbound s hs)
  · exact integrable_prod_of_le_gdom hsa (hGc.mul hc) hε fun s hs p =>
      hbound s (Set.Ioc_subset_Icc_self hs) p

namespace HeatData

variable (Hd : HeatData ι) (α : Fin 3 → ℝ)

/-- The vector of heat variances at scale `s) for rates `α`. -/
def sig (s : ℝ) : Fin 3 → ℝ := fun k => α k * s

theorem continuousOn_family (hα : ∀ k, 0 < α k) {η : ℝ} (hη : 0 < η) (v : Fin 3)
    (term : VertexQuantity) :
    let S : Set (ℝ × (Fin 3 → ℝ)) := Set.Ioi 0 ×ˢ Set.univ
    ContinuousOn (fun z => Hd.vertexValue z.2 (sig α z.1) η v term) S := by
  intro S
  have hp : Continuous fun x : S => (x : ℝ × (Fin 3 → ℝ)).2 := continuous_snd.comp
      continuous_subtype_val
  have hσ : Continuous fun x : S => sig α (x : ℝ × (Fin 3 → ℝ)).1 :=
    continuous_pi fun k => continuous_const.mul (continuous_fst.comp continuous_subtype_val)
  have hpos : ∀ (x : S) k, 0 < sig α (x : ℝ × (Fin 3 → ℝ)).1 k := fun x k =>
    mul_pos (hα k) x.2.1
  simp only [continuousOn_iff_continuous_domRestrict]
  exact Hd.continuous_scalars hp hσ hpos hη v term

end HeatData

end DifferentiationUnderIntegral

section VertexEnergies

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)

/-- The regularized energy at heat scale `s` and center vector `p`. -/
def qE (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .energy

/-- The first trace variation from the shared center along the chosen heat variances. -/
def qDr (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .centerTrace

/-- The first trace variation from the next center along the chosen heat variances. -/
def qDn (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .nextTrace

/-- The first trace variation from the previous center along the chosen heat variances. -/
def qDp (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .previousTrace

/-- The trace variation with a second derivative of the shared center weight. -/
def qA (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .centerSecondTrace

/-- The trace variation with a second derivative of the next center weight. -/
def qB (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .nextSecondTrace

/-- The trace variation with a second derivative of the previous center weight. -/
def qC (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .previousSecondTrace

/-- The shared vertex cost along the chosen heat variances. -/
def qV (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .centerCost

/-- The next-center cost along the chosen heat variances. -/
def qYn (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .nextCost

/-- The previous-center cost along the chosen heat variances. -/
def qYp (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .previousCost

/-- The mixed neighbor cost along the chosen heat variances. -/
def qZ (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.vertexValue p (sig α s) η v .mixedCost

/-- The terms used in dissipation include three sums of vertex quantities. -/
inductive DissipationTerm
  | base (term : VertexQuantity)
  | center | next | previous

/-- Evaluate a dissipation term along the chosen heat variances. -/
def dissipationValue : DissipationTerm → ℝ → (Fin 3 → ℝ) → ℝ
  | .base term => fun s p => Hd.vertexValue p (sig α s) η v term
  | .center => Hd.qV α η v + Hd.qA α η v
  | .next => Hd.qYn α η v + Hd.qB α η v
  | .previous => Hd.qYp α η v + Hd.qC α η v

lemma family_good (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {sa sb : ℝ} (hsa : 0 < sa) (hab : sa ≤ sb) (term : DissipationTerm) :
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.dissipationValue α η v term z.1 z.2)
        (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p,
        |Hd.dissipationValue α η v term s p| ≤ C * phi (2 * sb) v p ^ 2 := by
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα1 k)
  have continuity := Hd.continuousOn_family α hα0 hη v
  obtain ⟨C, _, bounds⟩ := Hd.scalar_bounds hh.le hη (σa := sa) (σb := 2 * sb) hsa (by linarith)
  have hrange : ∀ s ∈ Set.Icc sa sb, ∀ k, sig α s k ∈ Set.Icc sa (2 * sb) := by
    intro s hs k
    have hs0 : 0 < s := hsa.trans_le hs.1
    constructor
    · simp only [sig]; nlinarith [hα1 k, hs.1]
    · simp only [sig]; nlinarith [hα2 k, hs.2]
  have bound (q : VertexQuantity) (s : ℝ) (hs : s ∈ Set.Icc sa sb) (p : Fin 3 → ℝ) :=
    bounds p (sig α s) (hrange s hs) v q
  have sumGood (left right : VertexQuantity) :
      ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.vertexValue z.2 (sig α z.1) η v left +
        Hd.vertexValue z.2 (sig α z.1) η v right) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∃ D, ∀ s ∈ Set.Icc sa sb, ∀ p,
        |Hd.vertexValue p (sig α s) η v left + Hd.vertexValue p (sig α s) η v right| ≤
          D * phi (2 * sb) v p ^ 2 := by
    refine ⟨(continuity left).add (continuity right), 2 * C,
      fun s hs p => (abs_add_le _ _).trans ?_⟩
    linarith only [bound left s hs p, bound right s hs p]
  cases term with
  | base q => exact ⟨continuity q, C, bound q⟩
  | center => exact sumGood .centerCost .centerSecondTrace
  | next => exact sumGood .nextCost .nextSecondTrace
  | previous => exact sumGood .previousCost .previousSecondTrace

lemma weighted_integrable (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) (hab : sa ≤ sb)
    (term : DissipationTerm) (m : ℕ) :
    (∀ s ∈ Set.Icc sa sb, Integrable (fun p => Gm β m s p * Hd.dissipationValue α η v term s p)) ∧
      Integrable (fun z : ℝ × (Fin 3 → ℝ) =>
        Gm β m z.1 z.2 * Hd.dissipationValue α η v term z.1 z.2)
        ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
  obtain ⟨continuity, bound⟩ := Hd.family_good α η v hh hη hα1 hα2 hsa hab term
  exact good_integrable hsa (by linarith : 0 < 2 * sb) hβ v continuity bound m

end HeatData

end VertexEnergies

section VertexIdentities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)

theorem vertex_identities (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) (hab : sa ≤ sb) {s : ℝ} (hs : s ∈ Set.Icc sa sb) :
    ∫ p, Gm β 0 s p * (Hd.qV α η v + Hd.qA α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p,
      Gm β 0 s p * (Hd.qYn α η v + Hd.qB α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm
      β 0 s p * (Hd.qYp α η v + Hd.qC α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm β 0
      s p * Hd.qZ α η v s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p := by
  have integ (term : DissipationTerm) (m : ℕ) :=
    (Hd.weighted_integrable α η v hh hη hα1 hα2 hβ hsa hab term m).1 s hs
  have iE := integ (.base .energy)
  have iDr := integ (.base .centerTrace)
  have iDn := integ (.base .nextTrace)
  have iDp := integ (.base .previousTrace)
  have iVA := integ .center
  have iYB := integ .next
  have iYC := integ .previous
  have iZ := integ (.base .mixedCost)
  have hσ : ∀ k, 0 < sig α s k := fun k =>
    mul_pos (zero_lt_one.trans_le (hα1 k)) (hsa.trans_le hs.1)
  have hrow := fun p => Hd.e_heat_row p (sig α s) hh.le hη hσ v
  have hnext := fun p => Hd.e_heat_next p (sig α s) hh.le hη hσ v
  have hprev := fun p => Hd.e_heat_prev p (sig α s) hh.le hη hσ v
  have hmix := fun p => Hd.e_mixed p (sig α s) hh.le hη v
  have hG := fun m i p => hasDerivAt_Gm_coord β m s i p
  have hb : ∀ (i : Fin 3) (D : (Fin 3 → ℝ) → ℝ), (∀ p, HasDerivAt (fun x => Hd.qE α η v s
      (Function.update p i x)) (D p) (p i)) →
      Integrable (fun p => Gm β 1 s p * D p) →
      ∫ p, Gm β 1 s p * D p = -∫ p, Gm β 2 s p * Hd.qE α η v s p := fun i D hD hi =>
    integral_mul_deriv_coord i (F := Gm β 1 s) (F' := Gm β 2 s) (hG 1 i) hD hi (iE 2) (iE 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha := integral_mul_deriv_coord v (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDr α η v s) (G'
      := (Hd.qV α η v + Hd.qA α η v) s) (hG 0 v) (fun p => (hrow p).2.1) (iVA 0) (iDr 1) (iDr 0)
    exact ha.trans ((congrArg Neg.neg (hb v (Hd.qDr α η v s) (fun p => (hrow p).1) (iDr 1))).trans
        (neg_neg _))
  · have ha := integral_mul_deriv_coord (v + 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDn α η v
      s) (G' := (Hd.qYn α η v + Hd.qB α η v) s) (hG 0 (v + 1)) (fun p => (hnext p).2.1) (iYB 0) (iDn
      1) (iDn 0)
    exact ha.trans ((congrArg Neg.neg (hb (v + 1) (Hd.qDn α η v s) (fun p => (hnext p).1) (iDn
        1))).trans (neg_neg _))
  · have ha := integral_mul_deriv_coord (v - 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDp α η v
      s) (G' := (Hd.qYp α η v + Hd.qC α η v) s) (hG 0 (v - 1)) (fun p => (hprev p).2.1) (iYC 0) (iDp
      1) (iDp 0)
    exact ha.trans ((congrArg Neg.neg (hb (v - 1) (Hd.qDp α η v s) (fun p => (hprev p).1) (iDp
        1))).trans (neg_neg _))
  · have ha := integral_mul_deriv_coord (v + 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDp α η v
      s) (G' := Hd.qZ α η v s) (hG 0 (v + 1)) (fun p => hmix p) (iZ 0) (iDp 1) (iDp 0)
    exact ha.trans ((congrArg Neg.neg (hb (v - 1) (Hd.qDp α η v s) (fun p => (hprev p).1) (iDp
        1))).trans (neg_neg _))

end HeatData

end VertexIdentities

section NeighborAbsorption

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

lemma Z_le (p σ : Fin 3 → ℝ) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    Hd.Z p σ η v ≤ (Hd.Ynext p σ η v + Hd.Yprev p σ η v) / 2 := by
  have hPD := posDef_add_smul_one (Matrix.posSemidef_self_mul_conjTranspose (Hd.R p σ v)) hη
  have h := (le_abs_self _).trans (abs_matCostBil_le hPD (Hd.Pnext p σ v) (Hd.Pprev p σ v))
  have h1 : 0 ≤ Hd.Ynext p σ η v := ENNReal.toReal_nonneg
  have h2 : 0 ≤ Hd.Yprev p σ η v := ENNReal.toReal_nonneg
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  change Hd.Z p σ η v ≤ √(Hd.Ynext p σ η v) * √(Hd.Yprev p σ η v) at h
  nlinarith [sq_nonneg (√(Hd.Ynext p σ η v) - √(Hd.Yprev p σ η v))]

lemma sqrt_two_le : √2 ≤ 10 / 7 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num

private lemma sum_neighbor_dissipation (V nextCost prevCost mixed α : Fin 3 → ℝ)
    (hα : ∀ k, 1 ≤ α k) (hV : ∀ v, 0 ≤ V v) (hnext : ∀ v, 0 ≤ nextCost v)
    (hprev : ∀ v, 0 ≤ prevCost v)
    (hmixed : ∀ v, mixed v ≤ (nextCost v + prevCost v) / 2)
    (hneighbor : ∀ v, prevCost (v + 1) + nextCost (v - 1) ≤ 10 / 7 * V v) :
    ∑ v, (33 / 20 * mixed v - (α v * V v + α (v + 1) * nextCost v +
        α (v - 1) * prevCost v) / 2) ≤ -(1 / 28) * ∑ v, V v := by
  have sumPrev : ∑ v, prevCost (v + 1) = ∑ v, prevCost v :=
    Equiv.sum_comp (Equiv.addRight 1) prevCost
  have sumNext : ∑ v, nextCost (v - 1) = ∑ v, nextCost v :=
    Equiv.sum_comp (Equiv.addRight 1).symm nextCost
  have sumNeighbors : ∑ v, (nextCost v + prevCost v) ≤ 10 / 7 * ∑ v, V v := by
    have comparison := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hneighbor v
    rw [Finset.sum_add_distrib, sumPrev, sumNext, ← Finset.mul_sum] at comparison
    rwa [Finset.sum_add_distrib, add_comm]
  have termwise (v : Fin 3) :
      33 / 20 * mixed v - (α v * V v + α (v + 1) * nextCost v + α (v - 1) * prevCost v) / 2 ≤
        13 / 40 * (nextCost v + prevCost v) - 1 / 2 * V v := by
    have ownBound := mul_le_mul_of_nonneg_right (hα v) (hV v)
    have nextBound := mul_le_mul_of_nonneg_right (hα (v + 1)) (hnext v)
    have prevBound := mul_le_mul_of_nonneg_right (hα (v - 1)) (hprev v)
    linarith only [hmixed v, ownBound, nextBound, prevBound]
  calc
    _ ≤ ∑ v, (13 / 40 * (nextCost v + prevCost v) - 1 / 2 * V v) :=
      Finset.sum_le_sum fun v _ => termwise v
    _ ≤ _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      linarith only [sumNeighbors]

theorem pointwise_dissipation (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (p σ : Fin 3 → ℝ)
    (hσ : ∀ k, 0 < σ k) {α : Fin 3 → ℝ} (hα : ∀ k, 1 ≤ α k) :
    ∑ v, (33 / 20 * Hd.Z p σ η v - (α v * Hd.V p σ η v + α (v + 1) * Hd.Ynext p σ η v + α (v -
      1) * Hd.Yprev p σ η v) / 2) ≤ -(1 / 28) * ∑ v, Hd.V p σ η v := by
  refine sum_neighbor_dissipation (Hd.V p σ η) (Hd.Ynext p σ η) (Hd.Yprev p σ η) (Hd.Z p σ η) α
    hα (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun v => Hd.Z_le p σ hη v) ?_
  intro v
  exact (Hd.neighbor_cost_comparison p σ hh (hσ v) hη).trans
    (mul_le_mul_of_nonneg_right sqrt_two_le ENNReal.toReal_nonneg)

end HeatData

end NeighborAbsorption

section IntegratedDissipation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ)

/-- The total regularized energy averaged against the Gaussian weight across the center plane. -/
def Jbar (s : ℝ) : ℝ := ∫ p, Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p

/-- The cost at one vertex averaged against the Gaussian weight across the center plane. -/
def Vbar (v : Fin 3) (s : ℝ) : ℝ := ∫ p, Gm (1 / 10) 0 s p * Hd.qV α η v s p

theorem smeared_plane_dissipation (hh : 0 < Hd.h) (hη : 0 < η)
    (hα : ∀ k, α k = 1 ∨ α k = 11 / 10) (hsum : α 0 + α 1 + α 2 = 16 / 5) {sa sb : ℝ}
    (hsa : 0 < sa) (hab : sa ≤ sb) :
    (1 / 28) * ∫ s in sa..sb, ∑ v, Hd.Vbar α η v s ≤ Hd.Jbar α η sa - Hd.Jbar α η sb := by
  set β : ℝ := 1 / 10 with hβdef
  have hβ : 0 < β := by norm_num
  have hα1 : ∀ k, 1 ≤ α k := fun k => by rcases hα k with h | h <;> rw [h]; norm_num
  have hα2 : ∀ k, α k ≤ 2 := fun k => by rcases hα k with h | h <;> rw [h] <;> norm_num
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα1 k)
  have weighted := fun v => Hd.weighted_integrable α η v hh hη hα1 hα2 hβ hsa hab
  set F : ℝ → (Fin 3 → ℝ) → ℝ := fun s p => Gm β 0 s p * ∑ v, Hd.qE α η v s p with hF
  set Φ : Fin 3 → ℝ × (Fin 3 → ℝ) → ℝ := fun v z =>
    β / 2 * (Gm β 2 z.1 z.2 * Hd.qE α η v z.1 z.2) +
      α v / 2 * (Gm β 0 z.1 z.2 * Hd.qA α η v z.1 z.2) +
      α (v + 1) / 2 * (Gm β 0 z.1 z.2 * Hd.qB α η v z.1 z.2) +
      α (v - 1) / 2 * (Gm β 0 z.1 z.2 * Hd.qC α η v z.1 z.2) with hΦ
  set Fs : ℝ → (Fin 3 → ℝ) → ℝ := fun s p => ∑ v, Φ v (s, p) with hFs
  have hderiv : ∀ p, ∀ s, 0 < s → HasDerivAt (fun t => F t p) (Fs s p) s := by
    intro p s hs
    have hG0 : HasDerivAt (fun t => Gm β 0 t p) (gaussianD 2 (β * s) (p 0 + p 1 + p 2) / 2 * β)
        s := by
      have := (hasDerivAt_gaussianD_variance 0 (mul_pos hβ hs) (p 0 + p 1 + p 2)).comp s
          ((hasDerivAt_id s).const_mul β)
      simpa [Gm, Function.comp_def] using this
    have hE : HasDerivAt (fun t => ∑ v, Hd.qE α η v t p) (∑ v, (α v * Hd.qA α η v s p + α (v + 1) *
        Hd.qB α η v s p +
          α (v - 1) * Hd.qC α η v s p) / 2) s :=
      HasDerivAt.fun_sum fun v _ => Hd.e_heat_s p hh hη hα0 hs v
    refine (hG0.mul hE).congr_deriv ?_
    simp only [hFs, hΦ, Gm, Fin.sum_univ_three]
    ring
  have hΦint : ∀ v, Integrable (Φ v) ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
    intro v
    have iE := (weighted v (.base .energy) 2).2.const_mul (β / 2)
    have iA := (weighted v (.base .centerSecondTrace) 0).2.const_mul (α v / 2)
    have iB :=
      (weighted v (.base .nextSecondTrace) 0).2.const_mul (α (v + 1) / 2)
    have iC :=
      (weighted v (.base .previousSecondTrace) 0).2.const_mul (α (v - 1) / 2)
    exact ((iE.add iA).add iB).add iC
  have hFsint : Integrable (fun z : ℝ × (Fin 3 → ℝ) => Fs z.1 z.2) ((volume.restrict (Set.Ioc sa
      sb)).prod volume) :=
    integrable_finsetSum _ fun v _ => hΦint v
  have hFint : ∀ s ∈ Set.Icc sa sb, Integrable (F s) := by
    intro s hs
    have : F s = fun p => ∑ v, Gm β 0 s p * Hd.qE α η v s p := by
      funext p; simp only [hF, Finset.mul_sum]
    rw [this]
    exact integrable_finsetSum _ fun v _ =>
      (weighted v (.base .energy) 0).1 s hs
  have hVint (v : Fin 3) := (weighted v (.base .centerCost) 0).2
  have hstep : ∀ s ∈ Set.Icc sa sb, ∫ p, Fs s p ≤ -(1 / 28) * ∑ v, Hd.Vbar α η v s := by
    intro s hs
    have hs0 : 0 < s := hsa.trans_le hs.1
    have hσ : ∀ k, 0 < sig α s k := fun k => mul_pos (hα0 k) hs0
    have slice (v : Fin 3) (term : DissipationTerm) (m : ℕ) := (weighted v term m).1 s hs
    have iE (v : Fin 3) := (slice v (.base .energy) 2).const_mul (β / 2)
    have iVA (v : Fin 3) :=
      (slice v .center 0).const_mul (α v / 2)
    have iYB (v : Fin 3) :=
      (slice v .next 0).const_mul
        (α (v + 1) / 2)
    have iYC (v : Fin 3) :=
      (slice v .previous 0).const_mul
        (α (v - 1) / 2)
    have iZ (v : Fin 3) := slice v (.base .mixedCost) 0
    have iV (v : Fin 3) : Integrable (fun p => Gm β 0 s p * Hd.qV α η v s p) :=
      slice v (.base .centerCost) 0
    have iYn (v : Fin 3) := slice v (.base .nextCost) 0
    have iYp (v : Fin 3) := slice v (.base .previousCost) 0
    set K : Fin 3 → (Fin 3 → ℝ) → ℝ := fun v p =>
      β / 2 * (Gm β 2 s p * Hd.qE α η v s p) +
        α v / 2 * (Gm β 0 s p * (Hd.qV α η v + Hd.qA α η v) s p) +
        α (v + 1) / 2 * (Gm β 0 s p * (Hd.qYn α η v + Hd.qB α η v) s p) +
        α (v - 1) / 2 * (Gm β 0 s p * (Hd.qYp α η v + Hd.qC α η v) s p) -
        33 / 20 * (Gm β 0 s p * Hd.qZ α η v s p) with hK
    have hKint (v : Fin 3) : Integrable (K v) :=
      ((((iE v).add (iVA v)).add (iYB v)).add (iYC v)).sub ((iZ v).const_mul (33 / 20))
    have hK0 : ∀ v, ∫ p, K v p = 0 := by
      intro v
      obtain ⟨e1, e2, e3, e4⟩ := Hd.vertex_identities α η v hh hη hα1 hα2 hβ hsa hab hs
      have hsv := (sum_three_eq v α).1
      have integralEA := (iE v).add (iVA v)
      have integralEAB := integralEA.add (iYB v)
      have splitZ := integral_sub (integralEAB.add (iYC v)) ((iZ v).const_mul (33 / 20))
      have splitC := integral_add integralEAB (iYC v)
      have splitB := integral_add integralEA (iYB v)
      have splitA := integral_add (iE v) (iVA v)
      simp only [dissipationValue, qE, qV, qA, qYn, qB, qYp, qC, qZ, Pi.add_apply]
        at splitZ splitC splitB splitA e1 e2 e3 e4
      simp only [hK, qE, qV, qA, qYn, qB, qYp, qC, qZ, Pi.add_apply]
      rw [splitZ, splitC, splitB, splitA, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, e1, e2, e3, e4]
      have hs3 : α v + α (v + 1) + α (v - 1) = 16 / 5 := by linarith
      set J := ∫ p, Gm β 2 s p * Hd.vertexValue p (sig α s) η v .energy
      linear_combination (J / 2) * hs3 + (J / 2) * hβdef
    set H : (Fin 3 → ℝ) → ℝ := fun p => ∑ v, (33 / 20 * Hd.qZ α η v s p - (α v * Hd.qV α η v s p + α
        (v + 1) * Hd.qYn α η v s p +
        α (v - 1) * Hd.qYp α η v s p) / 2) with hH
    have hsplit : ∀ p, Fs s p = Gm β 0 s p * H p + ∑ v, K v p := by
      intro p
      simp only [hFs, hΦ, hH, hK, Pi.add_apply, Fin.sum_univ_three]
      ring
    have hHint : Integrable (fun p => Gm β 0 s p * H p) := by
      have : (fun p => Gm β 0 s p * H p) = fun p => ∑ v, (33 / 20 * (Gm β 0 s p * Hd.qZ α η v s p) -
          (α v * (Gm β 0 s p * Hd.qV α η v s p) + α (v + 1) * (Gm β 0 s p * Hd.qYn α η v s p) +
              α (v - 1) * (Gm β 0 s p * Hd.qYp α η v s p)) / 2) := by
        funext p; simp only [hH, Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_; ring
      rw [this]
      refine integrable_finsetSum _ fun v _ => ?_
      have costs := ((iV v).const_mul (α v)).add ((iYn v).const_mul (α (v + 1)))
      exact ((iZ v).const_mul (33 / 20)).sub
        ((costs.add ((iYp v).const_mul (α (v - 1)))).div_const 2)
    have hG0nn : ∀ p, 0 ≤ Gm β 0 s p := fun p => by
      simp only [Gm, gaussianD_zero, gaussian]; positivity
    have hpt : ∀ p, Gm β 0 s p * H p ≤ -(1 / 28) * ∑ v, Gm β 0 s p * Hd.qV α η v s p := by
      intro p
      have := Hd.pointwise_dissipation hh hη p (sig α s) hσ hα1
      rw [← Finset.mul_sum]
      have h' := mul_le_mul_of_nonneg_left this (hG0nn p)
      simp only [hH]
      simp only [qZ, qV, qYn, qYp, vertexValue]
      linarith
    calc ∫ p, Fs s p = ∫ p, (Gm β 0 s p * H p + ∑ v, K v p) := by
          congr 1; funext p; exact hsplit p
      _ = ∫ p, Gm β 0 s p * H p := by
          rw [integral_add hHint (integrable_finsetSum _ fun v _ => hKint v),
            integral_finsetSum _ fun v _ => hKint v]
          simp [hK0]
      _ ≤ ∫ p, -(1 / 28) * ∑ v, Gm β 0 s p * Hd.qV α η v s p :=
          integral_mono hHint ((integrable_finsetSum _ fun v _ => iV v).const_mul _) hpt
      _ = -(1 / 28) * ∑ v, Hd.Vbar α η v s := by
          rw [integral_const_mul, integral_finsetSum _ fun v _ => iV v]
          rfl
  have hIoc : Set.uIoc sa sb = Set.Ioc sa sb := Set.uIoc_of_le hab
  have hae : ∀ᵐ p ∂(volume : Measure (Fin 3 → ℝ)),
      IntervalIntegrable (fun s => Fs s p) volume sa sb := by
    filter_upwards [hFsint.prod_left_ae] with p hp
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hp
  have hFTC : ∀ᵐ p ∂(volume : Measure (Fin 3 → ℝ)),
      ∫ s in sa..sb, Fs s p = F sb p - F sa p := by
    filter_upwards [hae] with p hp
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv p s ?_) hp
    rw [Set.uIcc_of_le hab] at hs
    exact hsa.trans_le hs.1
  have hswap : ∫ p, ∫ s in sa..sb, Fs s p = ∫ s in sa..sb, ∫ p, Fs s p := by
    refine (intervalIntegral_integral_swap ?_).symm
    rw [hIoc]
    exact hFsint
  have hJ : Hd.Jbar α η sb - Hd.Jbar α η sa = ∫ s in sa..sb, ∫ p, Fs s p := by
    rw [← hswap, Jbar, Jbar, ← integral_sub (hFint sb ⟨hab, le_rfl⟩) (hFint sa ⟨le_rfl, hab⟩)]
    exact integral_congr_ae (hFTC.mono fun p hp => hp.symm)
  have hint1 : IntervalIntegrable (fun s => ∫ p, Fs s p) volume sa sb :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hFsint.integral_prod_left
  have hint2 : IntervalIntegrable (fun s => -(1 / 28) * ∑ v, Hd.Vbar α η v s) volume sa sb := by
    refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_).const_mul _
    exact integrable_finsetSum _ fun v _ => (hVint v).integral_prod_left
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hstep
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith

end HeatData

end IntegratedDissipation

section LatticeGaussianWeights

lemma gaussian_nonneg' (σ t : ℝ) : 0 ≤ gaussian σ t := by unfold gaussian; positivity

lemma gaussian_le_sup (σ t : ℝ) : gaussian σ t ≤ (√(2 * π * σ))⁻¹ := by
  unfold gaussian
  have : Real.exp (-(t ^ 2) / (2 * σ)) ≤ 1 ∨ σ ≤ 0 := by
    rcases le_or_gt σ 0 with h | h
    · exact Or.inr h
    · left; rw [Real.exp_le_one_iff]; have := sq_nonneg t; rw [neg_div, neg_nonpos]; positivity
  rcases this with h | h
  · exact mul_le_of_le_one_right (by positivity) h
  · have : √(2 * π * σ) = 0 := Real.sqrt_eq_zero'.2 (by nlinarith [Real.pi_pos])
    simp [this]

lemma gaussian_anti {σ : ℝ} (hσ : 0 < σ) {t t' : ℝ} (h : |t| ≤ |t'|) :
    gaussian σ t' ≤ gaussian σ t := by
  unfold gaussian
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (sq_le_sq.2 h) (by positivity)

end LatticeGaussianWeights

section LatticeGaussianSums

lemma integrable_gaussian' {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussian σ) := by
  have := integrable_gaussianD 0 hσ
  rwa [gaussianD_zero] at this

lemma two_div_sqrt_le : 2 * (√(2 * π))⁻¹ ≤ √(2 / π) := by
  rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt (by positivity)]
  field_simp
  ring_nf
  rfl

theorem sum_gweight_le {ι : Type*} [Fintype ι] (u : ι → ℝ) {h σ : ℝ} (hh : 0 < h)
    (hσ : h ^ 2 ≤ σ) (kk : ι → ℤ) (hk : Function.Injective kk) (hu : ∀ i, u i = h * kk i)
    (p : ℝ) :
    ∑ i, gweight u h σ p i ≤ 1 + √(2 / π) := by
  classical
  have hσ0 : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  set g : ℝ → ℝ := fun t => gaussian σ (t - p) with hg
  have hgi : Integrable g := (integrable_gaussian' hσ0).comp_sub_right p
  have hg1 : ∫ t, g t = 1 := by
    simp only [hg]
    rw [integral_sub_right_eq_self (fun t => gaussian σ t) p, integral_gaussian_eq_one hσ0]
  have hgnn : ∀ t, 0 ≤ g t := fun t => gaussian_nonneg' _ _
  have hsep : ∀ i j, i ≠ j → h ≤ |u i - u j| := by
    intro i j hij
    rw [hu, hu, ← mul_sub, abs_mul, abs_of_pos hh]
    have : (1 : ℝ) ≤ |(kk i : ℝ) - kk j| := by
      have h1 : kk i ≠ kk j := fun h => hij (hk h)
      have h2 : (1 : ℤ) ≤ |kk i - kk j| := Int.one_le_abs (sub_ne_zero.2 h1)
      exact_mod_cast h2
    nlinarith
  set far := Finset.univ.filter (fun i => h ≤ |u i - p|)
  set mid := Finset.univ.filter (fun i => ¬ h ≤ |u i - p|)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => h ≤ |u i - p|)]
  set I : ι → Set ℝ := fun i => if p ≤ u i then Set.Ioc (u i - h) (u i) else Set.Ico (u i) (u i + h)
  have hImeas : ∀ i, MeasurableSet (I i) := fun i => by
    simp only [I]; split_ifs; exacts [measurableSet_Ioc, measurableSet_Ico]
  have hIvol : ∀ i, (volume (I i)).toReal = h := fun i => by
    simp only [I]; split_ifs <;> simp [hh.le]
  have hIlow : ∀ i ∈ far, ∀ t ∈ I i, g (u i) ≤ g t := by
    intro i hi t ht
    simp only [far, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hg]
    refine gaussian_anti hσ0 ?_
    simp only [I] at ht
    split_ifs at ht with hpu
    · have : u i - p ≥ h := by rw [abs_of_nonneg (by linarith)] at hi; linarith
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]; linarith [ht.2]
    · have : p - u i ≥ h := by rw [abs_of_neg (by linarith)] at hi; linarith
      rw [abs_of_neg (by linarith [ht.2]), abs_of_neg (by linarith)]; linarith [ht.1]
  have hdisj : Set.Pairwise (↑far) (Function.onFun Disjoint I) := by
    intro i hi j hj hij
    simp only [far, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    have hs := hsep i j hij
    refine Set.disjoint_left.2 fun t hti htj => ?_
    simp only [I] at hti htj
    split_ifs at hti htj with h1 h2 h2
    · rcases le_total (u i) (u j) with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at hs; linarith [hti.2, htj.1]
      · rw [abs_of_nonneg (by linarith)] at hs; linarith [hti.1, htj.2]
    · rw [abs_of_nonneg (by linarith)] at hi
      rw [abs_of_neg (by linarith)] at hj
      linarith [hti.1, htj.2]
    · rw [abs_of_neg (by linarith)] at hi
      rw [abs_of_nonneg (by linarith)] at hj
      linarith [hti.2, htj.1]
    · rcases le_total (u i) (u j) with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at hs; linarith [hti.2, htj.1]
      · rw [abs_of_nonneg (by linarith)] at hs; linarith [hti.1, htj.2]
  have hfar : ∑ i ∈ far, gweight u h σ p i ≤ 1 := by
    calc ∑ i ∈ far, gweight u h σ p i ≤ ∑ i ∈ far, ∫ t in I i, g t := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := setIntegral_ge_of_const_le_real (hImeas i) (by
              simp only [I]; split_ifs <;> simp) (hIlow i hi) hgi.integrableOn
          rw [Measure.real, hIvol i] at this
          simp only [gweight, hg] at this ⊢
          linarith
      _ = ∫ t in ⋃ i ∈ far, I i, g t := (integral_biUnion_finset far (fun i _ => hImeas i) hdisj
            fun i _ => hgi.integrableOn).symm
      _ ≤ ∫ t, g t := setIntegral_le_integral hgi (Eventually.of_forall hgnn)
      _ = 1 := hg1
  have hmid_card : mid.card ≤ 2 := by
    set m0 := ⌊p / h⌋
    have hmaps : ∀ i ∈ mid, kk i ∈ ({m0, m0 + 1} : Finset ℤ) := by
      intro i hi
      simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      rw [hu, abs_lt] at hi
      have h1 : p / h - 1 < kk i := by
        rw [div_sub_one hh.ne', div_lt_iff₀ hh]; linarith [hi.1]
      have h2 : (kk i : ℝ) < p / h + 1 := by
        have : (kk i : ℝ) < (p + h) / h := by rw [lt_div_iff₀ hh]; linarith [hi.2]
        rwa [add_div, div_self hh.ne'] at this
      have hf1 := Int.floor_le (p / h)
      have hf2 := Int.lt_floor_add_one (p / h)
      have a1 : m0 ≤ kk i := by
        have : (m0 : ℝ) - 1 < kk i := by linarith
        have : m0 - 1 < kk i := by exact_mod_cast this
        omega
      have a2 : kk i ≤ m0 + 1 := by
        have : (kk i : ℝ) < m0 + 2 := by linarith
        have : kk i < m0 + 2 := by exact_mod_cast this
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc mid.card ≤ ({m0, m0 + 1} : Finset ℤ).card :=
          Finset.card_le_card_of_injOn kk (fun i hi => hmaps i hi) (fun i _ j _ h => hk h)
      _ ≤ 2 := Finset.card_le_two
  have hmid : ∑ i ∈ mid, gweight u h σ p i ≤ 2 * (√(2 * π))⁻¹ := by
    have hterm : ∀ i, gweight u h σ p i ≤ (√(2 * π))⁻¹ := by
      intro i
      simp only [gweight]
      have h1 := gaussian_le_sup σ (u i - p)
      have h2 : h * (√(2 * π * σ))⁻¹ ≤ (√(2 * π))⁻¹ := by
        rw [Real.sqrt_mul (by positivity), mul_inv, ← mul_assoc, mul_comm h, mul_assoc]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [mul_inv_le_iff₀ (Real.sqrt_pos.2 hσ0), one_mul]
        exact Real.le_sqrt_of_sq_le hσ
      calc h * gaussian σ (u i - p) ≤ h * (√(2 * π * σ))⁻¹ :=
            mul_le_mul_of_nonneg_left h1 hh.le
        _ ≤ _ := h2
    calc ∑ i ∈ mid, gweight u h σ p i ≤ ∑ _i ∈ mid, (√(2 * π))⁻¹ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = mid.card * (√(2 * π))⁻¹ := by simp
      _ ≤ 2 * (√(2 * π))⁻¹ := by
          gcongr
          exact_mod_cast hmid_card
  have := two_div_sqrt_le
  linarith

end LatticeGaussianSums

section PlaneIntegral

lemma plane_integral_prod01 {k f g : ℝ → ℝ} (hk : Continuous k) (hf : Continuous f)
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  set F : (Fin 3 → ℝ) → ℝ := fun p => k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1))
  set F' : ℝ × (Fin 2 → ℝ) → ℝ := fun z => k (z.2 0 + z.2 1 + z.1) * (f (z.2 0) * g (z.2 1))
  have hFF : ∀ z, F (e.symm z) = F' z := fun z => rfl
  have hF'c : Continuous F' := by
    simp only [F']
    fun_prop
  have hprod : Integrable (fun q : Fin 2 → ℝ => |f (q 0)| * |g (q 1)|) := by
    have := Integrable.fintype_prod (f := ![fun t => |f t|, fun t => |g t|]) (μ := fun _ : Fin 2 =>
        (volume : Measure ℝ)) (fun i => by
        fin_cases i
        · exact hfi.abs
        · exact hgi.abs)
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact this
  have hF' : Integrable F' ((volume : Measure ℝ).prod volume) := by
    rw [integrable_prod_iff' hF'c.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun q => ?_, ?_⟩
    · change Integrable (fun x => k (q 0 + q 1 + x) * (f (q 0) * g (q 1)))
      exact (hki.comp_add_left (q 0 + q 1)).mul_const (f (q 0) * g (q 1))
    · have : (fun q : Fin 2 → ℝ => ∫ x, ‖F' (x, q)‖) =
          fun q => (∫ t, |k t|) * (|f (q 0)| * |g (q 1)|) := by
        funext q
        simp only [F', norm_mul, Real.norm_eq_abs]
        rw [integral_mul_const, integral_add_left_eq_self (fun t => |k t|)]
      rw [this]
      exact hprod.const_mul _
  have hF : Integrable F := by
    rw [← hmp.integrable_comp_emb e.symm.measurableEmbedding]
    exact hF'
  refine ⟨hF, ?_⟩
  rw [← hmp.integral_comp' (g := F)]
  simp only [hFF]
  rw [integral_prod_symm _ hF']
  have : ∀ q : Fin 2 → ℝ, ∫ x, F' (x, q) = (∫ t, k t) * (f (q 0) * g (q 1)) := by
    intro q
    simp only [F']
    rw [integral_mul_const, integral_add_left_eq_self k]
  simp only [this]
  rw [integral_const_mul]
  congr 1
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (f := ![f, g]) (μ := fun _ : Fin 2 => (volume :
      Measure ℝ))
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

theorem plane_integral_prod {k f g : ℝ → ℝ} (hk : Continuous k) (hf : Continuous f)
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g)
    {a b : Fin 3} (hab : a ≠ b) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p a) * g (p b))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p a) * g (p b)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by
  have hτ : ∀ a b : Fin 3, a ≠ b → ∃ τ : Equiv.Perm (Fin 3), τ 0 = a ∧ τ 1 = b := by decide
  obtain ⟨τ, h0, h1⟩ := hτ a b hab
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) τ
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) τ
  have hE : ∀ (q : Fin 3 → ℝ) (c : Fin 3), E q c = q (τ.symm c) := fun q c => by
    simp [E, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hsum : ∀ q : Fin 3 → ℝ, E q 0 + E q 1 + E q 2 = q 0 + q 1 + q 2 := by
    intro q
    simp only [hE]
    have := Equiv.sum_comp τ.symm q
    simp only [Fin.sum_univ_three] at this
    exact this
  have ha : ∀ q : Fin 3 → ℝ, E q a = q 0 := fun q => by rw [hE, ← h0, Equiv.symm_apply_apply]
  have hb : ∀ q : Fin 3 → ℝ, E q b = q 1 := fun q => by rw [hE, ← h1, Equiv.symm_apply_apply]
  obtain ⟨hI, hV⟩ := plane_integral_prod01 hk hf hg hki hfi hgi
  set F : (Fin 3 → ℝ) → ℝ := fun p => k (p 0 + p 1 + p 2) * (f (p a) * g (p b))
  have hFE : ∀ q, F (E q) = k (q 0 + q 1 + q 2) * (f (q 0) * g (q 1)) := fun q => by
    simp only [F, hsum, ha, hb]
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb E.measurableEmbedding]
    have : F ∘ E = fun q => k (q 0 + q 1 + q 2) * (f (q 0) * g (q 1)) := funext hFE
    rw [this]; exact hI
  · rw [← hmp.integral_comp' (g := F)]
    simp only [hFE]
    exact hV

end PlaneIntegral

section InitialEnergy

lemma holder_three_halves {κ : Type*} (s : Finset κ) (μ a : κ → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ s, μ k * a k) ^ (3 / 2 : ℝ) ≤ (∑ k ∈ s, μ k) ^ (1 / 2 : ℝ) * ∑ k ∈ s, μ k * a k ^ (3
      / 2 : ℝ) := by
  have h := Real.inner_le_weight_mul_Lp_of_nonneg s (p := 3 / 2) (by norm_num) μ a hμ ha
  have hX : 0 ≤ ∑ k ∈ s, μ k * a k := Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (ha k)
  have hQ : 0 ≤ ∑ k ∈ s, μ k := Finset.sum_nonneg fun k _ => hμ k
  have hY : 0 ≤ ∑ k ∈ s, μ k * a k ^ (3 / 2 : ℝ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (Real.rpow_nonneg (ha k) _)
  have := Real.rpow_le_rpow hX h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hY _), ← Real.rpow_mul hQ,
    ← Real.rpow_mul hY] at this
  norm_num at this
  exact this

lemma hsSq_fromCols {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) :
    hsSq (Matrix.fromCols A B) = hsSq A + hsSq B := by
  simp [hsSq, Fintype.sum_sum_type, Finset.sum_add_distrib]

lemma hsSq_conjTranspose {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq Aᴴ = hsSq A := by
  unfold hsSq; rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

/-- The cube of the lattice-weighted entrywise norm of input matrix `v`. -/
def nCube (v : Fin 3) : ℝ := Hd.h ^ 2 * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3

theorem W_cube_le (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (h1 : ∑ i, Hd.w p σ v i ≤ M) (h2 : ∑ j, Hd.w p σ (v + 1) j ≤ M) :
    hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤ M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ
      (v + 1) j := by
  set w := Hd.w p σ v
  set w' := Hd.w p σ (v + 1)
  have hw : ∀ i, 0 ≤ w i := fun i => gweight_nonneg _ hh _ _ i
  have hw' : ∀ j, 0 ≤ w' j := fun j => gweight_nonneg _ hh _ _ j
  have hsq : ∀ k i, Hd.sqw p σ k i ^ 2 = Hd.w p σ k i := fun k i =>
    Real.sq_sqrt (gweight_nonneg _ hh _ _ i)
  have hW : hsSq (Hd.W p σ v) = ∑ z : ι × ι, (w z.1 * w' z.2) * ‖Hd.A v z.1 z.2‖ ^ 2 := by
    rw [hsSq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [W, rdiag_mul_mul_rdiag_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, hsq, hsq]
    ring
  have hH := holder_three_halves Finset.univ (fun z : ι × ι => w z.1 * w' z.2) (fun z => ‖Hd.A v z.1
      z.2‖ ^ 2) (fun z => mul_nonneg (hw _) (hw' _)) (fun z => sq_nonneg _)
  rw [← hW] at hH
  have hQ : ∑ z : ι × ι, w z.1 * w' z.2 = (∑ i, w i) * (∑ j, w' j) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hQM : (∑ z : ι × ι, w z.1 * w' z.2) ^ (1 / 2 : ℝ) ≤ M := by
    rw [hQ, ← Real.sqrt_eq_rpow, Real.sqrt_le_left hM]
    have a1 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
    have a2 : 0 ≤ ∑ j, w' j := Finset.sum_nonneg fun j _ => hw' j
    nlinarith [mul_le_mul h1 h2 a2 hM]
  have hpow : ∀ z : ι × ι, (‖Hd.A v z.1 z.2‖ ^ 2) ^ (3 / 2 : ℝ) = ‖Hd.A v z.1 z.2‖ ^ 3 := by
    intro z
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simp only [hpow] at hH
  have hS : 0 ≤ ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 :=
    Finset.sum_nonneg fun z _ => by have := hw z.1; have := hw' z.2; positivity
  calc hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ)
      ≤ (∑ z : ι × ι, w z.1 * w' z.2) ^ (1 / 2 : ℝ) *
          ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 := hH
    _ ≤ M * ∑ z : ι × ι, w z.1 * w' z.2 * ‖Hd.A v z.1 z.2‖ ^ 3 := by gcongr
    _ = _ := by
      rw [Fintype.sum_prod_type]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

theorem energy_le_W (p σ : Fin 3 → ℝ) (v : Fin 3) :
    Hd.e p σ 0 v ≤ √2 * (hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) + hsSq (Hd.W p σ (v - 1)) ^ (3 / 2 :
      ℝ)) := by
  have h1 : Hd.e p σ 0 v ≤ hsSq (Hd.R p σ v) ^ (3 / 2 : ℝ) := by
    rw [e, energyReg_zero, T]
    exact energy_conjTranspose_mul_self_le _
  have h2 : hsSq (Hd.R p σ v) = hsSq (Hd.W p σ v) + hsSq (Hd.W p σ (v - 1)) := by
    rw [R, rowMat, hsSq_fromCols, hsSq_conjTranspose]
  have h3 := holder_three_halves Finset.univ (fun _ : Fin 2 => (1 : ℝ))
    ![hsSq (Hd.W p σ v), hsSq (Hd.W p σ (v - 1))] (fun _ => zero_le_one)
    (fun k => by fin_cases k <;> exact hsSq_nonneg _)
  simp only [Fin.sum_univ_two, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h3
  rw [show (1 + 1 : ℝ) ^ (1 / 2 : ℝ) = √2 by rw [Real.sqrt_eq_rpow]; norm_num] at h3
  rw [h2] at h1
  exact h1.trans h3

end HeatData

end InitialEnergy

section InitialEnergyBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_gaussian' (σ : ℝ) : Continuous (gaussian σ) := by
  have := continuous_gaussianD 0 σ
  rwa [gaussianD_zero] at this

lemma integral_weight_line (u h σ : ℝ) (hσ : 0 < σ) : ∫ t, h * gaussian σ (u - t) = h := by
  rw [integral_const_mul, integral_sub_left_eq_self (fun t => gaussian σ t) volume u,
    integral_gaussian_eq_one hσ, mul_one]

lemma integrable_weight_line (u h σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t => h * gaussian σ (u - t)) := ((integrable_gaussian' hσ).comp_sub_left
        u).const_mul h

namespace HeatData

variable (Hd : HeatData ι)

omit [Fintype ι] [DecidableEq ι] in
lemma plane_integral_weights (α : Fin 3 → ℝ) (hα : ∀ k, 0 < α k) {β s : ℝ} (hβ : 0 < β)
    (hs : 0 < s) (v : Fin 3) (i j : ι) :
    Integrable (fun p : Fin 3 → ℝ => Gm β 0 s p * (Hd.w p (HeatData.sig α s) v i * Hd.w p
      (HeatData.sig α s) (v + 1) j)) ∧ ∫ p : Fin 3 → ℝ, Gm β 0 s p * (Hd.w p (HeatData.sig α s) v
      i * Hd.w p (HeatData.sig α s) (v + 1) j) = Hd.h ^ 2 := by
  have hσ : ∀ k, 0 < HeatData.sig α s k := fun k => mul_pos (hα k) hs
  obtain ⟨hI, hV⟩ := plane_integral_prod (k := gaussian (β * s)) (f := fun t => Hd.h * gaussian
      (HeatData.sig α s v) (Hd.u i - t)) (g := fun t => Hd.h * gaussian (HeatData.sig α s (v + 1))
      (Hd.u j - t)) (continuous_gaussian' _) (continuous_const.mul ((continuous_gaussian' _).comp
      (continuous_const.sub continuous_id))) (continuous_const.mul ((continuous_gaussian' _).comp
      (continuous_const.sub continuous_id))) (integrable_gaussian' (mul_pos hβ hs))
      (integrable_weight_line _ _ _ (hσ v)) (integrable_weight_line _ _ _ (hσ _)) (fin3_ne_succ v)
  have hG : ∀ p, Gm β 0 s p = gaussian (β * s) (p 0 + p 1 + p 2) := fun p => by
    simp [Gm, gaussianD_zero]
  refine ⟨?_, ?_⟩
  · simp only [hG]; exact hI
  · simp only [hG]
    rw [show (fun p : Fin 3 → ℝ => gaussian (β * s) (p 0 + p 1 + p 2) * (Hd.w p (HeatData.sig α s) v
        i * Hd.w p (HeatData.sig α s) (v + 1) j)) =
        fun p => gaussian (β * s) (p 0 + p 1 + p 2) * ((fun t => Hd.h * gaussian (HeatData.sig α s
            v) (Hd.u i - t)) (p v) * (fun t => Hd.h * gaussian (HeatData.sig α s (v + 1)) (Hd.u j -
            t)) (p (v + 1)))
        from rfl, hV, integral_gaussian_eq_one (mul_pos hβ hs),
      integral_weight_line _ _ _ (hσ v), integral_weight_line _ _ _ (hσ _)]
    ring

theorem Jbar_zero_le (hh : 0 < Hd.h) (kk : ι → ℤ) (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (α : Fin 3 → ℝ) (hα : ∀ k, 1 ≤ α k) {s : ℝ}
    (hs : Hd.h ^ 2 ≤ s) :
    Hd.Jbar α 0 s ≤ 2 * √2 * (1 + √(2 / π)) * ∑ v, Hd.nCube v := by
  set M := 1 + √(2 / π)
  set β : ℝ := 1 / 10
  have hβ : 0 < β := by norm_num
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα k)
  set σ := HeatData.sig α s
  have hσh : ∀ k, Hd.h ^ 2 ≤ σ k := fun k => by
    simp only [σ, HeatData.sig]; nlinarith [hα k]
  have hsum : ∀ (p : Fin 3 → ℝ) k, ∑ i, Hd.w p σ k i ≤ M := fun p k =>
    sum_gweight_le Hd.u hh (hσh k) kk hk hu (p k)
  have hM : 0 ≤ M := by positivity
  set c : Fin 3 → ι → ι → ℝ := fun v i j => 2 * √2 * M * ‖Hd.A v i j‖ ^ 3
  set B : (Fin 3 → ℝ) → ℝ := fun p => ∑ v, ∑ i, ∑ j,
    c v i j * (Gm β 0 s p * (Hd.w p σ v i * Hd.w p σ (v + 1) j))
  have hpw := fun v i j => Hd.plane_integral_weights α hα0 hβ hs0 v i j
  have hBint : Integrable B := integrable_finsetSum _ fun v _ =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpw v i j).1.const_mul _
  have hBval : ∫ p, B p = 2 * √2 * M * ∑ v, Hd.nCube v := by
    simp only [B]
    rw [integral_finsetSum _ fun v _ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hpw v i j).1.const_mul _]
    simp_rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hpw _ i j).1.const_mul _]
    simp_rw [integral_finsetSum _ fun j _ => (hpw _ _ j).1.const_mul _]
    simp_rw [integral_const_mul, (hpw _ _ _).2]
    simp only [c, nCube, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hG0 : ∀ p, 0 ≤ Gm β 0 s p := fun p => by
    simp only [Gm, gaussianD_zero]; exact gaussian_nonneg' _ _
  have hpt : ∀ p, Gm β 0 s p * ∑ v, Hd.qE α 0 v s p ≤ B p := by
    intro p
    have hW : ∀ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤
        M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ (v + 1) j := fun v =>
      Hd.W_cube_le hh.le p σ v hM (hsum p v) (hsum p (v + 1))
    have hE : ∀ v, Hd.qE α 0 v s p ≤
        √2 * (hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) + hsSq (Hd.W p σ (v - 1)) ^ (3 / 2 : ℝ)) :=
      fun v => Hd.energy_le_W p σ v
    have e02 : (0 : Fin 3) - 1 = 2 := rfl
    have e12 : (1 : Fin 3) - 1 = 0 := rfl
    have e22 : (2 : Fin 3) - 1 = 1 := rfl
    have hsumE : ∑ v, Hd.qE α 0 v s p ≤
        2 * √2 * ∑ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) := by
      have := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hE v
      rw [Fin.sum_univ_three, Fin.sum_univ_three, e02, e12, e22] at this
      simp only [Fin.sum_univ_three]
      linarith
    have hsumW : 2 * √2 * ∑ v, hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤
        ∑ v, ∑ i, ∑ j, c v i j * (Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      calc 2 * √2 * hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ)
          ≤ 2 * √2 * (M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
            gcongr; exact hW v
        _ = _ := by
            simp only [c, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have : B p = Gm β 0 s p * ∑ v, ∑ i, ∑ j, c v i j * (Hd.w p σ v i * Hd.w p σ (v + 1) j) := by
      simp only [B, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (hsumE.trans hsumW) (hG0 p)
  have hnn : ∀ p, 0 ≤ Gm β 0 s p * ∑ v, Hd.qE α 0 v s p := fun p =>
    mul_nonneg (hG0 p) (Finset.sum_nonneg fun v _ =>
      (energyReg_bounds (Matrix.posSemidef_conjTranspose_mul_self _) le_rfl).1)
  calc Hd.Jbar α 0 s = ∫ p, Gm β 0 s p * ∑ v, Hd.qE α 0 v s p := rfl
    _ ≤ ∫ p, B p := integral_mono_of_nonneg (Eventually.of_forall hnn) hBint (Eventually.of_forall
        hpt)
    _ = _ := hBval

end HeatData

end InitialEnergyBound

end

end Triangular.Auto
