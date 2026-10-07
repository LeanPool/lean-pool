/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingMain
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Input

/-! # Symmetry of the completed second derivative -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Foundation.Euclidean

private lemma pressureNewtonianPotential_mixedSecond_commute
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (i j : Fin 3) :
    mixedSecond (pressureNewtonianPotential F) i j =
      pressureNewtonianPotential (mixedSecond F i j) := by
  have hfirst : spatialDeriv (pressureNewtonianPotential F) j =
      pressureNewtonianPotential (spatialDeriv F j) := by
    funext x
    rw [pressureNewtonianPotential_spatialDeriv_convolution hF hFc j x,
      pressureNewtonianPotential]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hsecond : spatialDeriv (pressureNewtonianPotential (spatialDeriv F j)) i =
      pressureNewtonianPotential (spatialDeriv (spatialDeriv F j) i) := by
    funext x
    rw [pressureNewtonianPotential_spatialDeriv_convolution
      (contDiff_spatialDeriv_smooth hF j)
      (hFc.fderiv_apply (𝕜 := ℝ) (basisVec j)) i x,
      pressureNewtonianPotential]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  funext x
  change spatialDeriv (spatialDeriv (pressureNewtonianPotential F) j) i x = _
  rw [hfirst, hsecond]
  rfl

private theorem smooth_rieszSecond_pairing_symmetric
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (i j : Fin 3) :
    (∫ x, mixedSecond (pressureNewtonianPotential f) i j x * g x) =
      ∫ x, f x * mixedSecond (pressureNewtonianPotential g) i j x := by
  have hleft := pressure_newtonian_derivative_potential_smooth_pairing
    (i := i) (j := j) hf hfc hg hgc
  have hright := pressureNewtonianDerivativePotential_pairing_potential
    (i := i) (j := j) (hf.continuous.integrable_of_hasCompactSupport hfc)
      hfc hg hgc
  calc
    (∫ x, mixedSecond (pressureNewtonianPotential f) i j x * g x) =
        ∫ x, pressureNewtonianDerivativePotential i f x * spatialDeriv g j x :=
      hleft.symm
    _ = ∫ x, f x * pressureNewtonianPotential (mixedSecond g i j) x := hright
    _ = ∫ x, f x * mixedSecond (pressureNewtonianPotential g) i j x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(pressureNewtonianPotential_mixedSecond_commute hg hgc i j).symm]

private theorem integral_eq_inner_l2
    {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    ∫ x, f x * g x = inner ℝ (MemLp.toLp f hf) (MemLp.toLp g hg) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [RCLike.inner_apply]
  ring

private theorem rieszSecondL2Extension_selfAdjoint_on_smooth_left
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (v : rieszSecondL2) :
    inner ℝ (rieszSecondL2Extension hL2
      (MemLp.toLp f (hf.continuous.memLp_of_hasCompactSupport hfc))) v =
    inner ℝ (MemLp.toLp f (hf.continuous.memLp_of_hasCompactSupport hfc))
      (rieszSecondL2Extension hL2 v) := by
  let u : rieszSecondL2 := MemLp.toLp f
    (hf.continuous.memLp_of_hasCompactSupport hfc)
  let A : rieszSecondL2 → ℝ := fun w => inner ℝ
    (rieszSecondL2Extension hL2 u) w
  let B : rieszSecondL2 → ℝ := fun w => inner ℝ u
    (rieszSecondL2Extension hL2 w)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hclosed : IsClosed {w : rieszSecondL2 | A w = B w} :=
    isClosed_eq hAcont hBcont
  have hdense : DenseRange
      (fun z : {w : rieszSecondL2 // ∃ G : Vec3 → ℝ,
        w =ᵐ[volume] G ∧ HasCompactSupport G ∧ ContDiff ℝ (⊤ : ℕ∞) G} =>
        (z : rieszSecondL2)) :=
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Vec3))
      (by norm_num)).denseRange_val
  have hEq : A v = B v := by
    apply isClosed_property hdense hclosed
    rintro ⟨w, hw⟩
    rcases hw with ⟨G, hwG, hGc, hG⟩
    have hGmem : MemLp G (2 : ℝ≥0∞) volume :=
      hG.continuous.memLp_of_hasCompactSupport hGc
    have hw' : w = MemLp.toLp G hGmem := by
      apply Lp.ext
      exact hwG.trans hGmem.coeFn_toLp.symm
    change A w = B w
    rw [hw']
    obtain ⟨hTmemF, hTF⟩ := rieszSecondL2Extension_smooth_hessian hL2 hf hfc
    obtain ⟨hTmemG, hTG⟩ := rieszSecondL2Extension_smooth_hessian hL2 hG hGc
    dsimp only [A, B, u]
    rw [hTF, hTG]
    rw [← integral_eq_inner_l2 hTmemF hGmem,
      ← integral_eq_inner_l2
        (hf.continuous.memLp_of_hasCompactSupport hfc) hTmemG]
    exact smooth_rieszSecond_pairing_symmetric hf hfc hG hGc i j
  simpa only [A, B, u] using hEq

/-- The completed `L²` second derivative is symmetric for the real inner product. -/
theorem rieszSecondL2Extension_selfAdjoint {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u v : rieszSecondL2) :
    inner ℝ (rieszSecondL2Extension hL2 u) v =
      inner ℝ u (rieszSecondL2Extension hL2 v) := by
  let A : rieszSecondL2 → ℝ := fun w =>
    inner ℝ (rieszSecondL2Extension hL2 w) v
  let B : rieszSecondL2 → ℝ := fun w =>
    inner ℝ w (rieszSecondL2Extension hL2 v)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hclosed : IsClosed {w : rieszSecondL2 | A w = B w} :=
    isClosed_eq hAcont hBcont
  have hdense : DenseRange
      (fun z : {w : rieszSecondL2 // ∃ F : Vec3 → ℝ,
        w =ᵐ[volume] F ∧ HasCompactSupport F ∧ ContDiff ℝ (⊤ : ℕ∞) F} =>
        (z : rieszSecondL2)) :=
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Vec3))
      (by norm_num)).denseRange_val
  have hEq : A u = B u := by
    apply isClosed_property hdense hclosed
    rintro ⟨w, hw⟩
    rcases hw with ⟨F, hwF, hFc, hF⟩
    have hFmem : MemLp F (2 : ℝ≥0∞) volume :=
      hF.continuous.memLp_of_hasCompactSupport hFc
    have hw' : w = MemLp.toLp F hFmem := by
      apply Lp.ext
      exact hwF.trans hFmem.coeFn_toLp.symm
    change A w = B w
    rw [hw']
    exact rieszSecondL2Extension_selfAdjoint_on_smooth_left hL2 hF hFc v
  simpa only [A, B] using hEq

/-- The raw representative has the symmetric integral pairing on `L²` data. -/
theorem rieszSecondL2RawOperator_integral_mul_commute {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    ∫ x, rieszSecondL2RawOperator hL2 f x * g x =
      ∫ x, f x * rieszSecondL2RawOperator hL2 g x := by
  have hTf := (rieszSecondL2RawOperator_ae_eq hL2 hf).trans
    (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 (hf.toLp f))
  have hTg := (rieszSecondL2RawOperator_ae_eq hL2 hg).trans
    (rieszSecondL2MeasurableOperator_ae_eq_extension hL2 (hg.toLp g))
  have hTfmem : MemLp (rieszSecondL2RawOperator hL2 f) (2 : ℝ≥0∞) volume :=
    memLp_congr_ae hTf |>.2 (Lp.memLp (rieszSecondL2Extension hL2 (hf.toLp f)))
  have hTgmem : MemLp (rieszSecondL2RawOperator hL2 g) (2 : ℝ≥0∞) volume :=
    memLp_congr_ae hTg |>.2 (Lp.memLp (rieszSecondL2Extension hL2 (hg.toLp g)))
  have hTfLp : hTfmem.toLp (rieszSecondL2RawOperator hL2 f) =
      rieszSecondL2Extension hL2 (hf.toLp f) := by
    apply Lp.ext
    exact hTfmem.coeFn_toLp.trans hTf
  have hTgLp : hTgmem.toLp (rieszSecondL2RawOperator hL2 g) =
      rieszSecondL2Extension hL2 (hg.toLp g) := by
    apply Lp.ext
    exact hTgmem.coeFn_toLp.trans hTg
  calc
    ∫ x, rieszSecondL2RawOperator hL2 f x * g x =
        inner ℝ (hTfmem.toLp (rieszSecondL2RawOperator hL2 f))
          (hg.toLp g) := integral_eq_inner_l2 hTfmem hg
    _ = inner ℝ (rieszSecondL2Extension hL2 (hf.toLp f)) (hg.toLp g) :=
      congrArg (fun w : rieszSecondL2 => inner ℝ w (hg.toLp g)) hTfLp
    _ = inner ℝ (hf.toLp f) (rieszSecondL2Extension hL2 (hg.toLp g)) :=
      rieszSecondL2Extension_selfAdjoint hL2 (hf.toLp f) (hg.toLp g)
    _ = inner ℝ (hf.toLp f)
          (hTgmem.toLp (rieszSecondL2RawOperator hL2 g)) :=
      congrArg (inner ℝ (hf.toLp f)) hTgLp.symm
    _ = ∫ x, f x * rieszSecondL2RawOperator hL2 g x :=
      (integral_eq_inner_l2 hf hTgmem).symm

end CKN.Foundation.Euclidean
