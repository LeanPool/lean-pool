/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorCellInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputGradMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeSpatial
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoGrid

/-!
# GammaTenStripPathwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper.

# A `K`-uniform integrable majorant for the two strip fourth energies

ABK26, `e.def.w`, `e.Fz.def`, `e.nablaw.in.L.eight`, read at the closure's own
corrector families along the increment path.

## What is proved

`exists_strip_fourthEnergy_majorant` produces **one** real number `B >= 0`,
chosen before the localization scale `K`, such that for every `K` beyond the
strip top `n + h` there is a sample function `G >= 0`, integrable for the
cutoff-sample law, with `E[G] <= B`, dominating pathwise **both** shifted fourth
energies

```
  fint_{cu_K} |e' + grad w_D|^4      and      fint_{cu_K} |e + F_z|^4 ,
```

where `w_D` is `Closure.closureDirichletAlong` and `F_z` is the flux leg
`neumannFluxField` built from `Closure.closureNeumannAlong`.

The point of the statement shape is that `B` is chosen **before** `K`: the
expectation bound is uniform in the localization scale.

## The route

1. **General-direction stream forcing.**  `cubeEuclideanLpNorm_streamForcing_le`
   of `Corrector.FreshShellL8` is stated for directions of Euclidean length at
   most one.  `cubeEuclideanLpNorm_streamForcing_le_of_le` below removes that
   normalization by the exact homogeneity
   `streamForcing s omega n m e = streamForcing (s * c) omega n m (c⁻¹ • e)`,
   at the cost of the factor `c` for any `c` dominating both `1` and `|e|`.
2. **Calderon--Zygmund, pathwise.**
   `Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le`, instantiated at
   `Q = cu_K` and at the two weak-solution facts of `Closure.SplitProducerFold`,
   bounds both gradient `L^8` norms by `A * t`, where `t` is the fresh-shell
   `L^8` norm and `A` is a constant free of `K` and of the sample.
3. **`L^4 <= L^8` and Minkowski.**
   `originCubeFourthEnergy_le_cubeEuclideanLpNorm_eight_pow_four` and
   `cubeEuclideanLpNorm_add_le` turn that into the pathwise majorant
   `8 (a0^4 + (a1 t)^4)` for both shifted fields, with `a0`, `a1` free of `K`
   and of the sample.
4. **The `K`-uniform quartic moment.**
   `Closure.Step5InputGradMoment.exists_integral_streamIncrementLpNorm_eight_pow_four_le`
   bounds `E[t^4]` by a quantity **free of `K`**, which is exactly what lets `B`
   be produced before `K`.

## No regime, no normalization

There is no `inductionState`, no `M.gamma <= gamma0`, no `cstar` bound, no
`|e| <= 1`, no `|e'| <= 1` and no `0 < h`.  The degenerate depth `h = 0` is
handled honestly: the fresh-shell increment sums over `Finset.Ioc n n`, which is
empty, so the forcing vanishes identically and the majorant degenerates to a
constant.

## References

* ABK26, `e.def.w`; `e.Fz.def`; `e.nablaw.in.L.eight`; `e.km.kn.Lp`.
* None of the three enters a statement below: the majorant here is pathwise on
  the whole localization cube and carries no mesh at all.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

/-! ## Two elementary real inequalities -/

/-- `(x + y)^4 <= 8 (x^4 + y^4)`. -/
private theorem add_pow_four_le_eight (x y : ℝ) :
    (x + y) ^ (4 : ℕ) ≤ 8 * (x ^ (4 : ℕ) + y ^ (4 : ℕ)) := by
  have h1 : (x + y) ^ (2 : ℕ) ≤ 2 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (x - y)]
  have h2 : (x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) ≤ 2 * (x ^ (4 : ℕ) + y ^ (4 : ℕ)) := by
    nlinarith [sq_nonneg (x ^ (2 : ℕ) - y ^ (2 : ℕ))]
  have h0 : (0 : ℝ) ≤ (x + y) ^ (2 : ℕ) := sq_nonneg _
  calc (x + y) ^ (4 : ℕ) = ((x + y) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ ≤ (2 * (x ^ (2 : ℕ) + y ^ (2 : ℕ))) ^ (2 : ℕ) :=
      pow_le_pow_left₀ h0 h1 2
    _ = 4 * ((x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ)) := by ring
    _ ≤ 4 * (2 * (x ^ (4 : ℕ) + y ^ (4 : ℕ))) := by linarith
    _ = 8 * (x ^ (4 : ℕ) + y ^ (4 : ℕ)) := by ring

/-- Squares may be cancelled between nonnegative reals. -/
private theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b := by
  have hsqrt := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hsqrt

/-! ## The Euclidean cube norm of a constant field -/

/-- The Euclidean volume-normalized `L^p` norm of a constant vector field is the
Euclidean length of that constant. -/
theorem cubeEuclideanLpNorm_const {d : ℕ} (Q : TriadicCube d) {p : ℝ≥0∞}
    (hp : p ≠ 0) (c : Vec d) :
    cubeEuclideanLpNorm Q p (fun _ => c) = vecNorm c := by
  have hunfold : cubeEuclideanLpNorm Q p (fun _ : Vec d => c) =
      cubeLpNorm Q p (fun _ : Vec d => vecNorm c) := rfl
  rw [hunfold, cubeLpNorm_const Q p (vecNorm c) hp, Real.norm_eq_abs,
    abs_of_nonneg (vecNorm_nonneg c)]

/-- The Euclidean length of the zero field. -/
private theorem vecNorm_zero_vec {d : ℕ} : vecNorm (0 : Vec d) = 0 := by
  rw [Corrector.vecNorm_eq_sqrt_vecNormSq]
  have hz : vecNormSq (0 : Vec d) = 0 := by
    change ∑ i, (0 : Vec d) i * (0 : Vec d) i = 0
    simp
  rw [hz, Real.sqrt_zero]

/-! ## The stream forcing in a general direction -/

/-- **Step 1: the `L^8` bound on the forcing of `e.def.w` in an arbitrary
direction.**

`Corrector.cubeEuclideanLpNorm_streamForcing_le` is stated for directions of
Euclidean length at most one.  Since `streamForcing` is linear in the direction,
that normalization can be traded for any `c` dominating both `1` and `|e|`:

```
  ‖ s (k_m - k_n) e ‖_{L8bar(cu_l)}  <=  s c ‖k_m - k_n‖_{L8bar(cu_l)} .
```

on `0 <= s`, `1 <= c` and `|e| <= c` only; no regime, no model. -/
theorem cubeEuclideanLpNorm_streamForcing_le_of_le {d : ℕ} {sinv : ℝ}
    (hsinv : 0 ≤ sinv) (l n m : ℤ) (omega : ShellSeq d) {e : Vec d} {c : ℝ}
    (hc1 : (1 : ℝ) ≤ c) (hce : vecNorm e ≤ c) :
    cubeEuclideanLpNorm (originCube d l) 8 (streamForcing sinv omega n m e) ≤
      sinv * c * Provider.Stream.streamIncrementLpNorm 8 l n m omega := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hid : streamForcing sinv omega n m e =
      streamForcing (sinv * c) omega n m (c⁻¹ • e) := by
    funext x
    simp only [streamForcing, matVecMul_smul, smul_smul]
    congr 1
    field_simp
  have he : vecNorm (c⁻¹ • e) ≤ 1 := by
    rw [vecNorm_smul, abs_of_nonneg (inv_nonneg.2 hcpos.le)]
    calc c⁻¹ * vecNorm e ≤ c⁻¹ * c :=
          mul_le_mul_of_nonneg_left hce (inv_nonneg.2 hcpos.le)
      _ = 1 := inv_mul_cancel₀ hcne
  rw [hid]
  exact cubeEuclideanLpNorm_streamForcing_le (mul_nonneg hsinv hcpos.le) l n m omega he

/-- **The degenerate depth.**  The finite stream increment sums over `Ioc n n`,
which is empty, so the forcing of `e.def.w` at zero depth vanishes
identically. -/
theorem streamForcing_self_eq_zero {d : ℕ} (sinv : ℝ) (omega : ShellSeq d)
    (n : ℤ) (e : Vec d) :
    streamForcing sinv omega n n e = fun _ => (0 : Vec d) := by
  funext x
  have hz : Cutoff.finiteShellIncrement omega n n x = 0 := by
    simp [Cutoff.finiteShellIncrement_apply]
  have hmv : matVecMul (0 : Mat d) e = 0 := by
    funext i
    simp [matVecMul]
  simp only [streamForcing, hz, hmv, smul_zero]

/-! ## The spatial step, at a shifted field -/

/-- **Step 3, packaged.**  If the Euclidean length of the constant `c` is at most
`a` and the Euclidean `L^8` norm of `u` on `cu_K` is at most `b`, then the fourth
energy of the shifted field `c + u` is at most `8 (a^4 + b^4)`.

on the `L^8` membership `hu` and on the two numeric bounds. -/
private theorem originCubeFourthEnergy_shift_le {d : ℕ} (K : ℤ) (c : Vec d)
    (u : Vec d → Vec d)
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K)))
    {a b : ℝ} (ha : vecNorm c ≤ a)
    (hb : cubeEuclideanLpNorm (originCube d K) 8 u ≤ b) :
    originCubeFourthEnergy K (fun x => c + u x) ≤
      8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure (originCube d K)) :=
    ⟨by simp [normalizedCubeMeasure_apply_univ (originCube d K)]⟩
  have hcm : MemLp (fun _ : Vec d => c) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) := memLp_const c
  have hcn : MemLp (fun x : Vec d => vecNorm ((fun _ : Vec d => c) x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) :=
    memLp_vecNorm_eight_of_memLp_eight _ hcm
  have hun : MemLp (fun x => vecNorm (u x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) :=
    memLp_vecNorm_eight_of_memLp_eight _ hu
  have hsum : MemLp (fun x => vecNorm ((fun y => c + u y) x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) :=
    memLp_vecNorm_eight_of_memLp_eight _ (hcm.add hu)
  have h1 := originCubeFourthEnergy_le_cubeEuclideanLpNorm_eight_pow_four K
    (fun x => c + u x) hsum
  have h2 : cubeEuclideanLpNorm (originCube d K) 8 (fun x => c + u x) ≤ a + b := by
    have htri := cubeEuclideanLpNorm_add_le (originCube d K)
      (p := (8 : ℝ≥0∞)) (by norm_num) (fun _ : Vec d => c) u hcn hun
    rw [cubeEuclideanLpNorm_const (originCube d K) (by norm_num) c] at htri
    exact htri.trans (add_le_add ha hb)
  have hnn : (0 : ℝ) ≤
      cubeEuclideanLpNorm (originCube d K) (8 : ℝ≥0∞) (fun x => c + u x) :=
    cubeEuclideanLpNorm_nonneg _ _ _
  calc originCubeFourthEnergy K (fun x => c + u x)
      ≤ cubeEuclideanLpNorm (originCube d K) 8 (fun x => c + u x) ^ (4 : ℕ) := h1
    _ ≤ (a + b) ^ (4 : ℕ) := pow_le_pow_left₀ hnn h2 4
    _ ≤ 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := add_pow_four_le_eight a b

/-! ## The `K`-uniform majorant -/

private theorem stripFourthEnergy_calderonZygmund_bound :
    ∀ (d : ℕ) [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ)
      (e e' : Vec d) (Ccz : ℝ),
      (0 : ℝ) < Ccz →
        (∀ (Q : TriadicCube d) (fD fN : Vec d → Vec d),
            Continuous fD →
              Continuous fN →
                ∀ (wD : H10Function (openCubeSet Q)),
                  (IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d)
                    (Fin d) ℝ)) (openCubeSet Q)
                      wD fun (x : Vec d) => -fD x) →
                    ∀ (wN : H1MeanZeroFunction (openCubeSet Q)),
                      (IsMeanZeroNeumannRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d)
                        (Fin d) ℝ)) (openCubeSet Q)
                          wN fun (x : Vec d) => -fN x) →
                        cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wD.grad ^ (2 : ℕ) +
                            cubeEuclideanLpNorm Q (8 : ℝ≥0∞) wN.toH1Function.grad ^ (2 : ℕ) ≤
                          Ccz *
                            (cubeEuclideanLpNorm Q (8 : ℝ≥0∞) fD ^ (2 : ℕ) +
                              cubeEuclideanLpNorm Q (8 : ℝ≥0∞) fN ^ (2 : ℕ))) →
          let ce : ℝ := max (1 : ℝ) (vecNorm e);
          let ce' : ℝ := max (1 : ℝ) (vecNorm e');
          (0 : ℝ) ≤ ce →
            (0 : ℝ) ≤ ce' →
              let A : ℝ := √Ccz * (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ * (ce + ce');
              A = √Ccz * (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ * (ce + ce') →
                (0 : ℝ) ≤ A →
                  ∀ (K : ℕ) (tf : ShellSeq d → ℝ),
                    (∀ (omega : ShellSeq d), (0 : ℝ) ≤ tf omega) →
                      (∀ (omega : ShellSeq d),
                          cubeEuclideanLpNorm (originCube d (↑K : ℤ)) (8 : ℝ≥0∞)
                              (streamForcing (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ omega n (n + (↑h :
                                ℤ)) e) ≤
                            (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ * ce * tf omega) →
                        (∀ (omega : ShellSeq d),
                            cubeEuclideanLpNorm (originCube d (↑K : ℤ)) (8 : ℝ≥0∞)
                                (streamForcing (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ omega n (n + (↑h :
                                  ℤ)) e') ≤
                              (↑(Annealed.sigmaBar M n) : ℝ)⁻¹ * ce' * tf omega) →
                          ∀ (omega : ShellSeq d),
                            cubeEuclideanLpNorm (originCube d (↑K : ℤ)) (8 : ℝ≥0∞)
                                  (closureDirichletAlong M n h K e omega).grad ≤
                                A * tf omega ∧
                              cubeEuclideanLpNorm (originCube d (↑K : ℤ)) (8 : ℝ≥0∞)
                                  (closureNeumannAlong M n h K e' omega).toH1Function.grad ≤
                                A * tf omega := by
  intro d _ M n h e e' Ccz hCczpos hCZ ce ce' hce0 hce'0 A hAdef hAnn K tf htf0 htfD htfN omega
  have hbase := hCZ (originCube d (K : ℤ))
    (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e)
    (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e')
    (continuous_streamForcing _ _ _ _ _) (continuous_streamForcing _ _ _ _ _)
    (closureDirichletAlong M n h K e omega)
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega)
    (closureNeumannAlong M n h K e' omega)
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega)
  have ht0 := htf0 omega
  have hfD := htfD omega
  have hfN := htfN omega
  have hfD0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e) :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hfN0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e') :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hnD0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (closureDirichletAlong M n h K e omega).toH1Function.grad :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hnN0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (closureNeumannAlong M n h K e' omega).toH1Function.grad :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hsq1 : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e) ^ (2 : ℕ)
      ≤ (((Annealed.sigmaBar M n : ℝ))⁻¹ * ce * tf omega) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hfD0 hfD 2
  have hsq2 : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
      (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e') ^ (2 : ℕ)
      ≤ (((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' * tf omega) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hfN0 hfN 2
  have hcross : (((Annealed.sigmaBar M n : ℝ))⁻¹ * ce * tf omega) ^ (2 : ℕ) +
      (((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' * tf omega) ^ (2 : ℕ) ≤
      (((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega) ^ (2 : ℕ) := by
    have hid : (((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega) ^ (2 : ℕ) -
        ((((Annealed.sigmaBar M n : ℝ))⁻¹ * ce * tf omega) ^ (2 : ℕ) +
          (((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' * tf omega) ^ (2 : ℕ)) =
        2 * ((((Annealed.sigmaBar M n : ℝ))⁻¹) ^ (2 : ℕ) * tf omega ^ (2 : ℕ) *
          (ce * ce')) := by ring
    have hnn : (0 : ℝ) ≤ 2 * ((((Annealed.sigmaBar M n : ℝ))⁻¹) ^ (2 : ℕ) *
        tf omega ^ (2 : ℕ) * (ce * ce')) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (mul_nonneg hce0 hce'0))
    linarith
  have hAt : (A * tf omega) ^ (2 : ℕ) =
      Ccz * (((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega) ^ (2 : ℕ) := by
    have hs : Real.sqrt Ccz ^ (2 : ℕ) = Ccz := Real.sq_sqrt hCczpos.le
    rw [hAdef]
    calc (Real.sqrt Ccz * ((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega)
            ^ (2 : ℕ)
        = Real.sqrt Ccz ^ (2 : ℕ) *
            (((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega) ^ (2 : ℕ) := by
          ring
      _ = Ccz * (((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') * tf omega) ^ (2 : ℕ) := by
          rw [hs]
  have hAtnn : (0 : ℝ) ≤ A * tf omega := mul_nonneg hAnn ht0
  have hchain : Ccz * (cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e)
          ^ (2 : ℕ) +
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e')
          ^ (2 : ℕ)) ≤ (A * tf omega) ^ (2 : ℕ) := by
    rw [hAt]
    exact mul_le_mul_of_nonneg_left (by linarith) hCczpos.le
  constructor
  · refine le_of_sq_le_sq_of_nonneg hnD0 hAtnn ?_
    have hsplit : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (closureDirichletAlong M n h K e omega).toH1Function.grad ^ (2 : ℕ) ≤
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
          (closureDirichletAlong M n h K e omega).toH1Function.grad ^ (2 : ℕ) +
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
          (closureNeumannAlong M n h K e' omega).toH1Function.grad ^ (2 : ℕ) :=
      le_add_of_nonneg_right (sq_nonneg _)
    linarith
  · refine le_of_sq_le_sq_of_nonneg hnN0 hAtnn ?_
    have hsplit : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (closureNeumannAlong M n h K e' omega).toH1Function.grad ^ (2 : ℕ) ≤
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
          (closureDirichletAlong M n h K e omega).toH1Function.grad ^ (2 : ℕ) +
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
          (closureNeumannAlong M n h K e' omega).toH1Function.grad ^ (2 : ℕ) :=
      le_add_of_nonneg_left (sq_nonneg _)
    linarith

/-- **A `K`-uniform integrable majorant for the two strip fourth energies.**

There is one nonnegative `B`, chosen *before* the localization scale `K`, such
that for every `K` beyond the strip top `n + h` there is a nonnegative
integrable sample function `G` with `E[G] <= B` dominating pathwise both

```
  fint_{cu_K} |e' + grad w_D|^4      and      fint_{cu_K} |e + F_z|^4 ,
```

with `w_D = Closure.closureDirichletAlong M n h K e` the Dirichlet corrector of
`e.def.w` and `F_z` the flux leg `neumannFluxField` of `e.Fz.def` built from the
Neumann corrector `Closure.closureNeumannAlong M n h K e'`.

There is **no** regime hypothesis: no `inductionState`, no `M.gamma <= gamma0`,
no bound on `cstar`, no normalization `|e| <= 1` or `|e'| <= 1`, and no `0 < h`.
The only binders beyond the typing data are `hd : 2 <= d` and, per scale,
`n + h <= K`. -/
theorem exists_strip_fourthEnergy_majorant (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : ABKModel d) (n : ℤ) (h : ℕ) (e e' : Vec d) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ K : ℕ, n + (h : ℤ) ≤ (K : ℤ) →
        ∃ G : CutoffSample d → ℝ,
          (∀ omega, 0 ≤ G omega) ∧
          Integrable G (cutoffSampleLaw M).toMeasure ∧
          (∫ omega, G omega ∂(cutoffSampleLaw M).toMeasure ≤ B) ∧
          (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
              (fun x => e' + (closureDirichletAlong M n h K e omega.val).toH1Function.grad x)
              ≤ G omega) ∧
          (∀ omega : CutoffSample d, originCubeFourthEnergy (K : ℤ)
              (fun x => e + neumannFluxField (Annealed.sigmaBar M n) omega.val n
                (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) x)
              ≤ G omega) := by
  classical
  obtain ⟨Ccz, hCczpos, hCZ⟩ :=
    Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le (d := d) hd
  obtain ⟨Ckm, hCkmpos, hkm⟩ :=
    exists_integral_streamIncrementLpNorm_eight_pow_four_le d
  have hsinv : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ :=
    inv_nonneg.2 (Annealed.sigmaBar M n).2.le
  -- the constants, all free of the localization scale `K` and of the sample
  set ce : ℝ := max 1 (vecNorm e) with hcedef
  set ce' : ℝ := max 1 (vecNorm e') with hce'def
  have hce1 : (1 : ℝ) ≤ ce := le_max_left _ _
  have hce'1 : (1 : ℝ) ≤ ce' := le_max_left _ _
  have hcee : vecNorm e ≤ ce := le_max_right _ _
  have hcee' : vecNorm e' ≤ ce' := le_max_right _ _
  have hce0 : (0 : ℝ) ≤ ce := le_trans zero_le_one hce1
  have hce'0 : (0 : ℝ) ≤ ce' := le_trans zero_le_one hce'1
  set a0 : ℝ := vecNorm e + vecNorm e' with ha0def
  set A : ℝ := Real.sqrt Ccz * ((Annealed.sigmaBar M n : ℝ))⁻¹ * (ce + ce') with hAdef
  set a1 : ℝ := A + ((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' with ha1def
  have hAnn : (0 : ℝ) ≤ A := by
    rw [hAdef]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hsinv) (by linarith)
  have hAa1 : A ≤ a1 := by
    rw [ha1def]
    have hpos : (0 : ℝ) ≤ ((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' :=
      mul_nonneg hsinv hce'0
    linarith
  set A0 : ℝ := 8 * a0 ^ (4 : ℕ) with hA0def
  set A1 : ℝ := 8 * a1 ^ (4 : ℕ) with hA1def
  have hA0nn : (0 : ℝ) ≤ A0 := by
    rw [hA0def]; positivity
  have hA1nn : (0 : ℝ) ≤ A1 := by
    rw [hA1def]; positivity
  set km : ℝ := Ckm * ((((n + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (((n + (h : ℤ) : ℤ)) : ℝ))) ^ (2 : ℕ) with hkmdef
  have hkmnn : (0 : ℝ) ≤ km := by
    rw [hkmdef]
    exact mul_nonneg hCkmpos.le (by positivity)
  refine ⟨A0 + A1 * km, add_nonneg hA0nn (mul_nonneg hA1nn hkmnn), ?_⟩
  intro K hK
  -- the fresh-shell amplitude, with the degenerate depth folded in
  have key : ∃ tf : ShellSeq d → ℝ, (∀ omega, 0 ≤ tf omega) ∧
      (∀ omega : ShellSeq d,
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
            (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e) ≤
          ((Annealed.sigmaBar M n : ℝ))⁻¹ * ce * tf omega) ∧
      (∀ omega : ShellSeq d,
        cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
            (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e') ≤
          ((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' * tf omega) ∧
      Integrable (fun omega : CutoffSample d => tf omega.val ^ (4 : ℕ))
        (cutoffSampleLaw M).toMeasure ∧
      (∫ omega : CutoffSample d, tf omega.val ^ (4 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure) ≤ km := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · have hmn : n + (h : ℤ) = n := by rw [hh]; simp
      refine ⟨fun _ => 0, fun _ => le_refl 0, ?_, ?_, ?_, ?_⟩
      · intro omega
        rw [hmn, streamForcing_self_eq_zero,
          cubeEuclideanLpNorm_const (originCube d (K : ℤ)) (by norm_num) (0 : Vec d),
          vecNorm_zero_vec, mul_zero]
      · intro omega
        rw [hmn, streamForcing_self_eq_zero,
          cubeEuclideanLpNorm_const (originCube d (K : ℤ)) (by norm_num) (0 : Vec d),
          vecNorm_zero_vec, mul_zero]
      · simp
      · simpa using hkmnn
    · have hlt : n < n + (h : ℤ) := by omega
      obtain ⟨hint, hbd⟩ := hkm M (K : ℤ) n (n + (h : ℤ)) hlt hK
      refine ⟨fun omega =>
          Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ)) omega,
        fun omega => Provider.Stream.streamIncrementLpNorm_nonneg _ _ _ _ _,
        fun omega =>
          cubeEuclideanLpNorm_streamForcing_le_of_le hsinv _ _ _ omega hce1 hcee,
        fun omega =>
          cubeEuclideanLpNorm_streamForcing_le_of_le hsinv _ _ _ omega hce'1 hcee',
        hint, ?_⟩
      rw [hkmdef]
      exact hbd
  obtain ⟨tf, htf0, htfD, htfN, htfint, htfbd⟩ := key
  -- Step 2: Calderon--Zygmund, pathwise, at both legs at once
  have hCZstep := @stripFourthEnergy_calderonZygmund_bound (d) (by infer_instance) (M) (n) (h) (e)
    (e') (Ccz) (hCczpos) (hCZ) (hce0) (hce'0) (hAdef) (hAnn) (K) (tf) (htf0) (htfD) (htfN)
  refine ⟨fun omega => A0 + A1 * tf omega.val ^ (4 : ℕ), ?_, ?_, ?_, ?_, ?_⟩
  · intro omega
    have hnn : (0 : ℝ) ≤ A1 * tf omega.val ^ (4 : ℕ) :=
      mul_nonneg hA1nn (pow_nonneg (htf0 _) _)
    linarith
  · exact (integrable_const A0).add (htfint.const_mul A1)
  · have hsplit : (∫ omega : CutoffSample d, (A0 + A1 * tf omega.val ^ (4 : ℕ))
        ∂(cutoffSampleLaw M).toMeasure) =
        A0 + A1 * ∫ omega : CutoffSample d, tf omega.val ^ (4 : ℕ)
          ∂(cutoffSampleLaw M).toMeasure := by
      rw [integral_add (integrable_const A0) (htfint.const_mul A1), integral_const,
        integral_const_mul]
      simp
    rw [hsplit]
    have hmono : A1 * ∫ omega : CutoffSample d, tf omega.val ^ (4 : ℕ)
        ∂(cutoffSampleLaw M).toMeasure ≤ A1 * km :=
      mul_le_mul_of_nonneg_left htfbd hA1nn
    linarith
  · intro omega
    have hgradD := (hCZstep omega.val).1
    have hb : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (closureDirichletAlong M n h K e omega.val).toH1Function.grad ≤
        a1 * tf omega.val :=
      hgradD.trans (mul_le_mul_of_nonneg_right hAa1 (htf0 omega.val))
    have ha : vecNorm e' ≤ a0 := by
      rw [ha0def]
      have := vecNorm_nonneg e
      linarith
    have hshift := originCubeFourthEnergy_shift_le (K : ℤ) e'
      (closureDirichletAlong M n h K e omega.val).toH1Function.grad
      (memLp_eight_grad_closureDirichletAlong hd M n h K e omega.val) ha hb
    refine hshift.trans (le_of_eq ?_)
    rw [hA0def, hA1def]
    ring
  · intro omega
    have hgradN := (hCZstep omega.val).2
    have hmemN : MemLp (closureNeumannAlong M n h K e' omega.val).toH1Function.grad
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d (K : ℤ))) :=
      memLp_eight_grad_closureNeumannAlong hd M n h K e' omega.val
    have hmemF : MemLp
        (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e')
        (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d (K : ℤ))) :=
      memLp_normalizedCubeMeasure_of_continuous (originCube d (K : ℤ)) 8
        (continuous_streamForcing _ _ _ _ _)
    have htri := cubeEuclideanLpNorm_add_le (originCube d (K : ℤ))
      (p := (8 : ℝ≥0∞)) (by norm_num)
      (closureNeumannAlong M n h K e' omega.val).toH1Function.grad
      (streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n (n + (h : ℤ)) e')
      (memLp_vecNorm_eight_of_memLp_eight _ hmemN)
      (memLp_vecNorm_eight_of_memLp_eight _ hmemF)
    have hflux : cubeEuclideanLpNorm (originCube d (K : ℤ)) 8
        (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
          (closureNeumannAlong M n h K e' omega.val)) ≤ a1 * tf omega.val := by
      have hunfold : neumannFluxField (Annealed.sigmaBar M n) omega.val n
            (n + (h : ℤ)) e' (closureNeumannAlong M n h K e' omega.val) =
          fun x => (closureNeumannAlong M n h K e' omega.val).toH1Function.grad x +
            streamForcing ((Annealed.sigmaBar M n : ℝ))⁻¹ omega.val n
              (n + (h : ℤ)) e' x := rfl
      rw [hunfold]
      refine htri.trans ?_
      have hf := htfN omega.val
      have hexp : a1 * tf omega.val = A * tf omega.val +
          ((Annealed.sigmaBar M n : ℝ))⁻¹ * ce' * tf omega.val := by
        rw [ha1def]; ring
      rw [hexp]
      linarith
    have ha : vecNorm e ≤ a0 := by
      rw [ha0def]
      have := vecNorm_nonneg e'
      linarith
    have hshift := originCubeFourthEnergy_shift_le (K : ℤ) e
      (neumannFluxField (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e'
        (closureNeumannAlong M n h K e' omega.val))
      (memLp_eight_neumannFluxField_closure hd M n h K e' omega.val) ha hflux
    refine hshift.trans (le_of_eq ?_)
    rw [hA0def, hA1def]
    ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
