/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.StreamIncrementLpLargeCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpSquared
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellCZ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.ShellNormalization
import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# FreshShellL8

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.nablaw.in.L.eight`

This module assembles ABK26's three-line display

```
  ‖∇w_{D,e}^{(K)}‖²_{L^8(cu_K)} + ‖∇w_{N,e'}^{(K)}‖²_{L^8(cu_K)}
    <=  C shom_{m-h}^{-2} ‖k_m - k_{m-h}‖²_{L^8(cu_K)}                    (i)
    <=  C shom_{m-h}^{-2} h 3^{2 gamma m}
          + O_{Gamma_1}( C shom_{m-h}^{-2} 3^{2 gamma m} h 3^{-(K-m)d/8})  (ii)
    <=  C + O_{Gamma_1}( gamma^100 )                                       (iii)
```

inside the proof of `l.approximate.recurrence.formula`, with `h = k_m -
k_{m-h}` the fresh shell, `K >= m + 10^10 gamma^{-1}` and `h <= 6 cstar
gamma^{-1}` the parameters of `e.recurrence.params`, and `|e|, |e'| <= 1`.

## The three lines

* **(ii)** is `e.km.kn.Lp` at `p = 8`, `l = K`, `m - n = h`.  It is supplied
  here by `exists_streamIncrementLpNormSq_head_tail`, derived from the frozen
  theorem `Algsuperdiff.Frozen.Section3.stream_increment_lp_large_cube_bound`.
* **(iii)** is the deterministic normalization arithmetic, already established
  unconditionally in `ShellNormalization`: `inv_sigmaBarSq_mul_shellWidth_le`
  gives the absolute head constant `24 * 3^18` and
  `const_mul_rpow_gap_le_gammaPow` together with
  `exists_gamma_threshold_for_gap_constant` give the manuscript's "increasing
  `M` in `e.cgamma.constraints`, if necessary".

## Norm gauge

Every `L^8` norm below is `cubeEuclideanLpNorm`, i.e. the manuscript's
volume-normalized `L^8` norm read with the **Euclidean** pointwise length.  The
frozen Calder\'on-Zygmund anchor is stated in the ambient sup gauge of
`Vec d = Fin d -> ℝ`; module `CubeEuclideanL8` converts between the two at the
cost of a factor `sqrt d`, which the dimension-only constant absorbs.  The
stream-increment side is Euclidean already: `Provider.Stream` measures the
increment in `Book.Ch02.matrixOperatorNorm`, the Euclidean operator norm.

## Main results

* `exists_streamIncrementLpNormSq_head_tail` -- line (ii).
* `exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow` -- the whole
  display.

## References

* ABK26, `e.nablaw.in.L.eight`.
* ABK26, `e.def.w`; `e.recurrence.params`.
* ABK26, `e.km.kn.Lp`; `e.shom.h.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The positive part of a one-sided tail -/

/-- The positive part of an `O_Psi(A)` variable is again `O_Psi(A)`, for a
positive amplitude: the two upper-tail events coincide above `A`. -/
private theorem isBigOWith_posPart {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Psi : ℝ → ℝ} {X : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hX : IndependentSums.IsBigOWith mu Psi X A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => max (X omega) 0) A := by
  simpa only [max_comm] using
    Algsuperdiff.Section3.Probability.isBigOWith_max_zero hA hX

/-! ## Line (ii): `e.km.kn.Lp` at `p = 8` -/

/-- **Line (ii) of `e.nablaw.in.L.eight`.**

The squared volume-normalized `L^8` norm of a stream increment on a large cube
obeys

```
  ‖k_m - k_n‖²_{L^8(cu_l)}
    <=  C min{gamma^{-1}, m-n} 3^{2 gamma m}
        + O_{Gamma_1}( C min{gamma^{-1}, m-n} 3^{2 gamma m} 3^{-(d/8)(l-m)} ) ,
```

with one dimension-only constant `C`, produced before the model and the scales. -/
theorem exists_streamIncrementLpNormSq_head_tail (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (l n m : ℤ), n < m → m ≤ l →
        ∃ T : Cutoff.ShellSeq d → ℝ,
          (∀ omega, 0 ≤ T omega) ∧
          (∀ omega, Stream.streamIncrementLpNorm 8 l n m omega ^ 2 ≤
              C * (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) + T omega) ∧
          IndependentSums.IsBigOWith M.P.toMeasure
            (IndependentSums.gammaSigma 1) T
            (C * (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                  (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * ((l : ℝ) - (m : ℝ)))) := by
  obtain ⟨C₁, hC₁pos, hSI⟩ :=
    Algsuperdiff.Frozen.Section3.stream_increment_lp_large_cube_bound d
  refine ⟨8 * C₁, mul_pos (by norm_num) hC₁pos, ?_⟩
  intro M l n m hnm hml
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hfrozen := hSI M 8 (by norm_num) l m n hnm hml
  set A₀ : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA₀def
  have hA₀pos : 0 < A₀ := by
    have hmin : 0 < min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) := by
      refine lt_min (inv_pos.2 hgamma) ?_
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    have hthree : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hA₀def]
    exact mul_pos hmin hthree
  have hbase : (0 : ℝ) < C₁ * 8 := mul_pos hC₁pos (by norm_num)
  set H : ℝ := (C₁ * 8) ^ ((8 : ℝ) / 2) * A₀ ^ ((8 : ℝ) / 2) with hHdef
  have hHpos : 0 < H := by
    have h1 : (0 : ℝ) < (C₁ * 8) ^ ((8 : ℝ) / 2) := Real.rpow_pos_of_pos hbase _
    have h2 : (0 : ℝ) < A₀ ^ ((8 : ℝ) / 2) := Real.rpow_pos_of_pos hA₀pos _
    rw [hHdef]
    exact mul_pos h1 h2
  set Kamp : ℝ := H * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
    with hKampdef
  obtain ⟨-, hKamppos, -, htail⟩ := hfrozen
  -- the positive-part tail
  set T₀ : Cutoff.ShellSeq d → ℝ :=
    fun omega => max (Stream.streamIncrementLpMass 8 l n m omega - H) 0 with hT₀def
  have hT₀nonneg : ∀ omega, 0 ≤ T₀ omega := fun omega => le_max_right _ _
  have hT₀tail : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma (2 / 8)) T₀ Kamp :=
    isBigOWith_posPart hKamppos htail
  have hmassle : ∀ omega,
      Stream.streamIncrementLpMass 8 l n m omega ≤ H + T₀ omega := by
    intro omega
    have hmax := le_max_left (Stream.streamIncrementLpMass 8 l n m omega - H) 0
    have hT₀val : T₀ omega =
        max (Stream.streamIncrementLpMass 8 l n m omega - H) 0 := rfl
    rw [hT₀val]
    linarith
  obtain ⟨-, hnormle, htail'⟩ :=
    Stream.streamIncrementLpNormSq_head_tail_of_mass_head_tail M
      (p := 8) (by norm_num) l n m hHpos.le hKamppos.le hT₀nonneg hmassle hT₀tail
  -- the head and amplitude in closed form
  have hHroot : H ^ ((2 : ℝ) / 8) = 8 * C₁ * A₀ := by
    have hone : (8 : ℝ) / 2 * ((2 : ℝ) / 8) = 1 := by norm_num
    rw [hHdef, Real.mul_rpow (Real.rpow_nonneg hbase.le _)
      (Real.rpow_nonneg hA₀pos.le _), ← Real.rpow_mul hbase.le,
      ← Real.rpow_mul hA₀pos.le, hone, Real.rpow_one, Real.rpow_one]
    ring
  have hKroot : Kamp ^ ((2 : ℝ) / 8) =
      8 * C₁ * A₀ * (3 : ℝ) ^ (-((d : ℝ) / 8) * ((l : ℝ) - (m : ℝ))) := by
    have hexp : (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) * ((2 : ℝ) / 8) =
        -((d : ℝ) / 8) * ((l : ℝ) - (m : ℝ)) := by ring
    rw [hKampdef, Real.mul_rpow hHpos.le
      (Real.rpow_nonneg (by norm_num) _), hHroot,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp]
  refine ⟨fun omega => T₀ omega ^ ((2 : ℝ) / 8), fun omega =>
    Real.rpow_nonneg (hT₀nonneg omega) _, fun omega => ?_, ?_⟩
  · have hbound := hnormle omega
    rw [hHroot] at hbound
    exact hbound
  · rw [← hKroot]
    exact htail'

/-! ## The fresh-shell forcing of `e.def.w` -/

/-- The forcing of the two corrector problems `e.def.w`: `shom_{m-h}^{-1} (k_m -
k_{m-h}) e`. -/
def streamForcing (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ)
    (e : Vec d) : Vec d → Vec d :=
  fun x => sigmaInv • matVecMul (Cutoff.finiteShellIncrement omega n m x) e

/-- The Euclidean length is homogeneous. -/
theorem vecNorm_smul (c : ℝ) (v : Vec d) :
    Book.Ch02.vecNorm (c • v) = |c| * Book.Ch02.vecNorm v := by
  rw [vecNorm_eq_sqrt_vecNormSq, vecNorm_eq_sqrt_vecNormSq]
  have h : vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The stream increment is continuous in the space variable. -/
theorem continuous_finiteShellIncrement (omega : Cutoff.ShellSeq d) (n m : ℤ) :
    Continuous (fun x : Vec d => Cutoff.finiteShellIncrement omega n m x) := by
  have h : (fun x : Vec d => Cutoff.finiteShellIncrement omega n m x) =
      fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) x := by
    funext x
    rw [Cutoff.finiteShellIncrement_apply]
    rfl
  rw [h]
  exact continuous_finsetSum _ fun k _ => (omega k).1.1.continuous

/-- The forcing of `e.def.w` is continuous. -/
theorem continuous_streamForcing (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d)
    (n m : ℤ) (e : Vec d) :
    Continuous (streamForcing sigmaInv omega n m e) := by
  have hF := continuous_finiteShellIncrement omega n m
  have hmat : Continuous
      (fun x : Vec d => matVecMul (Cutoff.finiteShellIncrement omega n m x) e) := by
    refine continuous_pi fun i => ?_
    simp only [matVecMul]
    exact continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp hF)).mul
        continuous_const)
  have hsmul : Continuous
      (fun x : Vec d => sigmaInv • matVecMul (Cutoff.finiteShellIncrement omega n m x) e) :=
    (continuous_const : Continuous (fun _ : Vec d => sigmaInv)).smul hmat
  exact hsmul

/-- The pointwise size of the forcing of `e.def.w`, for a direction of Euclidean
length at most one. -/
theorem vecNorm_streamForcing_le {sigmaInv : ℝ} (hsigma : 0 ≤ sigmaInv)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) {e : Vec d}
    (he : Book.Ch02.vecNorm e ≤ 1) (x : Vec d) :
    Book.Ch02.vecNorm (streamForcing sigmaInv omega n m e x) ≤
      sigmaInv * streamIncrementSize n m omega x := by
  rw [streamForcing, vecNorm_smul, abs_of_nonneg hsigma]
  refine mul_le_mul_of_nonneg_left ?_ hsigma
  have hop := Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
    (Cutoff.finiteShellIncrement omega n m x) e
  have hnn : 0 ≤ streamIncrementSize n m omega x :=
    streamIncrementSize_nonneg n m omega x
  calc Book.Ch02.vecNorm (matVecMul (Cutoff.finiteShellIncrement omega n m x) e)
      ≤ streamIncrementSize n m omega x * Book.Ch02.vecNorm e := hop
    _ ≤ streamIncrementSize n m omega x * 1 :=
        mul_le_mul_of_nonneg_left he hnn
    _ = streamIncrementSize n m omega x := mul_one _

private theorem ofReal_eight : ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) := by
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
  norm_num

/-- **The right-hand side of line (i).**  The `L^8` norm of the forcing of
`e.def.w` is at most `shom^{-1}` times the `L^8` norm of the fresh shell. -/
theorem cubeEuclideanLpNorm_streamForcing_le {sigmaInv : ℝ}
    (hsigma : 0 ≤ sigmaInv) (l n m : ℤ) (omega : Cutoff.ShellSeq d) {e : Vec d}
    (he : Book.Ch02.vecNorm e ≤ 1) :
    cubeEuclideanLpNorm (originCube d l) 8 (streamForcing sigmaInv omega n m e) ≤
      sigmaInv * Stream.streamIncrementLpNorm 8 l n m omega := by
  have hcontSize : Continuous (streamIncrementSize (d := d) n m omega) :=
    continuous_streamIncrementSize n m omega
  have hmem : MemLp (fun x => sigmaInv • streamIncrementSize (d := d) n m omega x)
      (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d l)) :=
    memLp_normalizedCubeMeasure_of_continuous _ _
      ((continuous_const : Continuous (fun _ : Vec d => sigmaInv)).smul hcontSize :
        Continuous (fun x : Vec d => sigmaInv • streamIncrementSize (d := d) n m omega x))
  have hmono : cubeLpNorm (originCube d l) (8 : ℝ≥0∞)
        (fun x => Book.Ch02.vecNorm (streamForcing sigmaInv omega n m e x)) ≤
      cubeLpNorm (originCube d l) (8 : ℝ≥0∞)
        (fun x => sigmaInv • streamIncrementSize (d := d) n m omega x) := by
    refine cubeLpNorm_mono_of_memLp _ _ (fun x => ?_) hmem
    have hle := vecNorm_streamForcing_le hsigma omega n m he x
    have hnn : (0 : ℝ) ≤ sigmaInv * streamIncrementSize (d := d) n m omega x :=
      mul_nonneg hsigma (streamIncrementSize_nonneg n m omega x)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (Book.Ch02.vecNorm_nonneg (streamForcing sigmaInv omega n m e x)),
      abs_of_nonneg hsigma,
      abs_of_nonneg (streamIncrementSize_nonneg (d := d) n m omega x),
      smul_eq_mul] using hle
  have hsmul := cubeLpNorm_const_mul_of_nonneg (originCube d l) (8 : ℝ≥0∞)
    hsigma (streamIncrementSize (d := d) n m omega)
  have hbridge := cubeLpNorm_streamIncrementSize_eq_streamIncrementLpNorm
    (d := d) (p := 8) (by norm_num) l n m omega
  rw [ofReal_eight] at hbridge
  rw [cubeEuclideanLpNorm]
  calc cubeLpNorm (originCube d l) (8 : ℝ≥0∞)
        (fun x => Book.Ch02.vecNorm (streamForcing sigmaInv omega n m e x))
      ≤ cubeLpNorm (originCube d l) (8 : ℝ≥0∞)
          (fun x => sigmaInv • streamIncrementSize (d := d) n m omega x) := hmono
    _ = sigmaInv * cubeLpNorm (originCube d l) (8 : ℝ≥0∞)
          (streamIncrementSize (d := d) n m omega) := hsmul
    _ = sigmaInv * Stream.streamIncrementLpNorm 8 l n m omega := by rw [hbridge]

/-! ## The display -/

/-- **`e.nablaw.in.L.eight`.**

There is one dimension-only constant `Chead` and one positive scale threshold
`gamma0` -- the quantitative content of the manuscript's "increasing `M` in
`e.cgamma.constraints`, if necessary" -- such that, for every ABK model with
`gamma <= gamma0`, every valid induction state `S(m0, E)` of `d.mathcalS.def`,
every `m, K, h` obeying the recurrence parameters
`m - h <= m0`, `h <= 6 cstar gamma^{-1}`, `K >= m + 10^10 gamma^{-1}` of
`e.recurrence.params`, and all directions `e, e'` of Euclidean length at most
one, there is a nonnegative random amplitude `Tfluct` with

```
  Tfluct  <=  O_{Gamma_1}( gamma^100 )
```

such that **every** pair of a zero-trace Dirichlet solution and a mean-zero
Neumann solution of the two problems `e.def.w` satisfies, pathwise,

```
  ‖∇w_{D,e}^{(K)}‖²_{L^8(cu_K)} + ‖∇w_{N,e'}^{(K)}‖²_{L^8(cu_K)}
      <=  Chead + Tfluct(omega) .
```

`Tfluct` does not depend on the solutions, so no measurable selection of
correctors is claimed or needed; the left-hand side is the manuscript's actual
sum of squared gradient norms, not a majorant substituted for it.

The `L^8` norms are `cubeEuclideanLpNorm`, i.e. the manuscript's Euclidean
reading of the volume-normalized `L^8` norm.

This theorem therefore reaches those two anchors and carries the standard three
axioms, `[propext, Classical.choice, Quot.sound]`.  Line (iii) reaches neither
(`ShellNormalization`). -/
theorem exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Chead : ℝ, 0 < Chead ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 E →
            ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
              (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∃ Tfluct : Cutoff.ShellSeq d → ℝ,
                  (∀ omega, 0 ≤ Tfluct omega) ∧
                  IndependentSums.IsBigOWith M.P.toMeasure
                      (IndependentSums.gammaSigma 1) Tfluct
                      (M.gamma ^ (100 : ℕ)) ∧
                  ∀ (omega : Cutoff.ShellSeq d)
                    (wD : H10Function (openCubeSet (originCube d K))),
                    IsZeroTraceDirichletRhsWeakSolution
                        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                        (openCubeSet (originCube d K)) wD
                        (fun x => -streamForcing
                          ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                          (m - (h : ℤ)) m e x) →
                    ∀ (wN : H1MeanZeroFunction (openCubeSet (originCube d K))),
                      IsMeanZeroNeumannRhsWeakSolution
                          (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                          (openCubeSet (originCube d K)) wN
                          (fun x => -streamForcing
                            ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                            (m - (h : ℤ)) m e' x) →
                      cubeEuclideanLpNorm (originCube d K) 8
                            wD.toH1Function.grad ^ 2 +
                          cubeEuclideanLpNorm (originCube d K) 8
                            wN.toH1Function.grad ^ 2 ≤
                        Chead + Tfluct omega := by
  obtain ⟨Ccz, hCczpos, hCZ⟩ := exists_cubeEuclideanL8_gradient_sq_sum_le hd
  obtain ⟨Clp, hClppos, hLP⟩ := exists_streamIncrementLpNormSq_head_tail d
  set Ctot : ℝ := 2 * Ccz * Clp with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    exact mul_pos (mul_pos (by norm_num) hCczpos) hClppos
  have hgapconst : (0 : ℝ) < 24 * (3 : ℝ) ^ (18 : ℝ) := by
    have hthree : (0 : ℝ) < (3 : ℝ) ^ (18 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  obtain ⟨gamma0, hg0pos, hg0quarter, hg0⟩ :=
    exists_gamma_threshold_for_gap_constant (Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)))
  refine ⟨Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)), mul_pos hCtotpos hgapconst,
    gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 E hS m K h hhpos hm hh hK e e' he he'
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hquarter : M.gamma ≤ 1 / 4 := le_trans hMgamma hg0quarter
  have hsigmapos : 0 < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1
  set sigmaInv : ℝ := ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ with hsigmaInvdef
  have hsigmaInvnn : 0 ≤ sigmaInv := (inv_pos.2 hsigmapos).le
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ :=
      mul_pos (by norm_num) (inv_pos.2 hgamma)
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  have hnm : m - (h : ℤ) < m := by omega
  obtain ⟨T, hTnonneg, hTle, hTtail⟩ := hLP M K (m - (h : ℤ)) m hnm hmK
  -- the shell width, in the shape of `e.km.kn.Lp`
  have hcast : (m : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ) = (h : ℝ) := by push_cast; ring
  set A₀ : ℝ := min M.gamma⁻¹ ((m : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA₀def
  -- the normalization of line (iii)
  have hhead := inv_sigmaBarSq_mul_shellWidth_le M hS hm hh
  have hsigsq : sigmaInv ^ 2 =
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ := by
    rw [hsigmaInvdef, inv_pow]
  have hnormalized : sigmaInv ^ 2 * A₀ ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := by
    have hle : A₀ ≤ (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos (by norm_num) _).le
      rw [hcast]
      exact min_le_right _ _
    have hsq : (0 : ℝ) ≤ sigmaInv ^ 2 := sq_nonneg _
    calc sigmaInv ^ 2 * A₀
        ≤ sigmaInv ^ 2 * ((h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hle hsq
      _ = ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ * (h : ℝ) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by rw [hsigsq]; ring
      _ ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := hhead
  -- the fluctuation
  have hcnn : (0 : ℝ) ≤ 2 * Ccz * sigmaInv ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hCczpos.le) (sq_nonneg _)
  refine ⟨fun omega => 2 * Ccz * sigmaInv ^ 2 * T omega,
    fun omega => mul_nonneg hcnn (hTnonneg omega), ?_, ?_⟩
  · have hc : (0 : ℝ) ≤ 2 * Ccz * sigmaInv ^ 2 := hcnn
    have hscaled := hTtail.const_mul hc
    refine hscaled.mono_scale ?_
    have hCsmall : Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)) ≤
        (3 : ℝ) ^ ((10 : ℝ) ^ (9 : ℕ) * M.gamma⁻¹) := hg0 M.gamma hgamma hMgamma
    have hgap := const_mul_rpow_gap_le_gammaPow
      (C := Ctot * (24 * (3 : ℝ) ^ (18 : ℝ))) (gamma := M.gamma)
      (G := (K : ℝ) - (m : ℝ)) (mul_pos hCtotpos hgapconst).le hgamma hquarter hd
      hK hCsmall
    have hdecay : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hstep : 2 * Ccz * sigmaInv ^ 2 * (Clp * A₀ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ)))) ≤
        Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) := by
      have hmul : Ctot * (sigmaInv ^ 2 * A₀) ≤ Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnormalized hCtotpos.le
      calc 2 * Ccz * sigmaInv ^ 2 * (Clp * A₀ *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))))
          = (Ctot * (sigmaInv ^ 2 * A₀)) *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) := by
            rw [hCtotdef]; ring
        _ ≤ (Ctot * (24 * (3 : ℝ) ^ (18 : ℝ))) *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
            mul_le_mul_of_nonneg_right hmul hdecay
    exact le_trans hstep hgap
  · intro omega wD hwD wN hwN
    have hczapp := hCZ (originCube d K)
      (streamForcing sigmaInv omega (m - (h : ℤ)) m e)
      (streamForcing sigmaInv omega (m - (h : ℤ)) m e')
      (continuous_streamForcing _ _ _ _ _)
      (continuous_streamForcing _ _ _ _ _) wD hwD wN hwN
    have hN : (0 : ℝ) ≤ Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega :=
      Stream.streamIncrementLpNorm_nonneg _ _ _ _ _
    have hforcing : ∀ v : Vec d, Book.Ch02.vecNorm v ≤ 1 →
        cubeEuclideanLpNorm (originCube d K) 8
            (streamForcing sigmaInv omega (m - (h : ℤ)) m v) ^ 2 ≤
          sigmaInv ^ 2 *
            Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega ^ 2 := by
      intro v hv
      have hle := cubeEuclideanLpNorm_streamForcing_le hsigmaInvnn K
        (m - (h : ℤ)) m omega hv
      have hnn : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d K) 8
          (streamForcing sigmaInv omega (m - (h : ℤ)) m v) :=
        cubeEuclideanLpNorm_nonneg _ _ _
      have hrhs : (0 : ℝ) ≤ sigmaInv *
          Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega :=
        mul_nonneg hsigmaInvnn hN
      nlinarith [hle, hnn, hrhs]
    have hD := hforcing e he
    have hN' := hforcing e' he'
    have hmassbound := hTle omega
    have hsq : (0 : ℝ) ≤ sigmaInv ^ 2 := sq_nonneg _
    have hchain :
        cubeEuclideanLpNorm (originCube d K) 8 wD.toH1Function.grad ^ 2 +
            cubeEuclideanLpNorm (originCube d K) 8 wN.toH1Function.grad ^ 2 ≤
          Ccz * (2 * (sigmaInv ^ 2 *
            Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega ^ 2)) := by
      refine le_trans hczapp ?_
      refine mul_le_mul_of_nonneg_left ?_ hCczpos.le
      linarith
    have hfinal : Ccz * (2 * (sigmaInv ^ 2 *
          Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega ^ 2)) ≤
        Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)) + 2 * Ccz * sigmaInv ^ 2 * T omega := by
      have hstep1 : Ccz * (2 * (sigmaInv ^ 2 *
            Stream.streamIncrementLpNorm 8 K (m - (h : ℤ)) m omega ^ 2)) ≤
          Ccz * (2 * (sigmaInv ^ 2 * (Clp * A₀ + T omega))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCczpos.le
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hmassbound hsq
      have hstep2 : Ccz * (2 * (sigmaInv ^ 2 * (Clp * A₀ + T omega))) =
          Ctot * (sigmaInv ^ 2 * A₀) + 2 * Ccz * sigmaInv ^ 2 * T omega := by
        rw [hCtotdef]; ring
      have hstep3 : Ctot * (sigmaInv ^ 2 * A₀) ≤
          Ctot * (24 * (3 : ℝ) ^ (18 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnormalized hCtotpos.le
      linarith [hstep1, hstep3, hstep2.le, hstep2.ge]
    exact le_trans hchain hfinal

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
