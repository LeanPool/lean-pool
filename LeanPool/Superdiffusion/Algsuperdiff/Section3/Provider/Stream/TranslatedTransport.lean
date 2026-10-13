/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementDerivativeBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.OriginConcentration

/-!
# TranslatedTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# One-shell law transport under real translations

ABK26 upgrades the small-cube estimate `e.km.kn.Linfty.smallcube` to the large
cube `cu_l` by covering `cu_l` with translated copies of a small cube and
taking a maximum.  Every translated copy must carry the *same* amplitude as the
copy at the origin, which is where the stationarity half of the frozen (J1)
assumption enters.

The frozen (J1) stationarity field is stationarity of the *zero shell* law, and
the frozen prefix supplies only the one-coordinate marginal scaling law
`e.diff.law.shift`.  No joint shift invariance of the shell sequence is claimed
or used.  What is proved here is exactly the one-shell statement: for a
measurable real observable `F` of a single shell,

`law of F(j_k(· + z)) = law of F(j_k)`,

which follows from (J1) stationarity through the pointwise commutation

`translate z ∘ triadicScale γ k = triadicScale γ k ∘ translate (3^{-k} z)`.

The module then transports the three single-shell inputs of the small-cube
argument to an arbitrary base point `z`:

* the value gauge `e.jk.O`;
* the derivative gauge `e.nabla.jk.O` and its sum over `k ∈ (n, m]`;
* the mean-zero and independence facts for the shell values at `z`, the first
  of which is the frozen (J1) mean-zero field read at the point `3^{-k} z`
  rather than at the origin.

## Main results

* `Algsuperdiff.Section3.Provider.Stream.translate_triadicScale`
* `Algsuperdiff.Section3.Provider.Stream.map_shellObservable_translate_eq`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_shellObservable_translate`
* `Algsuperdiff.Section3.Provider.Stream.isBigO_gammaSigma_shell_entry`
* `Algsuperdiff.Section3.Provider.Stream.integral_shell_entry_eq_zero`
* `Algsuperdiff.Section3.Provider.Stream.iIndepFun_shell_entry`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate`

## References

* ABK26, (J1).
* ABK26, `e.diff.law.shift`, the marginal scaling law.
* ABK26, `e.jk.O`; `e.nabla.jk.O`.
* ABK26, `e.km.kn.Linfty`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Commutation of the two frozen actions -/

/-- The frozen translation and triadic scaling actions commute after rescaling
the shift: `j(3^{-k}(· + z)) = (j(· + 3^{-k} z))(3^{-k} ·)`.  Both sides are
compared through `ShellField.ext`, so the stored derivatives need no separate
argument. -/
theorem translate_triadicScale (gamma : ℝ) (k : ℤ) (z : Vec d) (j : ShellField d) :
    ShellField.translate z (ShellField.triadicScale gamma k j) =
      ShellField.triadicScale gamma k
        (ShellField.translate ((((3 : ℝ) ^ k)⁻¹) • z) j) := by
  refine ShellField.ext fun x => ?_
  simp only [ShellField.translate_apply, ShellField.triadicScale_apply, smul_add]

/-! ## The one-shell translated law -/

/-- Stationarity of the zero shell, transported to every shell index: for a
measurable real observable `F` of a single shell, the law of `F(j_k(· + z))`
under the shell-sequence law is the law of `F(j_k)`.

Only the one-coordinate marginal scaling law and the (J1) stationarity of the
zero shell are used; no joint shift invariance of the sequence is claimed. -/
theorem map_shellObservable_translate_eq (M : ABKModel d) (k : ℤ) (z : Vec d)
    (F : ShellField d → ℝ) (hF : Measurable F) :
    Measure.map (fun omega : ShellSeq d => F (ShellField.translate z (omega k)))
        M.P.toMeasure =
      Measure.map (fun omega : ShellSeq d => F (omega k)) M.P.toMeasure := by
  have hFt : Measurable (fun j : ShellField d => F (ShellField.translate z j)) :=
    hF.comp (ShellField.measurable_translate z)
  have hFs : Measurable (fun j : ShellField d =>
      F (ShellField.triadicScale M.gamma k j)) :=
    hF.comp (ShellField.measurable_triadicScale M.gamma k)
  calc Measure.map
        (fun omega : ShellSeq d => F (ShellField.translate z (omega k))) M.P.toMeasure
      = Measure.map (fun j : ShellField d =>
          F (ShellField.translate z (ShellField.triadicScale M.gamma k j)))
            (ShellField.zeroShellLaw M.P).toMeasure :=
        map_shellObservable_eq_zero_triadicScale M k
          (fun j => F (ShellField.translate z j)) hFt
    _ = Measure.map (fun j : ShellField d =>
          F (ShellField.triadicScale M.gamma k
            (ShellField.translate ((((3 : ℝ) ^ k)⁻¹) • z) j)))
            (ShellField.zeroShellLaw M.P).toMeasure := by
        refine Measure.map_congr ?_
        filter_upwards with j
        rw [translate_triadicScale]
    _ = Measure.map (fun j : ShellField d =>
          F (ShellField.triadicScale M.gamma k j))
            (ShellField.zeroShellLaw M.P).toMeasure :=
        map_zeroObservable_translate_eq M ((((3 : ℝ) ^ k)⁻¹) • z)
          (fun j => F (ShellField.triadicScale M.gamma k j)) hFs
    _ = Measure.map (fun omega : ShellSeq d => F (omega k)) M.P.toMeasure :=
        (map_shellObservable_eq_zero_triadicScale M k F hF).symm

/-- Transport a one-sided stretched-exponential estimate through an exact
push-forward identity.  The weak-Orlicz upper-tail relation only sees the law
of the random variable. -/
theorem isBigOWith_gammaSigma_of_law_eq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {sigma A : ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hmap : Measure.map X mu = Measure.map Y mu)
    (hYtail : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X A := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff] at hYtail ⊢
  intro t ht
  have hE : MeasurableSet {x : ℝ | A * t < x} :=
    measurableSet_lt measurable_const measurable_id
  calc mu.real {omega | A * t < X omega}
      = (Measure.map X mu).real {x : ℝ | A * t < x} := by
        have h := congrArg ENNReal.toReal
          (Measure.map_apply_of_aemeasurable (μ := mu) hX.aemeasurable hE)
        simpa only [Set.preimage_ofPred_eq] using! h.symm
    _ = (Measure.map Y mu).real {x : ℝ | A * t < x} := by rw [hmap]
    _ = mu.real {omega | A * t < Y omega} := by
        have h := congrArg ENNReal.toReal
          (Measure.map_apply_of_aemeasurable (μ := mu) hY.aemeasurable hE)
        simpa only [Set.preimage_ofPred_eq] using! h
    _ ≤ Real.exp (-(t ^ sigma)) := hYtail ht

/-- Every one-shell `Γ_σ` estimate holds verbatim at every translated base
point. -/
theorem isBigOWith_gammaSigma_shellObservable_translate (M : ABKModel d) (k : ℤ)
    (z : Vec d) {F : ShellField d → ℝ} (hF : Measurable F) {sigma A : ℝ}
    (h : IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma sigma)
      (fun omega : ShellSeq d => F (omega k)) A) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma sigma)
      (fun omega : ShellSeq d => F (ShellField.translate z (omega k))) A :=
  isBigOWith_gammaSigma_of_law_eq
    ((hF.comp (ShellField.measurable_translate z)).comp (measurable_pi_apply k))
    (hF.comp (measurable_pi_apply k))
    (map_shellObservable_translate_eq M k z F hF) h

/-! ## The translated single-shell gauges -/

/-- ABK26's `e.jk.O` on the translated cube `z + cu_k`. -/
theorem isBigOWith_gammaSigma_localCubeControl_shell_translate (M : ABKModel d)
    (k : ℤ) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        localCubeControl k (ShellField.translate z (omega k)))
      (Real.rpow 3 (M.gamma * (k : ℝ))) :=
  isBigOWith_gammaSigma_shellObservable_translate M k z
    (measurable_localCubeControl k)
    (isBigOWith_gammaSigma_localCubeControl_shell M k)

/-- ABK26's `e.nabla.jk.O` on the translated cube `z + cu_ell`, for `ell ≤ k`. -/
theorem isBigOWith_gammaSigma_shellDerivGauge_cube_translate (M : ABKModel d)
    {ell k : ℤ} (h : ell ≤ k) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        localCubeDerivNorm ell (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ ell *
            localCubeSecondDerivNorm ell (ShellField.translate z (omega k)))
      (Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) :=
  isBigOWith_gammaSigma_shellObservable_translate M k z
    (measurable_shellDerivGauge ell)
    (isBigOWith_gammaSigma_shellDerivGauge_cube M h)

/-- The translated form of ABK26's `e.nabla.km.kn.infty`: the summed derivative
gauges on the translated small cube `z + cu_n` obey the same `Γ₂` bound as at
the origin. -/
theorem isBigOWith_gammaSigma_shellDerivGaugeSum_Ioc_translate (M : ABKModel d)
    {n m : ℤ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        (localCubeDerivNorm n (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ n *
            localCubeSecondDerivNorm n (ShellField.translate z (omega k))))
      (IndependentSums.gammaTriangleConst 2 *
        Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by
  have hs : (Finset.Ioc n m).Nonempty := by
    refine ⟨m, ?_⟩
    simp only [Finset.mem_Ioc]
    exact ⟨hnm, le_refl m⟩
  have hnonneg : ∀ (k : ℤ) (omega : ShellSeq d),
      0 ≤ localCubeDerivNorm n (ShellField.translate z (omega k)) +
        (3 : ℝ) ^ n *
          localCubeSecondDerivNorm n (ShellField.translate z (omega k)) :=
    fun k omega => shellDerivGauge_nonneg n (ShellField.translate z (omega k))
  have hmeas : ∀ k : ℤ, Measurable (fun omega : ShellSeq d =>
      localCubeDerivNorm n (ShellField.translate z (omega k)) +
        (3 : ℝ) ^ n *
          localCubeSecondDerivNorm n (ShellField.translate z (omega k))) :=
    fun k => ((measurable_shellDerivGauge n).comp
      (ShellField.measurable_translate z)).comp (measurable_pi_apply k)
  have hbigO : ∀ k ∈ Finset.Ioc n m,
      IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d =>
          localCubeDerivNorm n (ShellField.translate z (omega k)) +
            (3 : ℝ) ^ n *
              localCubeSecondDerivNorm n (ShellField.translate z (omega k)))
        (Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) := by
    intro k hk
    have hnk : n ≤ k := le_of_lt (Finset.mem_Ioc.mp hk).1
    exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg (hnonneg k)).1
      (isBigOWith_gammaSigma_shellDerivGauge_cube_translate M hnk z)
  have hfinite := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.Ioc n m)
    (X := fun k omega => localCubeDerivNorm n (ShellField.translate z (omega k)) +
      (3 : ℝ) ^ n *
        localCubeSecondDerivNorm n (ShellField.translate z (omega k)))
    (a := fun k : ℤ => Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) (σ := 2)
    (by norm_num) hs (fun k _ => Real.rpow_pos_of_pos (by norm_num) _) hbigO
    (fun k _ => hmeas k)
  have hwith : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        (localCubeDerivNorm n (ShellField.translate z (omega k)) +
          (3 : ℝ) ^ n *
            localCubeSecondDerivNorm n (ShellField.translate z (omega k))))
      (IndependentSums.gammaTriangleConst 2 *
        ∑ k ∈ Finset.Ioc n m, Real.rpow 3 ((M.gamma - 1) * (k : ℝ))) :=
    (Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (fun omega => Finset.sum_nonneg fun k _ => hnonneg k omega)).2 hfinite
  refine hwith.mono_scale (mul_le_mul_of_nonneg_left ?_
    IndependentSums.gammaTriangleConst_pos.le)
  exact sum_Ioc_rpow_gamma_sub_one_le M.shellPrefix.gamma_le_quarter (le_of_lt hnm)

/-- The translated summed first-derivative gauge estimate, with the
second-derivative term discarded. -/
theorem isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate (M : ABKModel d)
    {n m : ℤ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m,
        localCubeDerivNorm n (ShellField.translate z (omega k)))
      (IndependentSums.gammaTriangleConst 2 *
        (3 : ℝ) ^ ((M.gamma - 1) * (n : ℝ))) := by
  refine (isBigOWith_gammaSigma_shellDerivGaugeSum_Ioc_translate M hnm z).of_le
    fun omega => ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have h2 : 0 ≤ (3 : ℝ) ^ n *
      localCubeSecondDerivNorm n (ShellField.translate z (omega k)) :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) n).le
      (localCubeSecondDerivNorm_nonneg n (ShellField.translate z (omega k)))
  linarith

/-! ## The shell values at an arbitrary base point -/

/-- The translated value gauge dominates every matrix entry of the shell at the
translation vector itself, because the origin lies in every origin cube. -/
theorem abs_shell_entry_le_localCubeControl_translate (k : ℤ) (z : Vec d)
    (j : ShellField d) (i l : Fin d) :
    |j z i l| ≤ localCubeControl k (ShellField.translate z j) := by
  have h := abs_entry_le_localCubeControl k (ShellField.translate z j)
    (zero_mem_openCubeSet_originCube k) i l
  rwa [ShellField.translate_apply, zero_add] at h

/-- ABK26's `e.jk.O` read entrywise at an arbitrary point:
`|j_k(z)_{il}| ≤ O_{Γ₂}(3^{γk})`, with the amplitude independent of `z`. -/
theorem isBigO_gammaSigma_shell_entry (M : ABKModel d) (k : ℤ) (z : Vec d)
    (i l : Fin d) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => (omega k) z i l)
      ((3 : ℝ) ^ (M.gamma * (k : ℝ))) :=
  (isBigOWith_gammaSigma_localCubeControl_shell_translate M k z).of_le
    fun omega => abs_shell_entry_le_localCubeControl_translate k z (omega k) i l

/-- ABK26's "`j_k` is mean zero" at *every* point: the frozen (J1) mean-zero
field holds at every point of space, so transporting it through the frozen
marginal scaling law centres the shell values at every base point. -/
theorem integral_shell_entry_eq_zero (M : ABKModel d) (k : ℤ) (z : Vec d)
    (i l : Fin d) :
    ∫ omega : ShellSeq d, (omega k) z i l ∂M.P.toMeasure = 0 := by
  rw [integral_shellObservable_eq M k (fun j : ShellField d => j z i l)
    (ShellField.measurable_eval_entry z i l)]
  have hpt : ∀ j : ShellField d, (ShellField.triadicScale M.gamma k j) z i l =
      Real.rpow 3 (M.gamma * (k : ℝ)) * (j ((((3 : ℝ) ^ k)⁻¹) • z) i l) := by
    intro j
    rw [ShellField.triadicScale_apply]
    rfl
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul,
    integral_zeroShell_entry_eq_zero M ((((3 : ℝ) ^ k)⁻¹) • z) i l, mul_zero]

/-- The frozen shell independence, read on the scalar entries of the shell
values at an arbitrary point. -/
theorem iIndepFun_shell_entry (M : ABKModel d) (z : Vec d) (i l : Fin d) :
    ProbabilityTheory.iIndepFun
      (fun (k : ℤ) (omega : ShellSeq d) => (omega k) z i l) M.P.toMeasure :=
  M.shellPrefix.independent.comp
    (fun _ : ℤ => fun j : ShellField d => j z i l)
    (fun _ => ShellField.measurable_eval_entry z i l)

end

end Algsuperdiff.Section3.Provider.Stream
