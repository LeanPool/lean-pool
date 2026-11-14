/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGammaFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationEndpointSixteen

/-!
# LocalizationOscillationFullMesh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.lower.bound.oscillations` on the **full** mesh, and at the closure's carrier

ABK26, `e.lower.bound.oscillations`.  Two transports separate the proved interior
endpoint from the shape the Step-5 gauge junction consumes; the docstring of
`Closure.JunctionDischargeStepFiveDisplay` names both under "Carrier transports the
caller must supply on `hosc`".  This module performs both.

## 1.  Interior mesh to full mesh

`LocalizationOscillationEndpoint` averages over `interiorMesoCubeGrid`, whereas
the manuscript's display -- and `Closure.Step5GaugeEndpoint` -- averages over the
full mesh `3^n Zd cap cu_K`.  The three steps are

* `LocalizationFluctuationGammaFold.gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment`:
  the full grid fourth moment is the interior one plus a geometric boundary
  remainder carrying the square root of an **eighth**-moment envelope `E`;
* `gridFourthMomentRoot_le_add_rpow_of_le` below: the fourth root is
  subadditive, `(A + B)^{1/4} <= A^{1/4} + B^{1/4}`, so the remainder survives
  the outer root as its own fourth root -- the proved per-cube
  `gridFourthMomentRoot_le_add_of_le` does not serve, its majorant being
  pointwise on the grid rather than additive on the functional;
* `LocalizationFluctuationGammaFold.exists_gamma_threshold_mesh_boundary`:
  under the recurrence's own large-cube gate `10^10 gamma^{-1} <= K - m` the
  remainder is below `gamma^{100}`, hence its fourth root below `gamma^{25}`.

The interior half is taken at `gamma^{16}`
(`LocalizationOscillationEndpointSixteen`), so the sum is
`gamma^{16} + gamma^{25} <= 2 gamma^{16} <= gamma^{15}` for `gamma <= 1/2`, which
the standing `gamma <= 1/4` gives.

## 2.  Shell-sequence law to cutoff-sample law

The endpoint runs on `M.P.toMeasure`, the closure's carrier is
`(cutoffSampleLaw M).toMeasure`.  `Cutoff.map_cutoffSampleLaw_val` pushes the
second forward onto the first along `Subtype.val`, which is a **measurable
embedding** (`Cutoff.measurableSet_lowerTailGoodSet`), so
`MeasurableEmbedding.integral_map` transports every Bochner integral with **no**
measurability hypothesis on the integrand.  `gridFourthMoment_val_cutoffSampleLaw`
and `integral_cutoffSampleLaw_val` are the two resulting identities; both are
unconditional.

## 3.  The mesh index

`LocalizationGrid.mesoCubeGrid_eq_descendantsAtDepth` identifies the display's
grid `3^{nmesh} Zd cap cu_K` with the closure's `descendantsAtDepth cu_K j` at
`nmesh = K - j`.  The corollary is stated at the closure's index.

## What is proved

* `gridFourthMomentRoot_le_add_rpow_of_le` -- grid-level fourth-root
  subadditivity.
* `integral_cutoffSampleLaw_val`, `gridFourthMoment_val_cutoffSampleLaw`,
  `gridFourthMomentRoot_val_cutoffSampleLaw` -- the carrier transport,
  unconditional.
* `exists_gamma0_freshShellDirichlet_fullMeshOscillation_le_gamma_pow_fifteen` --
  the full-mesh endpoint on `M.P.toMeasure`.

## Binders

Beyond those of the proved endpoint -- the model gate, the induction state, the
four source gates of `e.recurrence.params`, the direction bound and the weak
formulation of `e.def.w` -- exactly two propositions are added, both **analytic
side conditions on the very objects the display is about**, and both instances
of `e.nablaw.in.L.eight`:

* `hmem8`, the `L^2`-in-the-sample membership of the fourth powers of the
  oscillation cells, i.e. the finiteness of their eighth moments;
* `hE`, an envelope for the eighth-moment **grid average** of the same cells.

`LocalizationFluctuationGridEighth` reduces `hE` to `fint_{cu_K} |u|^8` at the
tiling constant `1`, and thence to `‖u‖^8_{L8bar(cu_K)}`; the last step of that
reduction -- the finiteness of `E[(Chead + Tfluct)^4]` -- is at its producer
and is *not* performed here.  `E` is a parameter of the statement, quantified
before the threshold, so no smallness or normalization is assumed: the
threshold is **produced** from `E`, as `exists_gamma_threshold_mesh_boundary`
requires.

## Scope

There is no `sorry`.

## References

* ABK26, `e.lower.bound.oscillations`, `e.recurrence.params`,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Grid-level fourth-root subadditivity -/

/-- **The fourth root is subadditive on the grid functional.**  If the grid
fourth moment splits as `A + B`, its fourth root splits as `A^{1/4} + B^{1/4}`.

The proved `gridFourthMomentRoot_le_add_of_le` does not serve here: its
majorant is pointwise on the grid (`F R omega <= G R omega + H R omega`), whereas
the mesh transfer's remainder is additive on the *functional*, with no
pointwise representative.  only on `hA`, `hB` and `h`. -/
theorem gridFourthMomentRoot_le_add_rpow_of_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (I : Finset (TriadicCube d)) (F : TriadicCube d → Omega → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : gridFourthMoment mu I F ≤ A + B) :
    gridFourthMomentRoot mu I F ≤ A ^ ((4 : ℝ)⁻¹) + B ^ ((4 : ℝ)⁻¹) := by
  have hstep : gridFourthMoment mu I F ^ ((4 : ℝ)⁻¹) ≤ (A + B) ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_le_rpow (gridFourthMoment_nonneg mu I F) h (by norm_num)
  exact hstep.trans
    (Real.rpow_add_le_add_rpow hA hB (by norm_num) (by norm_num))

/-! ## The carrier transport -/

/-- **Unconditional.**  Every Bochner integral against the cutoff-sample law,
read through `Subtype.val`, is the corresponding integral against the
shell-sequence law.  `Subtype.val` is a measurable embedding onto the
lower-tail-good carrier, so no measurability hypothesis on the integrand is
needed. -/
theorem integral_cutoffSampleLaw_val (M : ABKModel d) (g : Cutoff.ShellSeq d → ℝ) :
    ∫ omega : Cutoff.CutoffSample d, g omega.val ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ omega : Cutoff.ShellSeq d, g omega ∂M.P.toMeasure := by
  have h := (MeasurableEmbedding.subtype_coe
      (Cutoff.measurableSet_lowerTailGoodSet d)).integral_map
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) g
  rw [← Cutoff.map_cutoffSampleLaw_val M]
  exact h.symm

/-- **Unconditional.**  The grid fourth-moment functional is carrier-independent
in the same sense. -/
theorem gridFourthMoment_val_cutoffSampleLaw (M : ABKModel d)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Cutoff.ShellSeq d → ℝ) :
    gridFourthMoment (Cutoff.cutoffSampleLaw M).toMeasure I
        (fun R omega => F R omega.val) =
      gridFourthMoment M.P.toMeasure I F := by
  unfold gridFourthMoment
  refine congrArg (cubeFamilyAverage I) (funext fun R => ?_)
  exact integral_cutoffSampleLaw_val M (fun omega => F R omega ^ (4 : ℝ))

/-- **Unconditional.**  The same for the outer fourth root. -/
theorem gridFourthMomentRoot_val_cutoffSampleLaw (M : ABKModel d)
    (I : Finset (TriadicCube d)) (F : TriadicCube d → Cutoff.ShellSeq d → ℝ) :
    gridFourthMomentRoot (Cutoff.cutoffSampleLaw M).toMeasure I
        (fun R omega => F R omega.val) =
      gridFourthMomentRoot M.P.toMeasure I F := by
  unfold gridFourthMomentRoot
  rw [gridFourthMoment_val_cutoffSampleLaw]

/-! ## The full-mesh endpoint -/

/-- **`e.lower.bound.oscillations` on the full mesh, below `gamma^{15}`.**

The interior endpoint of `LocalizationOscillationEndpointSixteen` at
`gamma^{16}`, plus the boundary remainder at `gamma^{25}`, on the manuscript's
own carrier `3^n Zd cap cu_K`.

on the binders of the proved endpoint together with the two
`e.nablaw.in.L.eight` side conditions `hmem8` and `hE`; see the module
docstring's binder census.  The threshold is **produced** from `E`. -/
theorem exists_gamma0_freshShellDirichlet_fullMeshOscillation_le_gamma_pow_fifteen
    (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {Eb : ℝ // 1 ≤ Eb}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              ∀ z₀ : Vec d,
                ∀ wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)),
                  (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD omega)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                        (m - (h : ℤ)) m e x)) →
                  (∀ R ∈ mesoCubeGrid d K
                      (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ)),
                    MemLp (fun omega : Cutoff.ShellSeq d =>
                      meshOscillationCell
                        (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
                        (wD omega).toH1Function.grad R ^ (4 : ℝ)) 2 M.P.toMeasure) →
                  cubeFamilyAverage (mesoCubeGrid d K
                      (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ)))
                      (fun R => ∫ omega : Cutoff.ShellSeq d,
                        meshOscillationCell
                          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
                          (wD omega).toH1Function.grad R ^ (8 : ℝ) ∂M.P.toMeasure) ≤ E →
                  gridFourthMomentRoot M.P.toMeasure
                      (mesoCubeGrid d K
                        (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ)))
                      (fun R omega => meshOscillationCell
                        (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ))
                        (wD omega).toH1Function.grad R) +
                      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
                        ((3 : ℝ) ^ ((recurrenceMesoScale recurrenceGapMultiplier M.gamma
                            m (h : ℤ) : ℤ) : ℝ) *
                          (∫ omega : Cutoff.ShellSeq d,
                            shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
                              ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                    M.gamma ^ (15 : ℕ) := by
  classical
  obtain ⟨g16, hg160, hg16q, hint16⟩ :=
    exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_sixteen d hd
  obtain ⟨gbd, hgbd0, hgbdq, hbd⟩ :=
    exists_gamma_threshold_mesh_boundary d (Real.sqrt E) (Real.sqrt_nonneg E)
  refine ⟨min g16 gbd, lt_min hg160 hgbd0, le_trans (min_le_left _ _) hg16q, ?_⟩
  intro M hMgamma m0 Eind hstate m K h hhpos hm0 hcstar hK e he z₀ wD hsol hmem8 hEle
  have hg16le : M.gamma ≤ g16 := le_trans hMgamma (min_le_left _ _)
  have hgbdle : M.gamma ≤ gbd := le_trans hMgamma (min_le_right _ _)
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hq : M.gamma ≤ 1 / 4 := le_trans hg16le hg16q
  have hgamma1 : M.gamma ≤ 1 := le_trans hq (by norm_num)
  -- the interior endpoint at `gamma^16`
  have hinterior := hint16 M hg16le m0 Eind hstate m K h hhpos hm0 hcstar hK e e he he
    z₀ wD hsol
  -- scale bookkeeping
  obtain ⟨nbuf, hnbuf⟩ : ∃ n : ℤ,
      n = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) := ⟨_, rfl⟩
  obtain ⟨Ngap, hNgap⟩ : ∃ N : ℕ,
      N = recurrenceGap recurrenceGapMultiplier M.gamma := ⟨_, rfl⟩
  rw [← hnbuf] at hinterior hmem8 hEle ⊢
  have hsum : nbuf + (Ngap : ℤ) = m - (h : ℤ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap _ _ _ _
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  have hKone : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by
    have hinv : (1 : ℝ) ≤ M.gamma⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hgamma0]
      linarith
    have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) := by norm_num
    exact one_le_mul_of_one_le_of_one_le h10 hinv
  have hmK1 : m ≤ K - 1 := by
    have hle : (m : ℝ) + 1 ≤ (K : ℝ) := by linarith
    have : m + 1 ≤ K := by exact_mod_cast hle
    omega
  have hnNle : nbuf + (Ngap : ℤ) ≤ K - 1 := by omega
  have hnle : nbuf ≤ K := by omega
  obtain ⟨pdep, hpdep⟩ : ∃ p : ℕ, (p : ℤ) = K - nbuf := ⟨(K - nbuf).toNat, by omega⟩
  have hKeq : K = nbuf + (pdep : ℤ) := by omega
  have houter : (m - (h : ℤ) - 1) + 1 = nbuf + (Ngap : ℤ) := by omega
  have hgp : Ngap ≤ pdep := by omega
  -- the boundary remainder
  have hZ : (pdep : ℤ) - (Ngap : ℤ) = K - m + (h : ℤ) := by omega
  have hgapR : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (pdep : ℝ) - (Ngap : ℝ) := by
    have hcast := congrArg (fun t : ℤ => (t : ℝ)) hZ
    have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    push_cast at hcast
    linarith
  have hbdry := hbd M.gamma hgamma0 hgbdle pdep Ngap hgapR
  -- the mesh transfer
  have hFnn : ∀ (R : TriadicCube d) (omega : Cutoff.ShellSeq d),
      0 ≤ meshOscillationCell nbuf (wD omega).toH1Function.grad R := fun R omega =>
    meshOscillationCell_nonneg _ _ _
  have htransfer := gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment
    M.P.toMeasure d (K := K) (n := nbuf) (outer := m - (h : ℤ) - 1) (p := pdep)
    (g := Ngap) hKeq houter hgp
    (fun R omega => meshOscillationCell nbuf (wD omega).toH1Function.grad R)
    hFnn hmem8 hEle
  -- the fourth root of the two pieces
  have hAnn : (0 : ℝ) ≤ gridFourthMoment M.P.toMeasure
      (interiorMesoCubeGrid d K nbuf (m - (h : ℤ) - 1))
      (fun R omega => meshOscillationCell nbuf (wD omega).toH1Function.grad R) :=
    gridFourthMoment_nonneg _ _ _
  have hBnn : (0 : ℝ) ≤ Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ Ngap / (3 : ℝ) ^ pdep)) *
      Real.sqrt E := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hroot := gridFourthMomentRoot_le_add_rpow_of_le M.P.toMeasure
    (mesoCubeGrid d K nbuf)
    (fun R omega => meshOscillationCell nbuf (wD omega).toH1Function.grad R)
    hAnn hBnn htransfer
  -- the boundary fourth root is below `gamma^25`
  have hbdry' : Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ Ngap / (3 : ℝ) ^ pdep)) * Real.sqrt E ≤
      M.gamma ^ (100 : ℕ) := by
    rw [mul_comm]
    exact hbdry
  have hpow25 : (M.gamma ^ (100 : ℕ)) ^ ((4 : ℝ)⁻¹) = M.gamma ^ (25 : ℕ) := by
    rw [← Real.rpow_natCast M.gamma 100, ← Real.rpow_mul hgamma0.le,
      show ((100 : ℕ) : ℝ) * (4 : ℝ)⁻¹ = ((25 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hbdroot : (Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ Ngap / (3 : ℝ) ^ pdep)) *
      Real.sqrt E) ^ ((4 : ℝ)⁻¹) ≤ M.gamma ^ (25 : ℕ) := by
    have hmono := Real.rpow_le_rpow hBnn hbdry' (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    rwa [hpow25] at hmono
  -- assemble
  have hsig0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
      ((3 : ℝ) ^ ((nbuf : ℤ) : ℝ) *
        (∫ omega : Cutoff.ShellSeq d,
          shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
            ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) := by
    have h1 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ :=
      (inv_pos.2 (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1).le
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((nbuf : ℤ) : ℝ) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have h3 : (0 : ℝ) ≤ (∫ omega : Cutoff.ShellSeq d,
        shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
          ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (shellDerivNormSum_nonneg _ _ _ _) _) _
    positivity
  have hfinal : M.gamma ^ (16 : ℕ) + M.gamma ^ (25 : ℕ) ≤ M.gamma ^ (15 : ℕ) := by
    have h2515 : M.gamma ^ (25 : ℕ) ≤ M.gamma ^ (16 : ℕ) :=
      pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
    have hsplit : M.gamma ^ (16 : ℕ) = M.gamma * M.gamma ^ (15 : ℕ) := by ring
    have h15nn : (0 : ℝ) ≤ M.gamma ^ (15 : ℕ) := by positivity
    have hhalf : 2 * M.gamma ≤ 1 := by linarith
    calc M.gamma ^ (16 : ℕ) + M.gamma ^ (25 : ℕ)
        ≤ M.gamma ^ (16 : ℕ) + M.gamma ^ (16 : ℕ) := add_le_add le_rfl h2515
      _ = 2 * M.gamma * M.gamma ^ (15 : ℕ) := by rw [hsplit]; ring
      _ ≤ 1 * M.gamma ^ (15 : ℕ) := mul_le_mul_of_nonneg_right hhalf h15nn
      _ = M.gamma ^ (15 : ℕ) := one_mul _
  unfold gridFourthMomentRoot at hroot hinterior ⊢
  linarith [hroot, hinterior, hbdroot, hfinal]

/-! ## The Step-5 `hosc` shape -/

/-- The full-mesh endpoint, read at the closure's own carrier
`(cutoffSampleLaw M).toMeasure`, at the closure's own grid
`descendantsAtDepth cu_K j`, and at the shell pair `(n, n + h)` with gauge
`shom_n^{-1}` -- i.e. at `m = n + h` in the parameters of the endpoint.  The
mesh scale `nmesh` and the depth `j` are tied by `hj : j = K - nmesh`, which is
the identification `LocalizationGrid.mesoCubeGrid_eq_descendantsAtDepth`, and
`nmesh` is the recurrence buffer of `e.recurrence.params` by `hnmesh`.

A caller instantiates `wD := Closure.alongIncrementPath n h w`, at which point
the conclusion is literally the `hosc` binder.

on the binders of the full-mesh endpoint; see the module docstring. -/
theorem exists_gamma0_freshShellDirichlet_step5MeshOscillation_le_gamma_pow_fifteen
    (d : ℕ) (hd : 2 ≤ d) (E : ℝ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {Eb : ℝ // 1 ≤ Eb}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (n : ℤ) (h : ℕ) (K j : ℕ) (nmesh : ℤ), 0 < h → n ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              ((K : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            nmesh =
              recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) →
            (j : ℤ) = (K : ℤ) - nmesh →
            ∀ e : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              ∀ z0 : Vec d,
                ∀ wD : Cutoff.ShellSeq d →
                    H10Function (openCubeSet (originCube d (K : ℤ))),
                  (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d (K : ℤ))) (wD omega)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e x)) →
                  (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
                    MemLp (fun omega : Cutoff.ShellSeq d =>
                      meshOscillationCell nmesh
                        (wD omega).toH1Function.grad R ^ (4 : ℝ)) 2 M.P.toMeasure) →
                  cubeFamilyAverage (descendantsAtDepth (originCube d (K : ℤ)) j)
                      (fun R => ∫ omega : Cutoff.ShellSeq d,
                        meshOscillationCell nmesh
                          (wD omega).toH1Function.grad R ^ (8 : ℝ) ∂M.P.toMeasure) ≤ E →
                  gridFourthMomentRoot (Cutoff.cutoffSampleLaw M).toMeasure
                      (descendantsAtDepth (originCube d (K : ℤ)) j)
                      (fun R omega => meshOscillationCell nmesh
                        (fun x => (wD omega.val).toH1Function.grad x) R) +
                      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
                        ((3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
                          (∫ omega : Cutoff.CutoffSample d,
                            shellDerivNormSum n (n + (h : ℤ)) z0 omega.val ^ (4 : ℝ)
                              ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                    M.gamma ^ (15 : ℕ) := by
  classical
  obtain ⟨gamma0, hg0pos, hg0quarter, hmain⟩ :=
    exists_gamma0_freshShellDirichlet_fullMeshOscillation_le_gamma_pow_fifteen d hd E
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate n h K j nmesh hhpos hn0 hcstar hK hnmesh hj e he z0 wD
    hsol hmem8 hEle
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hshift : n + (h : ℤ) - (h : ℤ) = n := by ring
  -- the mesh index
  have hnmeshle : nmesh ≤ (K : ℤ) := by omega
  have hgrid : mesoCubeGrid d (K : ℤ) nmesh =
      descendantsAtDepth (originCube d (K : ℤ)) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hnmeshle]
    congr 1
    omega
  -- the endpoint at `m = n + h`
  have hbase := hmain M hMgamma m0 Eind hstate (n + (h : ℤ)) (K : ℤ) h hhpos
    (by rw [hshift]; exact hn0) hcstar hK e he z0 wD
  rw [hshift, ← hnmesh] at hbase
  have hbase' := hbase hsol (by rw [hgrid]; exact hmem8) (by rw [hgrid]; exact hEle)
  -- the carrier transport
  have hEqRoot :
      gridFourthMomentRoot (Cutoff.cutoffSampleLaw M).toMeasure
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (fun R omega => meshOscillationCell nmesh
            (fun x => (wD omega.val).toH1Function.grad x) R) =
        gridFourthMomentRoot M.P.toMeasure (mesoCubeGrid d (K : ℤ) nmesh)
          (fun R omega => meshOscillationCell nmesh (wD omega).toH1Function.grad R) := by
    rw [← hgrid]
    exact gridFourthMomentRoot_val_cutoffSampleLaw M (mesoCubeGrid d (K : ℤ) nmesh)
      (fun R omega => meshOscillationCell nmesh (wD omega).toH1Function.grad R)
  have hEqGauge :
      (∫ omega : Cutoff.CutoffSample d,
          shellDerivNormSum n (n + (h : ℤ)) z0 omega.val ^ (4 : ℝ)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ omega : Cutoff.ShellSeq d,
          shellDerivNormSum n (n + (h : ℤ)) z0 omega ^ (4 : ℝ) ∂M.P.toMeasure :=
    integral_cutoffSampleLaw_val M
      (fun omega => shellDerivNormSum n (n + (h : ℤ)) z0 omega ^ (4 : ℝ))
  rw [hEqRoot, hEqGauge]
  exact hbase'

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
