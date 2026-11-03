/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111bDelayedMoments.DelayRowsSum

/-!
# Trilinear Hilbert transform: delayData
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal




/-- The scalar data of a delayed replacement on the use cells `S` below `J`
(blueprint lem:delay, lines 1549–1553): the residuals `D_h = (f_a - (P_h F_a)_phys) ψ_a` at
depth `h`, their predictor moments `μ_h` (constant on depth-`h` cells below every use cell, with
the same cell integrals, `eq:predictor-moment`), energy densities `e_h` of the successive
projection increments (`Σ_h ∫_J e_h ≤ E`, orthogonality of `P_{h+1} - P_h`), the private weight
`ε` (the increments of `μ` cost `ε e_h` below the use cells), the bound of `μ` on the use cells
of one depth (`Σ_I ‖1_I μ_h‖² ≤ ε E`), the
depth `N` of the projection family (the predictor is present down to depth `N`) and the input
mass `|f_a|²` (`∫_J |f_a|² ≤ E`, and the terminal residual is a contraction of it). -/
structure DelayData (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)) where
  /-- Terminal depth of the delayed approximation. -/
  N : ℤ
  /-- Depth-indexed scalar functions being approximated. -/
  D : ℤ → ℝ → ℂ
  /-- Delayed approximants at each depth. -/
  μ : ℤ → ℝ → ℂ
  /-- Pointwise error envelopes at each depth. -/
  e : ℤ → ℝ → ℝ
  /-- Relative error tolerance in the delayed approximation estimates. -/
  ε : ℝ
  /-- Integrated mass budget for the delayed approximation. -/
  E : ℝ
  ε_nonneg : 0 ≤ ε
  ε_le_one : ε ≤ 1
  sub : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2
  D_meas : ∀ h, Measurable (D h)
  D_memLp : ∀ I ∈ S, ∀ h, MemLp (D h) 2 (volume.restrict (dyadicGridCell G I.1 I.2))
  μ_memLp : ∀ I ∈ S, ∀ h, MemLp (μ h) 2 (volume.restrict (dyadicGridCell G I.1 I.2))
  μ_const : ∀ I ∈ S, ∀ j : ℕ, I.1 + j ≤ N → ∀ Q ∈ dyadicGeneration G I j,
    ∀ y ∈ dyadicGridCell G Q.1 Q.2, ∀ z ∈ dyadicGridCell G Q.1 Q.2, μ (I.1 + j) y = μ (I.1 + j) z
  moment : ∀ I ∈ S, ∀ j : ℕ, I.1 + j ≤ N → ∀ Q ∈ dyadicGeneration G I j,
    ∫ y in dyadicGridCell G Q.1 Q.2, D (I.1 + j) y =
      ∫ y in dyadicGridCell G Q.1 Q.2, μ (I.1 + j) y
  e_nonneg : ∀ h y, 0 ≤ e h y
  e_int : ∀ h, IntegrableOn (e h) (dyadicGridCell G J.1 J.2)
  e_D : ∀ I ∈ S, ∀ h, I.1 ≤ h → h < N →
    ∀ᵐ y ∂(volume.restrict (dyadicGridCell G I.1 I.2)), ‖D h y - D (h + 1) y‖ ^ 2 ≤ e h y
  e_μ : ∀ I ∈ S, ∀ h, I.1 ≤ h → h < N →
    ∀ᵐ y ∂(volume.restrict (dyadicGridCell G I.1 I.2)), ‖μ (h + 1) y - μ h y‖ ^ 2 ≤ ε * e h y
  energy : ∀ Hs : Finset ℤ, ∑ h ∈ Hs, ∫ y in dyadicGridCell G J.1 J.2, e h y ≤ E
  /-- Nonnegative integrable envelope controlling the terminal approximation energy. -/
  mass : ℝ → ℝ
  mass_nonneg : ∀ y, 0 ≤ mass y
  mass_int : IntegrableOn mass (dyadicGridCell G J.1 J.2)
  mass_le : ∫ y in dyadicGridCell G J.1 J.2, mass y ≤ E
  D_final : ∀ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖D N y‖ ^ 2 ≤
    4 * ∫ y in dyadicGridCell G I.1 I.2, mass y
  μ_energy : ∀ S' ⊆ S, ∀ s : ℤ, (∀ I ∈ S', I.1 = s) → ∀ h, s ≤ h → h ≤ N →
    ∑ I ∈ S', ∫ y in dyadicGridCell G I.1 I.2, ‖μ h y‖ ^ 2 ≤ ε * E

theorem DelayData.E_nonneg {G : RealDyadicGrid} {J : ℤ × ℤ} {S : Finset (ℤ × ℤ)}
    (Δ : DelayData G J S) : 0 ≤ Δ.E := by simpa using Δ.energy ∅

/-- The wave row of a cell input as a normalized set integral. -/
theorem norm_waveRow_sq (G : RealDyadicGrid) (κ : LocalKernelClass) (α ν : ℤ × ℤ → ℝ)
    (I : ℤ × ℤ) (g : ℝ → ℂ) :
    ‖∫ y, conj (waveRowTest G κ id α ν (fun _ => 1) I y) * g y‖ ^ 2 =
      (dyadicGridLength G I.1)⁻¹ * ‖∫ y in dyadicGridCell G I.1 I.2, g y *
        (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (α I) y *
          (Real.fourierChar (ν I * y) : ℂ))‖ ^ 2 := by
  have hr := dyadicGridLength_pos G I.1
  rw [integral_conj_waveRowTest]
  have hsupp := (classWave_props κ (a₀ := dyadicGridLeft G I.1 I.2) hr (α I)).2.1
  have e : ∫ y, classWave κ (dyadicGridLeft G (id I).1 (id I).2) (dyadicGridLength G (id I).1)
      (α I) y * (Real.fourierChar (ν I * y) : ℂ) * 1 * g y =
      ∫ y in dyadicGridCell G I.1 I.2, g y *
        (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (α I) y *
          (Real.fourierChar (ν I * y) : ℂ)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := dyadicGridCell G I.1 I.2)
      (fun y hy => by simp only [id]; rw [hsupp y hy]; ring)]
    exact setIntegral_congr_fun (dyadicGridCell_measurable G I.1 I.2) (fun y _ => by
      simp only [id]; ring)
  rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by simpa using (inv_pos.mpr hr).le)]
  rfl

/-- The delayed wave rows of a sub-collection: the telescoping part, with the start term left
explicit. -/
theorem delay_wave_rows (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (S' : Finset (ℤ × ℤ)) (hS' : S' ⊆ S)
    (α ν : ℤ × ℤ → ℝ) {A V : ℝ} (hA : ∀ I ∈ S', 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G I.1 * |α I|)) ^ 2 ≤ A)
    (hV : ∀ I ∈ S', dyadicGridLength G I.1 * |ν I| ≤ V) (hV0 : 0 ≤ V) (hA0 : 0 ≤ A)
    (K₀ : ℕ) (hN : ∀ I ∈ S', I.1 + K₀ ≤ Δ.N) :
    ∑ I ∈ S', ‖∫ y, conj (waveRowTest G κ id α ν (fun _ => 1) I y) * Δ.D (I.1 + K₀) y‖ ^ 2 ≤
      3 * ∑ I ∈ S', (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, Δ.μ (I.1 + K₀) y *
          (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (α I) y *
            (Real.fourierChar (ν I * y) : ℂ))‖ ^ 2 +
      3 * (9 * (2 * A + 4 * Real.pi * V + 2) * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * Δ.E := by
  set L := 2 * A + 4 * Real.pi * V + 2 with hL
  have hL0 : 0 ≤ L := by positivity
  simp_rw [norm_waveRow_sq]
  refine delay_rows_sum G J S' (fun I hI => Δ.sub I (hS' hI))
    (fun I y => classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (α I) y *
      (Real.fourierChar (ν I * y) : ℂ)) hL0
    (fun I hI => (classWave_mod_bounds κ (dyadicGridLength_pos G I.1) (α I) (ν I)
      (hA I hI)).1)
    (fun I hI y => ((classWave_mod_bounds κ (dyadicGridLength_pos G I.1) (α I) (ν I)
      (hA I hI)).2.1 y).trans (by rw [hL]; nlinarith [Real.pi_pos]))
    (fun I hI y z => ?_) Δ.D Δ.μ Δ.e Δ.ε_nonneg Δ.ε_le_one Δ.N K₀ hN
    (fun I hI => Δ.D_memLp I (hS' hI)) (fun I hI => Δ.μ_memLp I (hS' hI))
    (fun I hI => Δ.μ_const I (hS' hI)) (fun I hI => Δ.moment I (hS' hI))
    Δ.e_nonneg Δ.e_int (fun I hI => Δ.e_D I (hS' hI)) (fun I hI => Δ.e_μ I (hS' hI))
    Δ.energy Δ.mass Δ.mass_nonneg Δ.mass_int Δ.mass_le
    (fun I hI => Δ.D_final I (hS' hI))
  have hr := dyadicGridLength_pos G I.1
  refine ((classWave_mod_bounds κ hr (α I) (ν I) (hA I hI)).2.2 y z).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [div_le_div_iff_of_pos_right hr]
  have h1 := hV I hI
  have : 4 * Real.pi * (dyadicGridLength G I.1 * |ν I|) ≤ 4 * Real.pi * V :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [hL]; linarith

/-- The multiplicity constant of a fixed center over distinct depths. -/
noncomputable def depthMultConst : ℝ := 4 * (2 * Real.pi) ^ 2

theorem depthMultConst_pos : 0 < depthMultConst := by unfold depthMultConst; positivity

/-- The constant of the mean-zero part of the delayed replacement. -/
noncomputable def delayZeroConst (κ : LocalKernelClass) : ℝ :=
  linearScaleConst κ * depthMultConst * Real.sqrt (27 / (2 * depthMultConst))

theorem delayZeroConst_nonneg (κ : LocalKernelClass) : 0 ≤ delayZeroConst κ := by
  unfold delayZeroConst
  have := linearScaleConst_nonneg κ
  have := depthMultConst_pos
  positivity

theorem sum_image_const_snd {β : Type*} (S : Finset (ℤ × ℤ)) (c : ℝ) (f : ℤ × ℝ → β)
    [AddCommMonoid β] :
    ∑ p ∈ S.image (fun I => (I.1, c)), f p = ∑ s ∈ S.image Prod.fst, f (s, c) := by
  classical
  have e : S.image (fun I => (I.1, c)) = (S.image Prod.fst).image (fun s => (s, c)) := by
    rw [Finset.image_image]; rfl
  rw [e, Finset.sum_image (fun x _ y _ h => by simpa using h)]

/-- Blueprint lem:delay, proof lines 1558–1559 with the kernel `w_I` itself: the mean-zero
tensor rows of `w_I` against the delayed residuals, paired with the opposing Bessel rows,
cost `C (K₀ √ε + 2^{-K₀}) ‖F_a‖ ‖F_b‖`. -/
theorem delay_part_zero (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) {ψb : ℝ → ℂ} (hψbm : Measurable ψb) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzb : IsAdmissibleOpponent G J Fb zb Kb) (hzbm : ∀ I, Measurable (zb I))
    (hzbi : ∀ I ∈ S, IntegrableOn (zb I) (dyadicGridCell G I.1 I.2)) (K₀ : ℕ)
    (hN : ∀ I ∈ S, I.1 + K₀ ≤ Δ.N) :
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (0 * t) : ℂ)) a b (fun y => 1 * Δ.D (I.1 + K₀) y)
        (fun y => ψb y * zb I y)‖ ≤
      delayZeroConst κ * (K₀ * Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) * Real.sqrt Δ.E * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set M := depthMultConst with hMdef
  have hM0 : 0 < M := depthMultConst_pos
  set X := (K₀ : ℝ) * Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hX
  have hX0 : 0 ≤ X := by positivity
  have hE0 := Δ.E_nonneg
  set! Ka := Real.sqrt (27 / (2 * M)) * X * Real.sqrt Δ.E with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) with hNb
  have hNb0 : 0 ≤ Nb := Real.sqrt_nonneg _
  have hLn : ∀ v : Fin 2 → ℤ, 0 ≤ frequencyLength v := frequencyLength_nonneg
  have hinj : Set.InjOn (fun I : ℤ × ℤ => (id I, (0 : ℝ) / ((b : ℝ) - (a : ℝ)))) S :=
    fun I _ I' _ h => by simpa using congrArg Prod.fst h
  have hM : ∀ ξ, ∑ p ∈ S.image (fun I : ℤ × ℤ => ((id I).1, (0 : ℝ) / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G p.1 * (ξ - p.2)) ≤ M := by
    intro ξ
    rw [show (fun I : ℤ × ℤ => ((id I).1, (0 : ℝ) / ((b : ℝ) - (a : ℝ)))) =
      fun I => (I.1, (0 : ℝ) / ((b : ℝ) - (a : ℝ))) from rfl, sum_image_const_snd]
    have h := bumpMultiplier_depth_sum_le G (S.image Prod.fst) (ξ - (0 : ℝ) / ((b : ℝ) - (a : ℝ)))
    simpa [hMdef, depthMultConst] using h
  have hAa : ∀ v, ∀ I ∈ S, 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G I.1 *
        |slotPairFreqA a b (dyadicGridLength G I.1) v|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ =>
    charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G I.1).le (abs_nonneg _))
      (slotPairFreqA_le hab (dyadicGridLength_pos G I.1) v)
  have hAb : ∀ v, ∀ I ∈ S, 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G (id I).1 *
        |(fun I : ℤ × ℤ => slotPairFreqB a b (dyadicGridLength G (id I).1) v) I|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ =>
    charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G I.1).le (abs_nonneg _))
      (slotPairFreqB_le hab (dyadicGridLength_pos G I.1) v)
  -- the delayed rows
  have hxrow : ∀ v, ∑ I ∈ S, ‖∫ y, conj (waveRowTest G κ id
      (fun I => slotPairFreqA a b (dyadicGridLength G (id I).1) v)
      (fun I => -((0 : ℝ) / ((b : ℝ) - (a : ℝ)))) (fun _ => 1) I y) *
        Δ.D ((id I).1 + K₀) y‖ ^ 2 ≤
      Ka ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * 1 ^ 2 := by
    intro v
    set A := charWaveConst κ (frequencyLength v) with hA
    have hA2 : 2 ≤ A := two_le_charWaveConst κ (hLn v)
    have h := delay_wave_rows κ Δ S subset_rfl
      (fun I => slotPairFreqA a b (dyadicGridLength G I.1) v)
      (fun _ => -((0 : ℝ) / ((b : ℝ) - (a : ℝ)))) (A := A) (V := 0) (hAa v)
      (fun I _ => by simp) le_rfl (by linarith) K₀ hN
    set L := 2 * A + 4 * Real.pi * 0 + 2 with hL
    have hL3 : L ≤ 3 * A := by rw [hL]; linarith
    have hstart := delay_start_meanZero G J S Δ.sub
      (fun I y => classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
        (slotPairFreqA a b (dyadicGridLength G I.1) v) y *
          (Real.fourierChar (-((0 : ℝ) / ((b : ℝ) - (a : ℝ))) * y) : ℂ))
      (L := L) (by rw [hL]; linarith)
      (fun I _ => (classWave_mod_bounds κ (dyadicGridLength_pos G I.1) _ _ (hAa v I ‹_›)).1)
      (fun I _ y => ((classWave_mod_bounds κ (dyadicGridLength_pos G I.1) _ _
        (hAa v I ‹_›)).2.1 y).trans (by rw [hL]; linarith))
      (fun I _ => by
        have hr := dyadicGridLength_pos G I.1
        obtain ⟨-, hsupp, hint, -, -⟩ := classWave_props κ
          (a₀ := dyadicGridLeft G I.1 I.2) hr (slotPairFreqA a b (dyadicGridLength G I.1) v)
        simp only [zero_div, neg_zero, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one,
          mul_one]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := dyadicGridCell G I.1 I.2)
          (fun y hy => hsupp y hy)).trans hint)
      Δ.μ Δ.e Δ.ε_nonneg (Δ.μ_memLp)
      (fun I hI y hy z hz => by
        have h0 := Δ.μ_const I hI 0 (by have := hN I hI; omega) I
          (by simp [dyadicGeneration]) y hy z hz
        simpa using h0)
      Δ.e_nonneg Δ.e_int Δ.N K₀ hN Δ.e_μ Δ.energy
    simp only [id] at h ⊢
    have hstart' : 3 * ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, Δ.μ (I.1 + K₀) y *
          (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
            (slotPairFreqA a b (dyadicGridLength G I.1) v) y *
            (Real.fourierChar (-((0 : ℝ) / ((b : ℝ) - (a : ℝ))) * y) : ℂ))‖ ^ 2 ≤
        3 * ((L * K₀) ^ 2 * Δ.ε * Δ.E) := by linarith
    have hεs : Real.sqrt Δ.ε ^ 2 = Δ.ε := Real.sq_sqrt Δ.ε_nonneg
    have hp0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ K₀ := by positivity
    have hK0 : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
    have hsum : 3 * ((L * K₀) ^ 2 * Δ.ε * Δ.E) + 3 * (9 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * Δ.E ≤
        27 * A ^ 2 * X ^ 2 * Δ.E := by
      have hL0 : 0 ≤ L := by rw [hL]; linarith
      have hLA : L ^ 2 ≤ 9 * A ^ 2 := by
        calc L ^ 2 ≤ (3 * A) ^ 2 := pow_le_pow_left₀ hL0 hL3 2
          _ = 9 * A ^ 2 := by ring
      have hX2 : (K₀ : ℝ) ^ 2 * Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2 ≤ X ^ 2 := by
        have e : ((K₀ : ℝ) * Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) ^ 2 =
            (K₀ : ℝ) ^ 2 * Real.sqrt Δ.ε ^ 2 + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2 +
              18 * ((K₀ : ℝ) * Real.sqrt Δ.ε * (2 : ℝ)⁻¹ ^ K₀) := by ring
        rw [hX, e, hεs]
        have := mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg Δ.ε)) hp0
        linarith
      calc 3 * ((L * K₀) ^ 2 * Δ.ε * Δ.E) + 3 * (9 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * Δ.E
          = 3 * L ^ 2 * ((K₀ : ℝ) ^ 2 * Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2) * Δ.E := by ring
        _ ≤ 3 * (9 * A ^ 2) * X ^ 2 * Δ.E := by
            have := mul_le_mul hLA hX2
              (add_nonneg (mul_nonneg (sq_nonneg _) Δ.ε_nonneg) (by positivity)) (by positivity)
            nlinarith only [hE0, this]
        _ = 27 * A ^ 2 * X ^ 2 * Δ.E := by ring
    have hKa2 : Ka ^ 2 * (A * 1 * Real.sqrt (2 * M)) ^ 2 * 1 ^ 2 = 27 * A ^ 2 * X ^ 2 * Δ.E := by
      have s1 : Real.sqrt (27 / (2 * M)) ^ 2 = 27 / (2 * M) := Real.sq_sqrt (by positivity)
      have s2 : Real.sqrt Δ.E ^ 2 = Δ.E := Real.sq_sqrt hE0
      have s3 : Real.sqrt (2 * M) ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
      rw [hKa]
      simp only [mul_pow, s1, s2, s3, one_pow, mul_one]
      field_simp
    rw [hKa2]
    linarith
  have hyrow : ∀ v, ∑ I ∈ S, ‖∫ y, conj (waveRowTest G κ id
      (fun I => slotPairFreqB a b (dyadicGridLength G (id I).1) v)
      (fun I => (0 : ℝ) / ((b : ℝ) - (a : ℝ))) ψb I y) * zb (id I) y‖ ^ 2 ≤
      Kb ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * Nb ^ 2 := by
    intro v
    have h := hzb (ℤ × ℤ) (waveRowFamily G κ id S
      (fun I => slotPairFreqB a b (dyadicGridLength G (id I).1) v)
      (fun _ => (0 : ℝ) / ((b : ℝ) - (a : ℝ))) hinj hψbm hψb
      (two_le_charWaveConst κ (hLn v)) (hAb v) hM) (fun I hI => Δ.sub I hI)
    rw [hNb, Real.sq_sqrt (setIntegral_nonneg (dyadicGridCell_measurable G J.1 J.2)
      fun _ _ => by positivity)]
    exact h
  have hzai : ∀ I ∈ S, IntegrableOn (Δ.D (I.1 + K₀)) (dyadicGridCell G I.1 I.2) := by
    intro I hI
    have := cell_isFiniteMeasure G I.1 I.2
    exact (Δ.D_memLp I hI _).integrable one_le_two
  have h := linear_phase_scale_sum_rows G κ id S w hw hab (fun _ => 0) hinj
    (ψa := fun _ => 1) measurable_const hψbm (fun _ => le_of_eq norm_one) hψb
    (za := fun I => Δ.D (I.1 + K₀)) (zb := zb) hKa0 hKb zero_le_one hNb0
    (fun I => Δ.D_meas _) hzbm hzai hzbi hM hxrow hyrow
  refine h.trans (le_of_eq ?_)
  rw [hKa, delayZeroConst]
  ring

/-- The constant of the one-depth linear-phase part of the delayed replacement. -/
noncomputable def delayLinConst (κ : LocalKernelClass) : ℝ :=
  linearScaleConst κ * (2 * Real.pi) ^ 2 * Real.sqrt (147 / (2 * (2 * Real.pi) ^ 2))

theorem delayLinConst_nonneg (κ : LocalKernelClass) : 0 ≤ delayLinConst κ := by
  unfold delayLinConst; have := linearScaleConst_nonneg κ; positivity

/-- The delayed residual rows at one depth for a fixed linear phase. -/
theorem delay_linear_xrow (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (S' : Finset (ℤ × ℤ)) (hS' : S' ⊆ S) (s : ℤ)
    (hs : ∀ I ∈ S', I.1 = s) {a b : Fin 4} (hab : a ≠ b) (γ : ℝ) (K₀ : ℕ)
    (hN : ∀ I ∈ S', I.1 + K₀ ≤ Δ.N) (v : Fin 2 → ℤ) :
    ∑ I ∈ S', ‖∫ y, conj (waveRowTest G κ id
      (fun I => slotPairFreqA a b (dyadicGridLength G (id I).1) v)
      (fun _ => -(γ / ((b : ℝ) - (a : ℝ)))) (fun _ => 1) I y) *
        Δ.D ((id I).1 + K₀) y‖ ^ 2 ≤
      (Real.sqrt (147 / (2 * (2 * Real.pi) ^ 2)) * (1 + dyadicGridLength G s * |γ|) *
        (Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) * Real.sqrt Δ.E) ^ 2 *
      (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * (2 * Real.pi) ^ 2)) ^ 2 *
        1 ^ 2 := by
  set M := (2 * Real.pi) ^ 2 with hMdef
  have hM0 : 0 < M := by positivity
  set r := dyadicGridLength G s with hr
  have hr0 : 0 < r := dyadicGridLength_pos G s
  have hrI : ∀ I ∈ S', dyadicGridLength G I.1 = r := fun I hI => by rw [hs I hI]
  set Y := Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hY
  have hY0 : 0 ≤ Y := by positivity
  have hE0 := Δ.E_nonneg
  set g := 1 + r * |γ| with hg
  have hg1 : 1 ≤ g := by rw [hg]; nlinarith [abs_nonneg γ]
  set Ka := Real.sqrt (147 / (2 * M)) * g * Y * Real.sqrt Δ.E with hKa
  have hLn : ∀ v : Fin 2 → ℤ, 0 ≤ frequencyLength v := frequencyLength_nonneg
  have hd1 : 1 ≤ |((b : ℝ) - (a : ℝ))| := one_le_abs_fin_sub hab
  have hνr : r * |γ / ((b : ℝ) - (a : ℝ))| ≤ r * |γ| := by
    rw [abs_div]
    exact mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hd1) hr0.le
  have hAa : ∀ v, ∀ I ∈ S', 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G I.1 *
        |slotPairFreqA a b (dyadicGridLength G I.1) v|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ =>
    charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G I.1).le (abs_nonneg _))
      (slotPairFreqA_le hab (dyadicGridLength_pos G I.1) v)
  set A := charWaveConst κ (frequencyLength v) with hA
  have hA2 : 2 ≤ A := two_le_charWaveConst κ (hLn v)
  have h := delay_wave_rows κ Δ S' hS'
    (fun I => slotPairFreqA a b (dyadicGridLength G I.1) v)
    (fun _ => -(γ / ((b : ℝ) - (a : ℝ)))) (A := A) (V := r * |γ|) (hAa v)
    (fun I hI => by rw [hrI I hI, abs_neg]; exact hνr) (by positivity) (by linarith) K₀ hN
  set L := 2 * A + 4 * Real.pi * (r * |γ|) + 2 with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hL7 : L ≤ 7 * A * g := by
    have h1 : 4 * Real.pi * (r * |γ|) ≤ 7 * A * (r * |γ|) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [Real.pi_lt_d2]
    calc L = 2 * A + 4 * Real.pi * (r * |γ|) + 2 := hL
      _ ≤ 7 * A + 7 * A * (r * |γ|) := by linarith
      _ = 7 * A * g := by rw [hg]; ring
  have hstart := delay_start_depth G S'
    (fun I y => classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
      (slotPairFreqA a b (dyadicGridLength G I.1) v) y *
        (Real.fourierChar (-(γ / ((b : ℝ) - (a : ℝ))) * y) : ℂ))
    hL0 (fun I hI y => ((classWave_mod_bounds κ (dyadicGridLength_pos G I.1) _ _
      (hAa v I hI)).2.1 y).trans (by rw [hL]; nlinarith only [Real.pi_pos, abs_nonneg γ, hg1, hA2]))
    (Δ.μ (s + K₀)) (fun I hI => Δ.μ_memLp I (hS' hI) _)
  have hμe : ∑ I ∈ S', ∫ y in dyadicGridCell G I.1 I.2, ‖Δ.μ (s + K₀) y‖ ^ 2 ≤ Δ.ε * Δ.E := by
    rcases S'.eq_empty_or_nonempty with he | ⟨I₀, hI₀⟩
    · rw [he, Finset.sum_empty]; exact mul_nonneg Δ.ε_nonneg Δ.E_nonneg
    · exact Δ.μ_energy S' hS' s hs (s + K₀) (by omega) (by
        have := hN I₀ hI₀; rw [hs I₀ hI₀] at this; exact this)
  have hcongr : ∑ I ∈ S', (dyadicGridLength G I.1)⁻¹ *
      ‖∫ y in dyadicGridCell G I.1 I.2, Δ.μ (I.1 + K₀) y *
        (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
          (slotPairFreqA a b (dyadicGridLength G I.1) v) y *
          (Real.fourierChar (-(γ / ((b : ℝ) - (a : ℝ))) * y) : ℂ))‖ ^ 2 =
      ∑ I ∈ S', (dyadicGridLength G I.1)⁻¹ *
      ‖∫ y in dyadicGridCell G I.1 I.2, Δ.μ (s + K₀) y *
        (classWave κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
          (slotPairFreqA a b (dyadicGridLength G I.1) v) y *
          (Real.fourierChar (-(γ / ((b : ℝ) - (a : ℝ))) * y) : ℂ))‖ ^ 2 :=
    Finset.sum_congr rfl fun I hI => by rw [hs I hI]
  simp only [id] at h ⊢
  rw [hcongr] at h
  have hεs : Real.sqrt Δ.ε ^ 2 = Δ.ε := Real.sq_sqrt Δ.ε_nonneg
  have hp0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ K₀ := by positivity
  have hsum : 3 * (L ^ 2 * (Δ.ε * Δ.E)) + 3 * (9 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * Δ.E ≤
      147 * A ^ 2 * g ^ 2 * Y ^ 2 * Δ.E := by
    have hLA : L ^ 2 ≤ 49 * A ^ 2 * g ^ 2 := by
      calc L ^ 2 ≤ (7 * A * g) ^ 2 := pow_le_pow_left₀ hL0 hL7 2
        _ = 49 * A ^ 2 * g ^ 2 := by ring
    have hY2 : Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2 ≤ Y ^ 2 := by
      have e : (Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) ^ 2 =
          Real.sqrt Δ.ε ^ 2 + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2 +
            18 * (Real.sqrt Δ.ε * (2 : ℝ)⁻¹ ^ K₀) := by ring
      rw [hY, e, hεs]
      have := mul_nonneg (Real.sqrt_nonneg Δ.ε) hp0
      linarith
    calc 3 * (L ^ 2 * (Δ.ε * Δ.E)) + 3 * (9 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * Δ.E
        = 3 * L ^ 2 * (Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2) * Δ.E := by ring
      _ ≤ 3 * (49 * A ^ 2 * g ^ 2) * Y ^ 2 * Δ.E := by
          have h1 := mul_le_mul hLA hY2 (add_nonneg Δ.ε_nonneg (by positivity)) (by positivity)
          have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1
            (by norm_num : (0 : ℝ) ≤ 3)) hE0
          calc 3 * L ^ 2 * (Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2) * Δ.E
              = 3 * (L ^ 2 * (Δ.ε + 81 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2)) * Δ.E := by ring
            _ ≤ 3 * (49 * A ^ 2 * g ^ 2 * Y ^ 2) * Δ.E := h2
            _ = _ := by ring
      _ = 147 * A ^ 2 * g ^ 2 * Y ^ 2 * Δ.E := by ring
  have hKa2 : Ka ^ 2 * (A * 1 * Real.sqrt (2 * M)) ^ 2 * 1 ^ 2 =
      147 * A ^ 2 * g ^ 2 * Y ^ 2 * Δ.E := by
    have s1 : Real.sqrt (147 / (2 * M)) ^ 2 = 147 / (2 * M) := Real.sq_sqrt (by positivity)
    have s2 : Real.sqrt Δ.E ^ 2 = Δ.E := Real.sq_sqrt hE0
    have s3 : Real.sqrt (2 * M) ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
    rw [hKa]
    simp only [mul_pow, s1, s2, s3, one_pow, mul_one]
    field_simp
  rw [hKa2]
  have hst : L ^ 2 * ∑ I ∈ S', ∫ y in dyadicGridCell G I.1 I.2, ‖Δ.μ (s + K₀) y‖ ^ 2 ≤
      L ^ 2 * (Δ.ε * Δ.E) := mul_le_mul_of_nonneg_left hμe (by positivity)
  linarith

/-- Blueprint lem:delay, proof lines 1558 and 1562 at one depth: for a fixed linear phase
`e(γ t)` on the use cells of a single depth `s`, the delayed residual rows (start term
`‖1_J μ_H‖ ≤ √ε ‖F_a‖`) paired with the opposing Bessel rows cost
`C (1 + |I_s| |γ|) (√ε + 2^{-K₀}) ‖F_a‖ ‖F_b‖`. -/
theorem delay_linear_depth (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (S' : Finset (ℤ × ℤ)) (hS' : S' ⊆ S) (s : ℤ)
    (hs : ∀ I ∈ S', I.1 = s) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S', IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) (γ : ℝ) {ψb : ℝ → ℂ} (hψbm : Measurable ψb)
    (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzb : IsAdmissibleOpponent G J Fb zb Kb) (hzbm : ∀ I, Measurable (zb I))
    (hzbi : ∀ I ∈ S', IntegrableOn (zb I) (dyadicGridCell G I.1 I.2)) (K₀ : ℕ)
    (hN : ∀ I ∈ S', I.1 + K₀ ≤ Δ.N) :
    ∑ I ∈ S', dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (γ * t) : ℂ)) a b (fun y => 1 * Δ.D (I.1 + K₀) y)
        (fun y => ψb y * zb I y)‖ ≤
      delayLinConst κ * (1 + dyadicGridLength G s * |γ|) *
        (Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) * Real.sqrt Δ.E * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set M := (2 * Real.pi) ^ 2 with hMdef
  have hM0 : 0 < M := by positivity
  set r := dyadicGridLength G s with hr
  have hr0 : 0 < r := dyadicGridLength_pos G s
  have hrI : ∀ I ∈ S', dyadicGridLength G I.1 = r := fun I hI => by rw [hs I hI]
  set Y := Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hY
  have hY0 : 0 ≤ Y := by positivity
  have hE0 := Δ.E_nonneg
  set g := 1 + r * |γ| with hg
  have hg1 : 1 ≤ g := by rw [hg]; nlinarith [abs_nonneg γ]
  set! Ka := Real.sqrt (147 / (2 * M)) * g * Y * Real.sqrt Δ.E with hKa
  have hKa0 : 0 ≤ Ka := by positivity
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) with hNb
  have hNb0 : 0 ≤ Nb := Real.sqrt_nonneg _
  have hLn : ∀ v : Fin 2 → ℤ, 0 ≤ frequencyLength v := frequencyLength_nonneg
  have hd1 : 1 ≤ |((b : ℝ) - (a : ℝ))| := one_le_abs_fin_sub hab
  set! ν := γ / ((b : ℝ) - (a : ℝ)) with hν
  have hνr : r * |ν| ≤ r * |γ| := by
    rw [hν, abs_div]
    exact mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hd1) hr0.le
  have hinj : Set.InjOn (fun I : ℤ × ℤ => (id I, γ / ((b : ℝ) - (a : ℝ)))) S' :=
    fun I _ I' _ h => by simpa using congrArg Prod.fst h
  have hM : ∀ ξ, ∑ p ∈ S'.image (fun I : ℤ × ℤ => ((id I).1, γ / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G p.1 * (ξ - p.2)) ≤ M := by
    intro ξ
    rcases S'.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.image_empty, Finset.sum_empty]; positivity
    have himg : S'.image (fun I : ℤ × ℤ => ((id I).1, γ / ((b : ℝ) - (a : ℝ)))) =
        {(s, γ / ((b : ℝ) - (a : ℝ)))} := by
      ext p
      simp only [Finset.mem_image, Finset.mem_singleton, id]
      constructor
      · rintro ⟨I, hI, rfl⟩; rw [hs I hI]
      · rintro rfl
        obtain ⟨I, hI⟩ := hne
        exact ⟨I, hI, by rw [hs I hI]⟩
    rw [himg, Finset.sum_singleton]
    exact bumpMultiplier_le _
  have hAa : ∀ v, ∀ I ∈ S', 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G I.1 *
        |slotPairFreqA a b (dyadicGridLength G I.1) v|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ =>
    charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G I.1).le (abs_nonneg _))
      (slotPairFreqA_le hab (dyadicGridLength_pos G I.1) v)
  have hAb : ∀ v, ∀ I ∈ S', 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G (id I).1 *
        |(fun I : ℤ × ℤ => slotPairFreqB a b (dyadicGridLength G (id I).1) v) I|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ =>
    charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G I.1).le (abs_nonneg _))
      (slotPairFreqB_le hab (dyadicGridLength_pos G I.1) v)
  have hxrow : ∀ v, ∑ I ∈ S', ‖∫ y, conj (waveRowTest G κ id
      (fun I => slotPairFreqA a b (dyadicGridLength G (id I).1) v)
      (fun _ => -(γ / ((b : ℝ) - (a : ℝ)))) (fun _ => 1) I y) *
        Δ.D ((id I).1 + K₀) y‖ ^ 2 ≤
      Ka ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * 1 ^ 2 :=
    fun v => delay_linear_xrow κ Δ S' hS' s hs hab γ K₀ hN v
  have hyrow : ∀ v, ∑ I ∈ S', ‖∫ y, conj (waveRowTest G κ id
      (fun I => slotPairFreqB a b (dyadicGridLength G (id I).1) v)
      (fun I => γ / ((b : ℝ) - (a : ℝ))) ψb I y) * zb (id I) y‖ ^ 2 ≤
      Kb ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * Nb ^ 2 := by
    intro v
    have h := hzb (ℤ × ℤ) (waveRowFamily G κ id S'
      (fun I => slotPairFreqB a b (dyadicGridLength G (id I).1) v)
      (fun _ => γ / ((b : ℝ) - (a : ℝ))) hinj hψbm hψb
      (two_le_charWaveConst κ (hLn v)) (hAb v) hM) (fun I hI => Δ.sub I (hS' hI))
    rw [hNb, Real.sq_sqrt (setIntegral_nonneg (dyadicGridCell_measurable G J.1 J.2)
      fun _ _ => by positivity)]
    exact h
  have hzai : ∀ I ∈ S', IntegrableOn (Δ.D (I.1 + K₀)) (dyadicGridCell G I.1 I.2) := by
    intro I hI
    have := cell_isFiniteMeasure G I.1 I.2
    exact (Δ.D_memLp I (hS' hI) _).integrable one_le_two
  have h := linear_phase_scale_sum_rows G κ id S' w hw hab (fun _ => γ) hinj
    (ψa := fun _ => 1) measurable_const hψbm (fun _ => le_of_eq norm_one) hψb
    (za := fun I => Δ.D (I.1 + K₀)) (zb := zb) hKa0 hKb zero_le_one hNb0
    (fun I => Δ.D_meas _) hzbm hzai hzbi hM hxrow hyrow
  refine h.trans (le_of_eq ?_)
  rw [hKa, delayLinConst]
  ring

/-- The cut-off chirp `(e(D u²) - 1) χ(u)`, the normalized form of `e(λ_* t²) - 1` on a cell
of length `r` with `D = λ_* r²` (blueprint lem:delay, line 1562). -/
noncomputable def chirpBump (χ : ℝ → ℝ) (D : ℝ) (u : ℝ) : ℂ :=
  ((Real.fourierChar (D * (u * u)) : ℂ) - 1) * (χ u : ℂ)

theorem contDiff_fourierChar_comp {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => (Real.fourierChar (φ s) : ℂ)) := by
  have h : (fun s => (Real.fourierChar (φ s) : ℂ)) =
      fun s => Complex.exp (((2 * Real.pi * φ s : ℝ) : ℂ) * Complex.I) := by
    funext s; rw [Real.fourierChar_apply]
  rw [h]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul hφ)).mul contDiff_const)

/-- Geometric derivative bounds of the cut-off chirp with the smallness factor `|D|`. -/
theorem chirpBump_geomBound {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {Cχ : ℝ}
    (hCχ : ∀ i ≤ 3, ∀ x, |iteratedDeriv i χ x| ≤ Cχ) (D : ℝ) {u : ℝ} (hu : |u| ≤ 3) :
    GeomBound (chirpBump χ D) u ((18 * Real.pi * |D| + 2 * Real.pi * (2 * |D| * 3) * 1) * Cχ)
      ((1 + ((0 + (0 + 1)) + (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 *
        (0 + (1 + 1))))) + 1) 3 := by
  have hpi := Real.pi_pos
  have hid : GeomBound (fun s : ℝ => s) u 3 1 3 := GeomBound.id_real u hu (by norm_num) 3
  have hsq : GeomBound (fun s : ℝ => s * s) u (3 * 3) (1 + 1) 3 :=
    GeomBound.mul contDiff_id contDiff_id zero_le_one hid hid
  have hc : GeomBound (fun _ : ℝ => D) u ‖D‖ 0 3 := GeomBound.const D u le_rfl 3
  have hφ0s : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => D * (s * s)) :=
    contDiff_const.mul (contDiff_id.mul contDiff_id)
  have hφ0 : GeomBound (fun s : ℝ => D * (s * s)) u (‖D‖ * (3 * 3)) (0 + (1 + 1)) 3 :=
    GeomBound.mul contDiff_const (contDiff_id.mul contDiff_id) le_rfl hc hsq
  rw [Real.norm_eq_abs] at hφ0
  have hE := GeomBound.fourierChar hφ0s (by norm_num) hφ0
  have hEs : ContDiff ℝ (⊤ : ℕ∞) (fun s => (Real.fourierChar (D * (s * s)) : ℂ)) :=
    contDiff_fourierChar_comp hφ0s
  -- the derivative `p E`
  have hlin : GeomBound (fun s : ℝ => (2 * D) * s) u (‖2 * D‖ * 3) (0 + 1) 3 :=
    GeomBound.mul contDiff_const contDiff_id le_rfl (GeomBound.const _ u le_rfl 3) hid
  have hlinC := GeomBound.ofReal (contDiff_const.mul contDiff_id) hlin
  have hp : GeomBound (fun s : ℝ => (2 * Real.pi * Complex.I) * (((2 * D) * s : ℝ) : ℂ)) u
      (‖2 * Real.pi * Complex.I‖ * (‖2 * D‖ * 3)) (0 + (0 + 1)) 3 :=
    GeomBound.mul contDiff_const (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)) le_rfl (GeomBound.const _ u le_rfl 3) hlinC
  have hps : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (2 * Real.pi * Complex.I) * (((2 * D) * s : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))
  have hpE := GeomBound.mul hps hEs (by norm_num) hp hE
  have hnorm : ‖2 * Real.pi * Complex.I‖ * (‖2 * D‖ * 3) = 2 * Real.pi * (2 * |D| * 3) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hpi, Complex.norm_ofNat]; ring
  rw [hnorm] at hpE
  -- the derivative of the chirp
  set g : ℝ → ℂ := fun s => (Real.fourierChar (D * (s * s)) : ℂ) - 1 with hg
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hEs.sub contDiff_const
  have hderiv : deriv g = fun s =>
      (2 * Real.pi * Complex.I) * (((2 * D) * s : ℝ) : ℂ) *
        (Real.fourierChar (D * (s * s)) : ℂ) := by
    funext s
    have h1 : HasDerivAt (fun s : ℝ => D * (s * s)) ((2 * D) * s) s :=
      (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul D).congr_deriv (by ring)
    have h2 := (Real.hasDerivAt_fourierChar (D * (s * s))).scomp s h1
    have h3 : HasDerivAt g (((2 * D) * s) •
        (2 * Real.pi * Complex.I * (Real.fourierChar (D * (s * s)) : ℂ))) s :=
      h2.sub_const (1 : ℂ)
    rw [h3.deriv, Complex.real_smul]
    ring
  have hRE0 : 0 ≤ (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 * (0 + (1 + 1))) := by
    positivity
  have hgb : GeomBound g u (18 * Real.pi * |D| + 2 * Real.pi * (2 * |D| * 3) * 1)
      (1 + ((0 + (0 + 1)) + (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 *
        (0 + (1 + 1))))) 3 := by
    intro i hi
    set R := 1 + ((0 + (0 + 1)) + (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 *
        (0 + (1 + 1)))) with hR
    have hR1 : 1 ≤ R := by rw [hR]; linarith
    have hK0 : 0 ≤ 2 * Real.pi * (2 * |D| * 3) * 1 := by positivity
    rcases i with _ | k
    · rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      have h := norm_fourierChar_sub_le (D * (u * u)) 0
      have h0 : ((Real.fourierChar 0 : Circle) : ℂ) = 1 := by simp
      rw [h0, sub_zero] at h
      have hu2 : |D * (u * u)| ≤ 9 * |D| := by
        rw [abs_mul, abs_mul]
        have : |u| * |u| ≤ 9 := by nlinarith [abs_nonneg u]
        nlinarith [abs_nonneg D]
      calc ‖g u‖ ≤ 2 * Real.pi * |D * (u * u)| := h
        _ ≤ 2 * Real.pi * (9 * |D|) := mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ _ := by nlinarith [abs_nonneg D]
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', hderiv,
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h := hpE k (by omega)
      have hRk : (0 + (0 + 1) + (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 *
          (0 + (1 + 1)))) ^ k ≤ R ^ (k + 1) := by
        calc _ ≤ R ^ k := pow_le_pow_left₀ (by positivity) (by rw [hR]; linarith) k
          _ ≤ R ^ (k + 1) := pow_le_pow_right₀ hR1 (by omega)
      calc _ ≤ 2 * Real.pi * (2 * |D| * 3) * 1 * (0 + (0 + 1) + (3 + 1) * (2 * Real.pi) *
            (max (|D| * (3 * 3)) 1 * (0 + (1 + 1)))) ^ k := h
        _ ≤ 2 * Real.pi * (2 * |D| * 3) * 1 * R ^ (k + 1) :=
            mul_le_mul_of_nonneg_left hRk hK0
        _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg D])
            (pow_nonneg (by linarith) _)
  have hχb : GeomBound χ u Cχ 1 3 := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, one_pow, mul_one, Real.norm_eq_abs]
    exact hCχ i hi u
  have hχC := GeomBound.ofReal hχ hχb
  exact GeomBound.mul hgs (Complex.ofRealCLM.contDiff.comp hχ) (by positivity) hgb hχC

/-- The one-dimensional frequency weight `Σ_v (1 + |v|)^{-2}`. -/
noncomputable def freqWeightOne : ℝ := ∑' v : Fin 1 → ℤ, ((1 + frequencyLength v) ^ 2)⁻¹

theorem summable_freqWeightOne :
    Summable (fun v : Fin 1 → ℤ => ((1 + frequencyLength v) ^ 2)⁻¹) := by
  have h := summable_norm_of_frequency_decay (d := 1) (m := 2) (A := (2 * Real.pi) ^ 2)
    (by positivity) (by norm_num)
    (fun v => ((((1 + frequencyLength v) ^ 2)⁻¹ : ℝ) : ℂ)) (fun v hv => by
      have h1 := one_le_frequencyLength hv
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have e : (2 * Real.pi) ^ 2 * (Real.sqrt ((1 : ℕ) : ℝ) /
          (2 * Real.pi * frequencyLength v)) ^ 2 = (frequencyLength v ^ 2)⁻¹ := by
        rw [Nat.cast_one, Real.sqrt_one]; field_simp
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2))
  refine h.congr fun v => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (by have := frequencyLength_nonneg v; positivity)]

theorem freqWeightOne_nonneg : 0 ≤ freqWeightOne :=
  tsum_nonneg fun v => by have := frequencyLength_nonneg v; positivity

/-- The constant of the one-dimensional bump expansion. -/
noncomputable def bumpFourierConst : ℝ := 8192 * freqWeightOne

/-- A smooth bump on `[-2, 2]` is, on `[-4, 4]`, the absolutely convergent sum of the linear
phases `e(v u / 8)`, with `Σ_v |q_v| (1 + |v|) ≤ C (sup |φ| + sup |φ'''|)`. -/
theorem bump_fourier_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ 2) {A0 A3 : ℝ} (hA0 : ∀ u, ‖φ u‖ ≤ A0)
    (hA3 : ∀ u, ‖iteratedDeriv 3 φ u‖ ≤ A3) :
    ∃ q : (Fin 1 → ℤ) → ℂ,
      (∀ u, |u| ≤ 4 → HasSum (fun v => q v * (Real.fourierChar ((v 0 : ℝ) * (u / 8)) : ℂ))
        (φ u)) ∧
      Summable (fun v => ‖q v‖ * (1 + frequencyLength v)) ∧
      (∑' v, ‖q v‖ * (1 + frequencyLength v)) ≤ bumpFourierConst * (A0 + A3) := by
  have hA00 : 0 ≤ A0 := (norm_nonneg _).trans (hA0 0)
  have hA30 : 0 ≤ A3 := (norm_nonneg _).trans (hA3 0)
  set F : (Fin 1 → ℝ) → ℂ := fun w => φ (w 0) with hF
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F :=
    hφ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
  have hFsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ 2 := by
    intro w hw l
    have hl : l = 0 := Subsingleton.elim _ _
    rw [hl]; exact hsupp _ hw
  set f := cubePeriodization F 8 with hf
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
    cubePeriodization_smooth hFs (by norm_num) (by norm_num) hFsupp
  have hslice : ∀ (i : Fin (0 + 1)) (x : Fin 0 → ℝ),
      (fun s => F (i.insertNth s x)) = φ := by
    intro i x
    funext s
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    simp [hF]
  have hline := cubePeriodization_line_le (d := 0) hFs (R := 2) (L := 8) (by norm_num)
    (by norm_num) hFsupp 3 (A := A3) (fun i x t => by rw [hslice]; exact hA3 t)
  have hB : ∀ y, ‖f y‖ ≤ 4 ^ 1 * ((8 : ℝ) ^ 0 * A0) := by
    intro y
    have h := cubePeriodization_iteratedFDeriv_le hFs (R := 2) (L := 8) (by norm_num)
      (by norm_num) hFsupp 0 (A := A0) (fun w => by
        rw [norm_iteratedFDeriv_zero]; exact hA0 _) y
    rwa [norm_iteratedFDeriv_zero] at h
  obtain ⟨hsum, -, hdec, hcB⟩ := periodic_fourier_expansion (d := 0) (m := 3) (by norm_num) f
    hfs.continuous (cubePeriodization_periodic F 8)
    (fun i x => (hfs.comp (contDiff_insertNth_line i x)).of_le (by simp))
    hline hB
  set q := periodicFourierCoeff f with hq
  set A' := (4 : ℝ) ^ (0 + 1) * ((8 : ℝ) ^ 3 * A3) with hA'
  set B' := (4 : ℝ) ^ 1 * ((8 : ℝ) ^ 0 * A0) with hB'
  -- the weighted coefficient bound
  have hpt : ∀ v, ‖q v‖ * (1 + frequencyLength v) ≤
      (4 * (B' + A')) * ((1 + frequencyLength v) ^ 2)⁻¹ := by
    intro v
    have hL0 := frequencyLength_nonneg v
    by_cases hv : v = 0
    · subst hv
      have h0 : frequencyLength (0 : Fin 1 → ℤ) = 0 := by simp [frequencyLength]
      rw [h0]
      have h0' := hcB 0
      have hA'0 : 0 ≤ A' := by positivity
      have hB'0 : 0 ≤ B' := by positivity
      rw [add_zero, mul_one, one_pow, inv_one, mul_one]
      linarith
    · have h1 := one_le_frequencyLength hv
      have hd := hdec v hv
      rw [Nat.cast_zero, zero_add, Real.sqrt_one] at hd
      have hpi := Real.pi_gt_three
      set x := frequencyLength v with hx
      have hA'0 : 0 ≤ A' := by positivity
      have hB'0 : 0 ≤ B' := by positivity
      -- `A' (1/(2π x))³ (1 + x) ≤ 4 A' (1 + x)^{-2}`
      have key : A' * (1 / (2 * Real.pi * x)) ^ 3 * (1 + x) ≤ 4 * A' * ((1 + x) ^ 2)⁻¹ := by
        have hx0 : 0 < x := by linarith
        have h3 : (1 + x) ^ 3 ≤ 8 * x ^ 3 := by
          have : 1 + x ≤ 2 * x := by linarith
          calc (1 + x) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
            _ = 8 * x ^ 3 := by ring
        have h4 : (1 + x) ^ 3 ≤ 4 * ((2 * Real.pi) ^ 3 * x ^ 3) := by
          have h6 : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          have : (2 : ℝ) ≤ (2 * Real.pi) ^ 3 :=
            h6.trans (le_self_pow₀ (by linarith) (by norm_num))
          nlinarith [pow_pos hx0 3]
        have h5 : (1 / (2 * Real.pi * x)) ^ 3 * (1 + x) ≤ 4 * ((1 + x) ^ 2)⁻¹ := by
          have e1 : (1 / (2 * Real.pi * x)) ^ 3 * (1 + x) =
              (1 + x) / ((2 * Real.pi) ^ 3 * x ^ 3) := by field_simp
          have e2 : 4 * ((1 + x) ^ 2)⁻¹ = 4 / (1 + x) ^ 2 := by ring
          rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
          have e3 : (1 + x) * (1 + x) ^ 2 = (1 + x) ^ 3 := by ring
          rw [e3]; linarith
        calc A' * (1 / (2 * Real.pi * x)) ^ 3 * (1 + x)
            = A' * ((1 / (2 * Real.pi * x)) ^ 3 * (1 + x)) := by ring
          _ ≤ A' * (4 * ((1 + x) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h5 hA'0
          _ = 4 * A' * ((1 + x) ^ 2)⁻¹ := by ring
      calc ‖q v‖ * (1 + x) ≤ A' * (1 / (2 * Real.pi * x)) ^ 3 * (1 + x) :=
            mul_le_mul_of_nonneg_right hd (by linarith)
        _ ≤ 4 * A' * ((1 + x) ^ 2)⁻¹ := key
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hsw : Summable (fun v => ‖q v‖ * (1 + frequencyLength v)) :=
    Summable.of_nonneg_of_le (fun v => by have := frequencyLength_nonneg v; positivity) hpt
      (summable_freqWeightOne.mul_left _)
  refine ⟨q, fun u hu => ?_, hsw, ?_⟩
  · have he := cubePeriodization_eq F (R := 2) (L := 8) (by norm_num) (by norm_num)
      (by norm_num) hFsupp (fun _ => u) (fun _ => by linarith)
    have he' : f (fun _ => u / 8) = φ u := he
    have h := hsum (fun _ => u / 8)
    rw [he'] at h
    simpa [Fin.sum_univ_one, hF] using h
  · calc _ ≤ ∑' v, (4 * (B' + A')) * ((1 + frequencyLength v) ^ 2)⁻¹ :=
          Summable.tsum_le_tsum hpt hsw (summable_freqWeightOne.mul_left _)
      _ = 4 * (B' + A') * freqWeightOne := by rw [tsum_mul_left, freqWeightOne]
      _ ≤ bumpFourierConst * (A0 + A3) := by
          rw [bumpFourierConst, hA', hB']
          have := freqWeightOne_nonneg
          norm_num
          nlinarith

/-- Blueprint lem:delay, line 1562 (smooth expansion of `e(λ_* t²) - 1`): on `|u| ≤ 1`,
`e(D u²) - 1` is an absolutely convergent sum of linear phases `e(v u / 8)` whose weighted
coefficient norm is at most `C |D| (1 + |D|)³`. -/
theorem chirp_fourier : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, ∃ q : (Fin 1 → ℤ) → ℂ,
    (∀ u, |u| ≤ 1 → HasSum (fun v => q v * (Real.fourierChar ((v 0 : ℝ) * (u / 8)) : ℂ))
      ((Real.fourierChar (D * u ^ 2) : ℂ) - 1)) ∧
    Summable (fun v => ‖q v‖ * (1 + frequencyLength v)) ∧
    (∑' v, ‖q v‖ * (1 + frequencyLength v)) ≤ C * |D| * (1 + |D|) ^ 3 := by
  obtain ⟨χ, Kχ, hK1, hχs, hχb, hχ1, hχ0, hχd⟩ := exists_plateau_cutoff
  set Cχ : ℝ := ((Kχ : ℝ) * 4) ^ (Kχ * 4) with hCχ
  have hK1' : (1 : ℝ) ≤ Kχ := by exact_mod_cast hK1
  have hCχb : ∀ i ≤ 3, ∀ x, |iteratedDeriv i χ x| ≤ Cχ := by
    intro i hi x
    refine (hχd i x).trans ?_
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hb : (1 : ℝ) ≤ (Kχ : ℝ) * ((i : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le hK1' (by linarith)
    calc ((Kχ : ℝ) * ((i : ℝ) + 1)) ^ (Kχ * (i + 1))
        ≤ ((Kχ : ℝ) * 4) ^ (Kχ * (i + 1)) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have : (i : ℝ) ≤ 3 := by exact_mod_cast hi
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ((Kχ : ℝ) * 4) ^ (Kχ * 4) :=
          pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left _ (by omega))
  have hCχ0 : 0 ≤ Cχ := by positivity
  set C := bumpFourierConst * (120 * Cχ) * (1 + 600 ^ 3) with hC
  have hbf0 : 0 ≤ bumpFourierConst := by
    unfold bumpFourierConst; have := freqWeightOne_nonneg; positivity
  refine ⟨C, by positivity, fun D => ?_⟩
  set φ := chirpBump χ D with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ :=
    ((contDiff_fourierChar_comp (contDiff_const.mul (contDiff_id.mul contDiff_id))).sub
      contDiff_const).mul (Complex.ofRealCLM.contDiff.comp hχs)
  have hφ0 : ∀ u, 2 ≤ |u| → φ u = 0 := fun u hu => by
    simp only [hφ, chirpBump, hχ0 u hu, Complex.ofReal_zero, mul_zero]
  have hsupp : ∀ u, φ u ≠ 0 → |u| ≤ 2 := fun u hu => by
    by_contra h; exact hu (hφ0 u (le_of_lt (not_le.mp h)))
  -- uniform derivative bounds
  set R := (1 + ((0 + (0 + 1)) + (3 + 1) * (2 * Real.pi) * (max (|D| * (3 * 3)) 1 *
      (0 + (1 + 1))))) + 1 with hR
  set K := (18 * Real.pi * |D| + 2 * Real.pi * (2 * |D| * 3) * 1) * Cχ with hK
  have hpi4 : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
  have hpi0 := Real.pi_pos
  have hR0 : 0 ≤ R := by positivity
  have hRle : R ≤ 600 * (1 + |D|) := by
    have hm : max (|D| * (3 * 3)) 1 ≤ 9 * |D| + 1 :=
      max_le (by linarith [abs_nonneg D]) (by linarith [abs_nonneg D])
    have hm0 : 0 ≤ max (|D| * (3 * 3)) 1 := le_max_of_le_right zero_le_one
    rw [hR]
    nlinarith [abs_nonneg D]
  have hKle : K ≤ 120 * Cχ * |D| := by
    rw [hK]
    calc (18 * Real.pi * |D| + 2 * Real.pi * (2 * |D| * 3) * 1) * Cχ
        = (30 * Real.pi) * (|D| * Cχ) := by ring
      _ ≤ 120 * (|D| * Cχ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 120 * Cχ * |D| := by ring
  have hder : ∀ i ≤ 3, ∀ u, ‖iteratedDeriv i φ u‖ ≤ K * R ^ i := by
    intro i hi u
    by_cases hu : |u| ≤ 3
    · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact chirpBump_geomBound hχs hCχb D hu i hi
    · have hev : φ =ᶠ[nhds u] fun _ => (0 : ℂ) := by
        have hopen : IsOpen {x : ℝ | 2 < |x|} := isOpen_lt continuous_const continuous_abs
        filter_upwards [hopen.mem_nhds (show 2 < |u| by linarith)] with x hx
        exact hφ0 x (le_of_lt hx)
      rw [hev.iteratedDeriv_eq]
      have hK0 : 0 ≤ K := by rw [hK]; positivity
      rw [show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl, iteratedDeriv_const_zero, norm_zero]
      positivity
  have hA0 : ∀ u, ‖φ u‖ ≤ 120 * Cχ * |D| := fun u => by
    have h := hder 0 (by norm_num) u
    rw [iteratedDeriv_zero, pow_zero, mul_one] at h
    exact h.trans hKle
  have hA3 : ∀ u, ‖iteratedDeriv 3 φ u‖ ≤ 120 * Cχ * |D| * (600 * (1 + |D|)) ^ 3 := by
    intro u
    refine (hder 3 le_rfl u).trans ?_
    exact mul_le_mul hKle (pow_le_pow_left₀ hR0 hRle 3) (by positivity) (by positivity)
  obtain ⟨q, hq, hqs, hqb⟩ := bump_fourier_one hφs hsupp hA0 hA3
  refine ⟨q, fun u hu => ?_, hqs, hqb.trans ?_⟩
  · have h := hq u (by linarith)
    have e : φ u = (Real.fourierChar (D * u ^ 2) : ℂ) - 1 := by
      simp only [hφ, chirpBump, hχ1 u hu, Complex.ofReal_one, mul_one, sq]
    rwa [e] at h
  · have h1 : (1 : ℝ) ≤ (1 + |D|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg D])
    have e : bumpFourierConst * (120 * Cχ * |D| + 120 * Cχ * |D| * (600 * (1 + |D|)) ^ 3) =
        bumpFourierConst * (120 * Cχ) * |D| * (1 + 600 ^ 3 * (1 + |D|) ^ 3) := by ring
    rw [e, hC]
    have hX : 0 ≤ bumpFourierConst * (120 * Cχ) * |D| := by positivity
    calc bumpFourierConst * (120 * Cχ) * |D| * (1 + 600 ^ 3 * (1 + |D|) ^ 3)
        ≤ bumpFourierConst * (120 * Cχ) * |D| * ((1 + 600 ^ 3) * (1 + |D|) ^ 3) :=
          mul_le_mul_of_nonneg_left (by nlinarith only [h1]) hX
      _ = _ := by ring

/-- The constant of `chirp_fourier`. -/
noncomputable def chirpConst : ℝ := Classical.choose chirp_fourier

theorem chirpConst_spec : 0 ≤ chirpConst ∧ ∀ D : ℝ, ∃ q : (Fin 1 → ℤ) → ℂ,
    (∀ u, |u| ≤ 1 → HasSum (fun v => q v * (Real.fourierChar ((v 0 : ℝ) * (u / 8)) : ℂ))
      ((Real.fourierChar (D * u ^ 2) : ℂ) - 1)) ∧
    Summable (fun v => ‖q v‖ * (1 + frequencyLength v)) ∧
    (∑' v, ‖q v‖ * (1 + frequencyLength v)) ≤ chirpConst * |D| * (1 + |D|) ^ 3 :=
  Classical.choose_spec chirp_fourier

/-- Blueprint lem:delay, proof line 1562 at one depth: the smooth tensor expansion of
`w_I (e(λ_* t²) - 1)` in linear phases costs `C |λ_*| r² (1 + |λ_*| r²)³` times the one-depth
linear-phase bound. -/
theorem delay_chirp_depth (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (S' : Finset (ℤ × ℤ)) (hS' : S' ⊆ S) (s : ℤ)
    (hs : ∀ I ∈ S', I.1 = s) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S', IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) (lam : ℝ) {ψb : ℝ → ℂ} (hψbm : Measurable ψb)
    (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzb : IsAdmissibleOpponent G J Fb zb Kb) (hzbm : ∀ I, Measurable (zb I))
    (hzb2 : ∀ I ∈ S', MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) (K₀ : ℕ)
    (hN : ∀ I ∈ S', I.1 + K₀ ≤ Δ.N) :
    ∑ I ∈ S', dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ) - 1) a b
        (fun y => 1 * Δ.D (I.1 + K₀) y) (fun y => ψb y * zb I y)‖ ≤
      delayLinConst κ * chirpConst * (|lam * dyadicGridLength G s ^ 2| *
        (1 + |lam * dyadicGridLength G s ^ 2|) ^ 3) *
        (Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀) * Real.sqrt Δ.E * Kb *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set r := dyadicGridLength G s with hr
  have hr0 : 0 < r := dyadicGridLength_pos G s
  have hrI : ∀ I ∈ S', dyadicGridLength G I.1 = r := fun I hI => by rw [hs I hI]
  set D := lam * r ^ 2 with hD
  obtain ⟨q, hq, hqs, hqb⟩ := chirpConst_spec.2 D
  have hqn : Summable (fun v => ‖q v‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => le_mul_of_one_le_right (norm_nonneg _)
      (by have := frequencyLength_nonneg v; linarith)) hqs
  set! γ : (Fin 1 → ℤ) → ℝ := fun v => (v 0 : ℝ) / (8 * r) with hγ
  set Y := Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hY
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) with hNb
  set! B := delayLinConst κ * Y * Real.sqrt Δ.E * Kb * Nb with hB
  have hB0 : 0 ≤ B := by have := delayLinConst_nonneg κ; positivity
  -- the linear-phase bound for each frequency
  set! sepv : (Fin 1 → ℤ) → ℤ × ℤ → ℂ := fun v I =>
    separatedLocalForm (dyadicGridLength G I.1) (w I)
      (fun t => (Real.fourierChar (γ v * t) : ℂ)) a b (fun y => 1 * Δ.D (I.1 + K₀) y)
      (fun y => ψb y * zb I y) with hsepv
  have hlin : ∀ v, ∑ I ∈ S', dyadicGridLength G I.1 * ‖sepv v I‖ ≤
      B * (1 + frequencyLength v) := by
    intro v
    have h := delay_linear_depth κ Δ S' hS' s hs w hw hab (γ v) hψbm hψb hKb hzb hzbm
      (fun I hI => by have := cell_isFiniteMeasure G I.1 I.2
                      exact (hzb2 I hI).integrable one_le_two) K₀ hN
    refine h.trans ?_
    have hγv : r * |γ v| ≤ frequencyLength v := by
      rw [hγ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * r)]
      have := abs_frequency_coordinate_le v 0
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith only [abs_nonneg ((v 0 : ℤ) : ℝ), hr0, this]
    rw [hB]
    have hX : 0 ≤ delayLinConst κ * Y * Real.sqrt Δ.E * Kb * Nb := hB0
    calc delayLinConst κ * (1 + r * |γ v|) * Y * Real.sqrt Δ.E * Kb * Nb
        = delayLinConst κ * Y * Real.sqrt Δ.E * Kb * Nb * (1 + r * |γ v|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hX
  -- the expansion at each cell
  have hcell : ∀ I ∈ S', ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
      (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ) - 1) a b
      (fun y => 1 * Δ.D (I.1 + K₀) y) (fun y => ψb y * zb I y)‖ ≤ ∑' v, ‖q v‖ * ‖sepv v I‖ := by
    intro I hI
    have hrI' := hrI I hI
    have hrpos := dyadicGridLength_pos G I.1
    have hFa2 : MemLp (fun y => 1 * Δ.D (I.1 + K₀) y) 2
        (volume.restrict (Set.Ico (dyadicGridLeft G I.1 I.2)
          (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1))) := by
      exact MemLp.const_mul (Δ.D_memLp I (hS' hI) (I.1 + K₀)) 1
    have hFb2 : MemLp (fun y => ψb y * zb I y) 2
        (volume.restrict (Set.Ico (dyadicGridLeft G I.1 I.2)
          (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1))) :=
      memLp_mul_bounded_restrict hψbm hψb (hzb2 I hI)
    have hEc : ∀ c : ℝ, Measurable (fun t : ℝ => (Real.fourierChar (c * t) : ℂ)) := fun c =>
      (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_const.mul continuous_id))).measurable
    have hS := separatedLocalForm_hasSum hrpos (hw I hI) hab q
      (Fa := fun y => 1 * Δ.D (I.1 + K₀) y) (Fb := fun y => ψb y * zb I y)
      (fun v t => (Real.fourierChar (γ v * t) : ℂ)) (fun v => hEc (γ v))
      (fun v t => by rw [Circle.norm_coe]) hqn
      (Q := fun t => (Real.fourierChar (lam * t ^ 2) : ℂ) - 1) (fun t ht => by
        rw [hrI'] at ht
        have hu : |t / r| ≤ 1 := by rw [abs_div, abs_of_pos hr0, div_le_one hr0]; exact ht
        have h := hq (t / r) hu
        have e1 : D * (t / r) ^ 2 = lam * t ^ 2 := by rw [hD]; field_simp
        have e2 : ∀ v : Fin 1 → ℤ, (v 0 : ℝ) * (t / r / 8) = γ v * t := fun v => by
          rw [hγ]; field_simp
        rw [e1] at h
        simpa only [e2] using h)
      (measurable_const.mul (Δ.D_meas _)) (hψbm.mul (hzbm I)) hFa2 hFb2
    rw [← hS.tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun v => norm_mul _ _))
    -- summability of the norms
    obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, ∀ v, ‖sepv v I‖ ≤ Bd := by
      refine ⟨_, fun v => separatedLocalForm_bounded_le hrpos (hw I hI) hab
        (fun t => by rw [Circle.norm_coe]) measurable_const hψbm (fun _ => le_of_eq norm_one)
        hψb (Δ.D_meas _) (hzbm I)
        (Δ.D_memLp I (hS' hI) _) (hzb2 I hI)⟩
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) (hqn.mul_right Bd)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hBd v) (norm_nonneg _)
  -- sum over the cells and the frequencies
  have hsumm : ∀ I ∈ S', Summable (fun v => dyadicGridLength G I.1 * (‖q v‖ * ‖sepv v I‖)) := by
    intro I hI
    refine Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (dyadicGridLength_pos G I.1).le (by positivity)) (fun v => ?_)
      ((hqs.mul_left B))
    have h1 : dyadicGridLength G I.1 * ‖sepv v I‖ ≤ B * (1 + frequencyLength v) :=
      (Finset.single_le_sum (f := fun I => dyadicGridLength G I.1 * ‖sepv v I‖)
        (fun I' _ => mul_nonneg (dyadicGridLength_pos G I'.1).le (norm_nonneg _)) hI).trans
        (hlin v)
    calc dyadicGridLength G I.1 * (‖q v‖ * ‖sepv v I‖)
        = ‖q v‖ * (dyadicGridLength G I.1 * ‖sepv v I‖) := by ring
      _ ≤ ‖q v‖ * (B * (1 + frequencyLength v)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = B * (‖q v‖ * (1 + frequencyLength v)) := by ring
  calc ∑ I ∈ S', dyadicGridLength G I.1 * ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ) - 1) a b
        (fun y => 1 * Δ.D (I.1 + K₀) y) (fun y => ψb y * zb I y)‖
      ≤ ∑ I ∈ S', ∑' v, dyadicGridLength G I.1 * (‖q v‖ * ‖sepv v I‖) := by
        refine Finset.sum_le_sum fun I hI => ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hcell I hI) (dyadicGridLength_pos G I.1).le
    _ = ∑' v, ∑ I ∈ S', dyadicGridLength G I.1 * (‖q v‖ * ‖sepv v I‖) :=
        (Summable.tsum_finsetSum hsumm).symm
    _ ≤ ∑' v, B * (‖q v‖ * (1 + frequencyLength v)) := by
        refine Summable.tsum_le_tsum (fun v => ?_) (summable_sum hsumm) (hqs.mul_left B)
        calc ∑ I ∈ S', dyadicGridLength G I.1 * (‖q v‖ * ‖sepv v I‖)
            = ‖q v‖ * ∑ I ∈ S', dyadicGridLength G I.1 * ‖sepv v I‖ := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun I _ => by ring
          _ ≤ ‖q v‖ * (B * (1 + frequencyLength v)) :=
              mul_le_mul_of_nonneg_left (hlin v) (norm_nonneg _)
          _ = _ := by ring
    _ = B * ∑' v, ‖q v‖ * (1 + frequencyLength v) := tsum_mul_left
    _ ≤ B * (chirpConst * |D| * (1 + |D|) ^ 3) := mul_le_mul_of_nonneg_left hqb hB0
    _ = _ := by rw [hB]; ring

/-- Squared lengths of distinct depths sum to at most twice the largest one. -/
theorem depth_sq_sum_le (G : RealDyadicGrid) (Ds : Finset ℤ) (hne : Ds.Nonempty) :
    ∑ s ∈ Ds, dyadicGridLength G s ^ 2 ≤ 2 * dyadicGridLength G (Ds.min' hne) ^ 2 := by
  set s₀ := Ds.min' hne
  have hle : ∀ s ∈ Ds, s₀ ≤ s := fun s hs => Ds.min'_le s hs
  have hb : ∀ s ∈ Ds, dyadicGridLength G s ^ 2 ≤
      dyadicGridLength G s₀ ^ 2 * (2 : ℝ)⁻¹ ^ (s - s₀).toNat := by
    intro s hs
    have e : s = s₀ + ((s - s₀).toNat : ℕ) := by have := hle s hs; omega
    rw [e, dyadicGridLength_add_nat, mul_pow, ← e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc ∑ s ∈ Ds, dyadicGridLength G s ^ 2
      ≤ ∑ s ∈ Ds, dyadicGridLength G s₀ ^ 2 * (2 : ℝ)⁻¹ ^ (s - s₀).toNat :=
        Finset.sum_le_sum hb
    _ = dyadicGridLength G s₀ ^ 2 * ∑ s ∈ Ds, (2 : ℝ)⁻¹ ^ (s - s₀).toNat := by
        rw [Finset.mul_sum]
    _ ≤ dyadicGridLength G s₀ ^ 2 * 2 := mul_le_mul_of_nonneg_left
        (sum_geom_inj_le Ds _ (fun x hx y hy h => by
          have := hle x hx; have := hle y hy; omega)) (by positivity)
    _ = _ := by ring

/-- The constant of the delayed replacement. -/
noncomputable def delayConst (κ : LocalKernelClass) : ℝ :=
  9 * delayZeroConst κ + 18 * delayLinConst κ * chirpConst

theorem delayConst_nonneg (κ : LocalKernelClass) : 0 ≤ delayConst κ := by
  unfold delayConst
  have := delayZeroConst_nonneg κ
  have := delayLinConst_nonneg κ
  have := chirpConst_spec.1
  positivity

/-- Blueprint lem:delay, `eq:delay-error`: replacing the position-`a` input at each use cell
of depth `s` by its projection at depth `s + K₀` changes the length-weighted scale sum of a
fixed predictor term `w_I(x,t) e(λ_* t²)` (with `|λ_*| |I|² ≤ D_pred`) against an admissible
opponent by at most `C (2^{-K₀} + (1 + K₀) √ε) (1 + D_pred)⁴ ‖F_a‖ ‖F_b‖`; here the delayed
residual `D_{s+K₀}` carries the multiplier `ψ_a`, `E = ‖1_J F_a‖²` bounds the projection
energies and `K_b` is the opponent's transfer constant. -/
theorem delay_error_bound (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ}
    {S : Finset (ℤ × ℤ)} (Δ : DelayData G J S) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) (lam : ℝ) {Dp : ℝ} (hDp0 : 0 ≤ Dp)
    (hDp : ∀ I ∈ S, |lam| * dyadicGridLength G I.1 ^ 2 ≤ Dp)
    {ψb : ℝ → ℂ} (hψbm : Measurable ψb) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzb : IsAdmissibleOpponent G J Fb zb Kb) (hzbm : ∀ I, Measurable (zb I))
    (hzb2 : ∀ I ∈ S, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) (K₀ : ℕ)
    (hN : ∀ I ∈ S, I.1 + K₀ ≤ Δ.N) :
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b (Δ.D (I.1 + K₀))
        (fun y => ψb y * zb I y)‖ ≤
      delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt Δ.ε) * (1 + Dp) ^ 4 *
        Real.sqrt Δ.E * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) with hNb
  have hNb0 : 0 ≤ Nb := Real.sqrt_nonneg _
  have hE0 := Δ.E_nonneg
  set! X := (K₀ : ℝ) * Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hX
  set! Y := Real.sqrt Δ.ε + 9 * (2 : ℝ)⁻¹ ^ K₀ with hY
  set Z := (2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt Δ.ε with hZ
  have hs0 := Real.sqrt_nonneg Δ.ε
  have hp0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ K₀ := by positivity
  have hK0 : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
  have hXZ : X ≤ 9 * Z := by rw [hX, hZ]; nlinarith
  have hYZ : Y ≤ 9 * Z := by rw [hY, hZ]; nlinarith
  -- split the time factor
  set! sep1 : ℤ × ℤ → ℂ := fun I => separatedLocalForm (dyadicGridLength G I.1) (w I)
    (fun t => (Real.fourierChar (0 * t) : ℂ)) a b (fun y => 1 * Δ.D (I.1 + K₀) y)
    (fun y => ψb y * zb I y) with hsep1
  set! sep2 : ℤ × ℤ → ℂ := fun I => separatedLocalForm (dyadicGridLength G I.1) (w I)
    (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ) - 1) a b (fun y => 1 * Δ.D (I.1 + K₀) y)
    (fun y => ψb y * zb I y) with hsep2
  have hEc : ∀ c : ℝ, Measurable (fun t : ℝ => (Real.fourierChar (c * t) : ℂ)) := fun c =>
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul continuous_id))).measurable
  have hEq : Measurable (fun t : ℝ => (Real.fourierChar (lam * t ^ 2) : ℂ)) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul (continuous_pow 2)))).measurable
  have hsplit : ∀ I ∈ S, separatedLocalForm (dyadicGridLength G I.1) (w I)
      (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b (Δ.D (I.1 + K₀))
      (fun y => ψb y * zb I y) = sep1 I + sep2 I := by
    intro I hI
    have hr := dyadicGridLength_pos G I.1
    have hQ : (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) = fun t =>
        (Real.fourierChar (0 * t) : ℂ) + ((Real.fourierChar (lam * t ^ 2) : ℂ) - 1) := by
      funext t; simp
    have hF : Δ.D (I.1 + K₀) = fun y => 1 * Δ.D (I.1 + K₀) y := by funext y; ring
    rw [hQ, hF]
    exact separatedLocalForm_add hr (hw I hI) hab (hEc 0) (hEq.sub measurable_const)
      (C := 2) (fun t => by rw [Circle.norm_coe]; norm_num)
      (fun t => (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num))
      (measurable_const.mul (Δ.D_meas _)) (hψbm.mul (hzbm I))
      (MemLp.const_mul (Δ.D_memLp I hI _) 1) (memLp_mul_bounded_restrict hψbm hψb (hzb2 I hI))
  have hzbi : ∀ I ∈ S, IntegrableOn (zb I) (dyadicGridCell G I.1 I.2) := fun I hI => by
    have := cell_isFiniteMeasure G I.1 I.2
    exact (hzb2 I hI).integrable one_le_two
  -- the first part
  have h1 : ∑ I ∈ S, dyadicGridLength G I.1 * ‖sep1 I‖ ≤
      delayZeroConst κ * X * Real.sqrt Δ.E * Kb * Nb :=
    delay_part_zero κ Δ w hw hab hψbm hψb hKb hzb hzbm hzbi K₀ hN
  -- the second part, depth by depth
  have h2 : ∑ I ∈ S, dyadicGridLength G I.1 * ‖sep2 I‖ ≤
      delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * Real.sqrt Δ.E * Kb * Nb := by
    rcases S.eq_empty_or_nonempty with he | hne
    · rw [Finset.sum_eq_zero (fun I hI => by simp [he] at hI)]
      have := delayLinConst_nonneg κ; have := chirpConst_spec.1
      positivity
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image Prod.fst)
      (g := fun I : ℤ × ℤ => I.1) (fun I hI => Finset.mem_image_of_mem _ hI)]
    have hdep : ∀ s ∈ S.image Prod.fst, ∑ I ∈ S with I.1 = s,
        dyadicGridLength G I.1 * ‖sep2 I‖ ≤
        delayLinConst κ * chirpConst * (|lam| * dyadicGridLength G s ^ 2 * (1 + Dp) ^ 3) *
          Y * Real.sqrt Δ.E * Kb * Nb := by
      intro s hs
      obtain ⟨I₀, hI₀, rfl⟩ := Finset.mem_image.mp hs
      have h := delay_chirp_depth κ Δ (S.filter (fun I => I.1 = I₀.1)) (Finset.filter_subset _ _)
        I₀.1 (fun I hI => (Finset.mem_filter.mp hI).2) w
        (fun I hI => hw I (Finset.mem_filter.mp hI).1) hab lam hψbm hψb hKb hzb hzbm
        (fun I hI => hzb2 I (Finset.mem_filter.mp hI).1) K₀
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
      refine h.trans ?_
      have hD := hDp I₀ hI₀
      have habs : |lam * dyadicGridLength G I₀.1 ^ 2| = |lam| * dyadicGridLength G I₀.1 ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ dyadicGridLength G I₀.1 ^ 2)]
      rw [habs]
      have hpow : (1 + |lam| * dyadicGridLength G I₀.1 ^ 2) ^ 3 ≤ (1 + Dp) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      have hc0 : 0 ≤ delayLinConst κ * chirpConst := by
        have := delayLinConst_nonneg κ; have := chirpConst_spec.1; positivity
      have hrest : 0 ≤ Y * Real.sqrt Δ.E * Kb * Nb := by positivity
      have hmid : |lam| * dyadicGridLength G I₀.1 ^ 2 *
          (1 + |lam| * dyadicGridLength G I₀.1 ^ 2) ^ 3 ≤
          |lam| * dyadicGridLength G I₀.1 ^ 2 * (1 + Dp) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      calc delayLinConst κ * chirpConst * (|lam| * dyadicGridLength G I₀.1 ^ 2 *
            (1 + |lam| * dyadicGridLength G I₀.1 ^ 2) ^ 3) * Y * Real.sqrt Δ.E * Kb * Nb
          = delayLinConst κ * chirpConst * (|lam| * dyadicGridLength G I₀.1 ^ 2 *
            (1 + |lam| * dyadicGridLength G I₀.1 ^ 2) ^ 3) * (Y * Real.sqrt Δ.E * Kb * Nb) := by
            ring
        _ ≤ delayLinConst κ * chirpConst * (|lam| * dyadicGridLength G I₀.1 ^ 2 * (1 + Dp) ^ 3) *
            (Y * Real.sqrt Δ.E * Kb * Nb) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid hc0) hrest
        _ = _ := by ring
    refine (Finset.sum_le_sum hdep).trans ?_
    have hgeo := depth_sq_sum_le G (S.image Prod.fst) (hne.image _)
    obtain ⟨I₀, hI₀, hmin⟩ := Finset.mem_image.mp
      ((S.image Prod.fst).min'_mem (hne.image _))
    have hmax : |lam| * dyadicGridLength G ((S.image Prod.fst).min' (hne.image _)) ^ 2 ≤ Dp := by
      rw [← hmin]; exact hDp I₀ hI₀
    have hsumD : ∑ s ∈ S.image Prod.fst, |lam| * dyadicGridLength G s ^ 2 ≤ 2 * Dp := by
      rw [← Finset.mul_sum]
      calc |lam| * ∑ s ∈ S.image Prod.fst, dyadicGridLength G s ^ 2
          ≤ |lam| * (2 * dyadicGridLength G ((S.image Prod.fst).min' (hne.image _)) ^ 2) :=
            mul_le_mul_of_nonneg_left hgeo (abs_nonneg _)
        _ ≤ 2 * Dp := by linarith
    have hc0 : 0 ≤ delayLinConst κ * chirpConst := by
      have := delayLinConst_nonneg κ; have := chirpConst_spec.1; positivity
    have hrest : 0 ≤ (1 + Dp) ^ 3 * (Y * Real.sqrt Δ.E * Kb * Nb) := by positivity
    calc ∑ s ∈ S.image Prod.fst, delayLinConst κ * chirpConst *
          (|lam| * dyadicGridLength G s ^ 2 * (1 + Dp) ^ 3) * Y * Real.sqrt Δ.E * Kb * Nb
        = delayLinConst κ * chirpConst * ((∑ s ∈ S.image Prod.fst,
            |lam| * dyadicGridLength G s ^ 2) * ((1 + Dp) ^ 3 * (Y * Real.sqrt Δ.E * Kb * Nb))) :=
                by
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ ≤ delayLinConst κ * chirpConst * ((2 * Dp) *
            ((1 + Dp) ^ 3 * (Y * Real.sqrt Δ.E * Kb * Nb))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumD hrest) hc0
      _ = _ := by ring
  -- combine
  have hsum : ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
        (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b (Δ.D (I.1 + K₀))
        (fun y => ψb y * zb I y)‖ ≤
      ∑ I ∈ S, dyadicGridLength G I.1 * ‖sep1 I‖ + ∑ I ∈ S, dyadicGridLength G I.1 * ‖sep2 I‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun I hI => ?_
    rw [hsplit I hI, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (dyadicGridLength_pos G I.1).le
  refine hsum.trans ((add_le_add h1 h2).trans ?_)
  have hZ0 : 0 ≤ Z := by positivity
  have hD1 : 1 ≤ (1 + Dp) ^ 4 := one_le_pow₀ (by linarith)
  have hD2 : 2 * Dp * (1 + Dp) ^ 3 ≤ 2 * (1 + Dp) ^ 4 := by
    have : Dp * (1 + Dp) ^ 3 ≤ (1 + Dp) * (1 + Dp) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith only [hDp0, hD1]
  have hc1 := delayZeroConst_nonneg κ
  have hc2 : 0 ≤ delayLinConst κ * chirpConst := by
    have := delayLinConst_nonneg κ; have := chirpConst_spec.1; positivity
  set! W := Real.sqrt Δ.E * Kb * Nb with hW
  have hW0 : 0 ≤ W := by positivity
  have e1 : delayZeroConst κ * X * Real.sqrt Δ.E * Kb * Nb = delayZeroConst κ * X * W := by
    rw [hW]; ring
  have e2 : delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * Real.sqrt Δ.E * Kb * Nb
      = delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * W := by rw [hW]; ring
  rw [e1, e2]
  have b1 : delayZeroConst κ * X * W ≤ delayZeroConst κ * (9 * Z) * ((1 + Dp) ^ 4 * W) := by
    have h := mul_le_mul hXZ (le_mul_of_one_le_left hW0 hD1) hW0 (by positivity)
    have h' := mul_le_mul_of_nonneg_left h hc1
    calc delayZeroConst κ * X * W = delayZeroConst κ * (X * W) := by ring
      _ ≤ delayZeroConst κ * (9 * Z * ((1 + Dp) ^ 4 * W)) := h'
      _ = _ := by ring
  have b2 : delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * W ≤
      delayLinConst κ * chirpConst * (2 * (1 + Dp) ^ 4) * (9 * Z) * W := by
    have h3 := mul_le_mul hD2 hYZ (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hc2
    have h5 := mul_le_mul_of_nonneg_right h4 hW0
    calc delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * W
        = delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3 * Y) * W := by ring
      _ ≤ delayLinConst κ * chirpConst * (2 * (1 + Dp) ^ 4 * (9 * Z)) * W := h5
      _ = _ := by ring
  calc delayZeroConst κ * X * W + delayLinConst κ * chirpConst * (2 * Dp * (1 + Dp) ^ 3) * Y * W
      ≤ delayZeroConst κ * (9 * Z) * ((1 + Dp) ^ 4 * W) +
        delayLinConst κ * chirpConst * (2 * (1 + Dp) ^ 4) * (9 * Z) * W := add_le_add b1 b2
    _ = delayConst κ * Z * (1 + Dp) ^ 4 * W := by rw [delayConst]; ring
    _ = _ := by rw [hW, hZ]; ring

/-! ### The position-`a` projection family -/

/-- A column tree that is complete down to depth `N` below its root, with a fixed inherited
mask: the nested depth projections `P_h` of blueprint lem:delay (line 1549), on the direct-sum
partitions of the root into its depth-`h` cells. -/
structure ColumnDepthFamily (V : Type*) [Fintype V] where
  /-- Column-tree data used by the depth-indexed family. -/
  D : ColumnTreeData V
  /-- Inherited column mask on the depth-indexed tree. -/
  A : InheritedColumnMask D
  /-- Last depth represented by the column family. -/
  N : ℤ
  root_le : D.root.1 ≤ N
  complete : ∀ c : ℤ × ℤ, dyadicGridCell D.grid c.1 c.2 ⊆
    dyadicGridCell D.grid D.root.1 D.root.2 → c.1 ≤ N → c ∈ D.cells

variable {V : Type*} [Fintype V]

/-- The depth used at level `h`: `h` clamped to `[root, N]`. -/
def ColumnDepthFamily.depth (Ψ : ColumnDepthFamily V) (h : ℤ) : ℤ :=
  max Ψ.D.root.1 (min h Ψ.N)

theorem ColumnDepthFamily.root_le_depth (Ψ : ColumnDepthFamily V) (h : ℤ) :
    Ψ.D.root.1 ≤ Ψ.depth h := le_max_left _ _

theorem ColumnDepthFamily.depth_le (Ψ : ColumnDepthFamily V) (h : ℤ) : Ψ.depth h ≤ Ψ.N :=
  max_le Ψ.root_le (min_le_right _ _)

theorem ColumnDepthFamily.depth_eq (Ψ : ColumnDepthFamily V) {h : ℤ}
    (h1 : Ψ.D.root.1 ≤ h) (h2 : h ≤ Ψ.N) : Ψ.depth h = h := by
  unfold ColumnDepthFamily.depth; rw [min_eq_left h2, max_eq_right h1]

theorem ColumnDepthFamily.depth_mono (Ψ : ColumnDepthFamily V) {h h' : ℤ} (hh : h ≤ h') :
    Ψ.depth h ≤ Ψ.depth h' :=
  max_le_max le_rfl (min_le_min hh le_rfl)

/-- The partition of the root into its cells of depth `depth h`. -/
noncomputable def ColumnDepthFamily.partition (Ψ : ColumnDepthFamily V) (h : ℤ) :
    ColumnStoppingPartition Ψ.D where
  cells := dyadicGeneration Ψ.D.grid Ψ.D.root (Ψ.depth h - Ψ.D.root.1).toNat
  subset := fun c hc => Ψ.complete c (dyadicGeneration_subset _ _ _ hc) (by
    have := dyadicGeneration_depth _ _ _ hc
    have := Ψ.depth_le h; have := Ψ.root_le_depth h; omega)
  disjoint := dyadicGeneration_pairwiseDisjoint _ _ _
  cover := dyadicGeneration_union _ _ _

theorem ColumnDepthFamily.mem_partition (Ψ : ColumnDepthFamily V) (h : ℤ) (c : ℤ × ℤ) :
    c ∈ (Ψ.partition h).cells ↔ c.1 = Ψ.depth h ∧
      dyadicGridCell Ψ.D.grid c.1 c.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 := by
  change c ∈ dyadicGeneration _ _ _ ↔ _
  rw [dyadicGeneration_mem_iff]
  have := Ψ.root_le_depth h
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-- The depth projection `P_h`. -/
noncomputable def ColumnDepthFamily.proj (Ψ : ColumnDepthFamily V) (h : ℤ) :
    ColumnL2 V →L[ℂ] ColumnL2 V :=
  partitionColumnProjection Ψ.D Ψ.A (Ψ.partition h)

theorem ColumnDepthFamily.isStarProjection_proj (Ψ : ColumnDepthFamily V) (h : ℤ) :
    IsStarProjection (Ψ.proj h) := isStarProjection_starProjection

/-- Cells below the root of depth at least the root's are contained in the root's cell along
with their ancestors. -/
theorem ancestor_below_root (G : RealDyadicGrid) (J c : ℤ × ℤ)
    (hc : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G J.1 J.2) {k : ℤ} (hJk : J.1 ≤ k)
    (hkc : k ≤ c.1) :
    ∃ m : ℤ, dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G k m ∧
      dyadicGridCell G k m ⊆ dyadicGridCell G J.1 J.2 := by
  obtain ⟨m, hm⟩ := dyadicGridCell_ancestor G hkc c.2
  refine ⟨m, hm, ?_⟩
  rcases dyadicGridCell_nested_or_disjoint_of_le G hJk J.2 m with hd | hs
  · exfalso
    have hy := dyadicGridCell_left_mem G c.1 c.2
    exact Set.disjoint_left.mp hd (hc hy) (hm hy)
  · exact hs

/-- The depth projections are nested. -/
theorem ColumnDepthFamily.proj_nested (Ψ : ColumnDepthFamily V) {h h' : ℤ} (hh : h ≤ h') :
    (Ψ.proj h).comp (Ψ.proj h') = Ψ.proj h := by
  refine partitionColumnProjection_nested Ψ.D Ψ.A (fun c hc => ?_)
  obtain ⟨hc1, hc2⟩ := (Ψ.mem_partition h' c).mp hc
  obtain ⟨m, hm1, hm2⟩ := ancestor_below_root Ψ.D.grid Ψ.D.root c hc2 (Ψ.root_le_depth h)
    (by rw [hc1]; exact Ψ.depth_mono hh)
  exact ⟨(Ψ.depth h, m), (Ψ.mem_partition h _).mpr ⟨rfl, hm2⟩, hm1⟩

/-- On a cell of the depth-`h` partition, `P_h z` agrees a.e. with the cell projection. -/
theorem ColumnDepthFamily.proj_ae_cell (Ψ : ColumnDepthFamily V) (h : ℤ) (z : ColumnL2 V)
    {Q : ℤ × ℤ} (hQ : Q ∈ (Ψ.partition h).cells) :
    (Ψ.proj h z : ℝ → ColumnHilbert V) =ᵐ[volume.restrict
      (dyadicGridCell Ψ.D.grid Q.1 Q.2)] cellColumnProjection Ψ.D Ψ.A
        ((Ψ.partition h).subset hQ) z := by
  classical
  set π := Ψ.partition h
  have hsum := partitionColumnProjection_eq_sum Ψ.D Ψ.A π z
  have h1 := Lp.coeFn_finsetSum (Finset.univ : Finset {c // c ∈ π.cells})
    (fun c => cellColumnProjection Ψ.D Ψ.A (π.subset c.property) z)
  have hoff : ∀ c : {c // c ∈ π.cells}, c.val ≠ Q →
      ∀ᵐ y ∂volume.restrict (dyadicGridCell Ψ.D.grid Q.1 Q.2),
        (cellColumnProjection Ψ.D Ψ.A (π.subset c.property) z : ℝ → ColumnHilbert V) y = 0 := by
    intro c hc
    have h0 := cellColumnRange_ae_zero_off Ψ.D Ψ.A (π.subset c.property)
      (cellColumnProjection_mem Ψ.D Ψ.A (π.subset c.property) z)
    rw [ae_restrict_iff' (dyadicGridCell_measurable _ _ _)]
    filter_upwards [h0] with y hy hyQ
    refine hy fun hyc => ?_
    exact Set.disjoint_left.mp (π.disjoint c.property hQ hc) hyc hyQ
  have hall := (Filter.eventually_all (ι := {c // c ∈ π.cells})).mpr
    (fun c => (Classical.em (c.val = Q)).elim (fun he => Filter.Eventually.of_forall
      (fun _ (hne : c.val ≠ Q) => absurd he hne)) (fun hne =>
      (hoff c hne).mono fun y hy _ => hy))
  have h1' := ae_restrict_of_ae (s := dyadicGridCell Ψ.D.grid Q.1 Q.2) h1
  have : Ψ.proj h z = ∑ c : {c // c ∈ π.cells},
      cellColumnProjection Ψ.D Ψ.A (π.subset c.property) z := hsum
  rw [this]
  filter_upwards [h1', hall] with y hy hall'
  rw [hy, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟨Q, hQ⟩]
  · intro c _ hc
    exact hall' c (fun he => hc (Subtype.ext he))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ColumnDepthFamily.depth_of_mem (Ψ : ColumnDepthFamily V) {h : ℤ}
    (h1 : Ψ.D.root.1 ≤ h) (h2 : h ≤ Ψ.N) {Q : ℤ × ℤ} (hQ1 : Q.1 = h)
    (hQ : dyadicGridCell Ψ.D.grid Q.1 Q.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2) :
    Q ∈ (Ψ.partition h).cells :=
  (Ψ.mem_partition h Q).mpr ⟨by rw [Ψ.depth_eq h1 h2]; exact hQ1, hQ⟩

/-- On a partition cell, `P_h z` is a.e. the constant-coefficient column combination. -/
theorem ColumnDepthFamily.proj_ae_combination (Ψ : ColumnDepthFamily V) (h : ℤ)
    (z : ColumnL2 V) {Q : ℤ × ℤ} (hQ : Q ∈ (Ψ.partition h).cells) :
    ∀ᵐ y ∂volume.restrict (dyadicGridCell Ψ.D.grid Q.1 Q.2),
      (Ψ.proj h z : ℝ → ColumnHilbert V) y = columnCombination Ψ.D Ψ.A Q
        (cellProjectionCoefficients Ψ.D Ψ.A ((Ψ.partition h).subset hQ) z) y := by
  have h1 := Ψ.proj_ae_cell h z hQ
  have h2 := ae_restrict_of_ae (s := dyadicGridCell Ψ.D.grid Q.1 Q.2)
    (cellColumnProjection_coeFn Ψ.D Ψ.A ((Ψ.partition h).subset hQ) z)
  have h3 := ae_restrict_mem (μ := volume) (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [hy1, hy2, Set.indicator_of_mem hy3]

/-- The delayed residual `D_h = (f - (P_h F)_phys) ψ_a` of a physical input. -/
noncomputable def ColumnDepthFamily.resid (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (ψa : ℝ → ℂ) (h : ℤ) (y : ℝ) : ℂ :=
  ((f : ℝ → ℂ) y - (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y none) * ψa y

open scoped Classical in
/-- The predictor moment on a partition cell (`eq:predictor-moment`): if the predictor
`(ψBar_a, √ε e_p)` is available on `Q`, the cell average of the residual is `ε` times the
predictor's coefficient. -/
theorem ColumnDepthFamily.integral_resid (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} {p : V}
    (hscal : ∀ y, Ψ.D.scalar p y = star (ψa y)) (h : ℤ) {Q : ℤ × ℤ}
    (hQ : Q ∈ (Ψ.partition h).cells) (hp : p ∈ Ψ.A.labels Q) :
    (((dyadicGridLength Ψ.D.grid Q.1)⁻¹ : ℝ) : ℂ) *
      ∫ y in dyadicGridCell Ψ.D.grid Q.1 Q.2, Ψ.resid f ψa h y =
      (Ψ.D.privateWeight p : ℂ) * cellProjectionCoefficients Ψ.D Ψ.A
        ((Ψ.partition h).subset hQ) (physicalColumnInput f) ⟨p, hp⟩ := by
  have hm := cellColumnProjection_predictor_moment Ψ.D Ψ.A ((Ψ.partition h).subset hQ) f
    ⟨p, hp⟩
  rw [← hm]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Ψ.proj_ae_cell h (physicalColumnInput f) hQ] with y hy
  simp only [ColumnDepthFamily.resid, hy, hscal, star_star]

open scoped Classical in
/-- The private coordinate of `P_h F` on a partition cell. -/
theorem ColumnDepthFamily.proj_private_ae (Ψ : ColumnDepthFamily V) (h : ℤ) (z : ColumnL2 V)
    {Q : ℤ × ℤ} (hQ : Q ∈ (Ψ.partition h).cells) {p : V} (hp : p ∈ Ψ.A.labels Q) :
    ∀ᵐ y ∂volume.restrict (dyadicGridCell Ψ.D.grid Q.1 Q.2),
      (Ψ.proj h z : ℝ → ColumnHilbert V) y (some p) =
        cellProjectionCoefficients Ψ.D Ψ.A ((Ψ.partition h).subset hQ) z ⟨p, hp⟩ *
          (Real.sqrt (Ψ.D.privateWeight p) : ℂ) := by
  filter_upwards [Ψ.proj_ae_combination h z hQ] with y hy
  rw [hy]
  exact columnCombination_private Ψ.D Ψ.A Q _ y ⟨p, hp⟩

/-- Blueprint lem:delay, line 1550: below a use cell carrying the predictor, the
conditional expectation of the residual at depth `h` is `√ε` times the private coordinate,
`μ_h = E_h D_h = ε a_{h,p}`. -/
theorem ColumnDepthFamily.moment_ae (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} {p : V}
    (hscal : ∀ y, Ψ.D.scalar p y = star (ψa y)) {I : ℤ × ℤ}
    (hI : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
    (havail : ∀ c ∈ Ψ.D.cells, dyadicGridCell Ψ.D.grid c.1 c.2 ⊆
      dyadicGridCell Ψ.D.grid I.1 I.2 → p ∈ Ψ.A.labels c)
    {h : ℤ} (hIh : I.1 ≤ h) (hhN : h ≤ Ψ.N) :
    ∀ᵐ y ∂volume.restrict (dyadicGridCell Ψ.D.grid I.1 I.2),
      depthExpectation Ψ.D.grid h (Ψ.resid f ψa h) y =
        (Real.sqrt (Ψ.D.privateWeight p) : ℂ) *
          (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y (some p) := by
  classical
  have hroot : Ψ.D.root.1 ≤ I.1 := dyadicGridCell_depth_le_of_subset _ _ _ hI
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h = I.1 + n := ⟨(h - I.1).toNat, by omega⟩
  have hU := dyadicGeneration_union Ψ.D.grid I n
  rw [← hU, ae_restrict_biUnion_finset_iff]
  intro Q hQg
  have hQ1 : Q.1 = h := by rw [dyadicGeneration_depth _ _ _ hQg, hn]
  obtain ⟨q1, q2⟩ := Q
  simp only at hQ1
  subst hQ1
  have hQI := dyadicGeneration_subset _ _ _ hQg
  have hQ : (q1, q2) ∈ (Ψ.partition q1).cells :=
    Ψ.depth_of_mem (by omega) hhN rfl (hQI.trans hI)
  have hQc : (q1, q2) ∈ Ψ.D.cells := (Ψ.partition q1).subset hQ
  have hp := havail (q1, q2) hQc hQI
  have hε := Ψ.D.privateWeight_pos p
  have hint := Ψ.integral_resid f hscal q1 hQ hp
  have hmem := ae_restrict_mem (μ := volume) (dyadicGridCell_measurable Ψ.D.grid q1 q2)
  filter_upwards [Ψ.proj_private_ae q1 (physicalColumnInput f) hQ hp, hmem] with y hy hyQ
  rw [hy, depthExpectation_of_mem hyQ, cellAverage]
  simp only at hint
  rw [hint]
  have hs : ((Real.sqrt (Ψ.D.privateWeight p) : ℝ) : ℂ) *
      (Real.sqrt (Ψ.D.privateWeight p) : ℂ) = (Ψ.D.privateWeight p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hε.le]
  rw [← hs]
  ring

theorem physicalColumnInput_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ y ∂volume, ‖(physicalColumnInput (V := V) f : ℝ → ColumnHilbert V) y‖ = ‖(f : ℝ → ℂ) y‖ ∧
      (physicalColumnInput (V := V) f : ℝ → ColumnHilbert V) y none = (f : ℝ → ℂ) y := by
  classical
  filter_upwards [physicalColumnInput_coeFn (V := V) f] with y hy
  rw [hy]
  exact ⟨by simp [norm_smul], by simp⟩

/-- The depth projections only see the input on the root. -/
theorem ColumnDepthFamily.proj_restrict_root (Ψ : ColumnDepthFamily V) (h : ℤ)
    (z : ColumnL2 V) :
    Ψ.proj h (columnL2Restriction (dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
      (dyadicGridCell_measurable _ _ _) z) = Ψ.proj h z := by
  unfold ColumnDepthFamily.proj
  rw [partitionColumnProjection_eq_sum, partitionColumnProjection_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact cellColumnProjection_input_superset _ _ _ _
    ((Ψ.mem_partition h c.val).mp c.property).2 z

/-- Integrals over a cell split along its depth-`(s+n)` generation (real-valued version). -/
theorem setIntegral_cell_eq_sum_generation_real (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ)
    {F : ℝ → ℝ} (hF : IntegrableOn F (dyadicGridCell G I.1 I.2)) :
    ∫ y in dyadicGridCell G I.1 I.2, F y =
      ∑ Q ∈ dyadicGeneration G I n, ∫ y in dyadicGridCell G Q.1 Q.2, F y := by
  have h := integral_biUnion_finset (dyadicGeneration G I n)
    (fun Q _ => dyadicGridCell_measurable G Q.1 Q.2) (dyadicGeneration_pairwiseDisjoint G I n)
    (μ := volume) (f := F)
    (fun Q hQ => hF.mono_set (dyadicGeneration_subset G I n hQ))
  rw [dyadicGeneration_union] at h
  exact h

theorem integrableOn_norm_sq_Lp (z : ColumnL2 V) (s : Set ℝ) :
    IntegrableOn (fun y => ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2) s :=
  ((Lp.memLp z).integrable_norm_pow two_ne_zero).integrableOn

/-- Local contraction: on a cell `I` of depth at most the depth of `P_h`,
`‖1_I P_h z‖ ≤ ‖1_I z‖`. -/
theorem ColumnDepthFamily.setIntegral_proj_le (Ψ : ColumnDepthFamily V) (h : ℤ)
    (z : ColumnL2 V) {I : ℤ × ℤ}
    (hI : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
    (hIh : I.1 ≤ Ψ.depth h) :
    ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖(Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Ψ.depth h = I.1 + n := ⟨(Ψ.depth h - I.1).toNat, by omega⟩
  rw [setIntegral_cell_eq_sum_generation_real _ I n (integrableOn_norm_sq_Lp _ _),
    setIntegral_cell_eq_sum_generation_real _ I n (integrableOn_norm_sq_Lp _ _)]
  refine Finset.sum_le_sum fun Q hQg => ?_
  have hQ1 : Q.1 = Ψ.depth h := by rw [dyadicGeneration_depth _ _ _ hQg, hn]
  have hQI := dyadicGeneration_subset _ _ _ hQg
  have hQ : Q ∈ (Ψ.partition h).cells := (Ψ.mem_partition h Q).mpr ⟨hQ1, hQI.trans hI⟩
  have hQc := (Ψ.partition h).subset hQ
  set! PQ := cellColumnProjection Ψ.D Ψ.A hQc with hPQ
  have e1 : ∫ y in dyadicGridCell Ψ.D.grid Q.1 Q.2, ‖(Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2 =
      ∫ y in dyadicGridCell Ψ.D.grid Q.1 Q.2, ‖(PQ z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
    integral_congr_ae ((Ψ.proj_ae_cell h z hQ).mono fun y hy => by beta_reduce; rw [hy])
  rw [e1]
  have hloc : PQ z = PQ (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
      (dyadicGridCell_measurable _ _ _) z) := by
    have := congrArg (fun T => T z) (cellColumnProjection_input_locality Ψ.D Ψ.A hQc)
    exact this.symm
  calc ∫ y in dyadicGridCell Ψ.D.grid Q.1 Q.2, ‖(PQ z : ℝ → ColumnHilbert V) y‖ ^ 2
      ≤ ∫ y, ‖(PQ z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
        setIntegral_le_integral ((Lp.memLp _).integrable_norm_pow two_ne_zero)
          (Filter.Eventually.of_forall fun _ => by positivity)
    _ = ‖PQ z‖ ^ 2 := (columnInput_norm_sq_integral _).symm
    _ ≤ ‖columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
          (dyadicGridCell_measurable _ _ _) z‖ ^ 2 := by
        rw [hloc]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((PQ.le_opNorm _).trans (by
            have := cellColumnProjection_norm_le Ψ.D Ψ.A hQc
            nlinarith only [norm_nonneg (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
              (dyadicGridCell_measurable _ _ _) z), this])) 2
    _ = _ := columnL2Restriction_norm_sq _ _ z

theorem ColumnDepthFamily.proj_eq_of_depth (Ψ : ColumnDepthFamily V) {h h' : ℤ}
    (hd : Ψ.depth h = Ψ.depth h') : Ψ.proj h = Ψ.proj h' := by
  have hp : Ψ.partition h = Ψ.partition h' := by
    unfold ColumnDepthFamily.partition
    congr 1
    rw [hd]
  rw [ColumnDepthFamily.proj, ColumnDepthFamily.proj, hp]

/-- Blueprint lem:delay, line 1558 (orthogonality of `P_{h+1} - P_h`): the successive
increments of the depth projections have total energy at most `‖1_J z‖²`. -/
theorem ColumnDepthFamily.increment_energy (Ψ : ColumnDepthFamily V) (z : ColumnL2 V)
    (Hs : Finset ℤ) :
    ∑ h ∈ Hs, ∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2,
      ‖(Ψ.proj (h + 1) z : ℝ → ColumnHilbert V) y - (Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      ∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2,
        ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  classical
  set J := Ψ.D.root with hJ
  set! z₀ := columnL2Restriction (dyadicGridCell Ψ.D.grid J.1 J.2)
    (dyadicGridCell_measurable _ _ _) z with hz₀
  set! T := (Ψ.N - J.1).toNat with hT
  set! P : ℕ → ColumnL2 V →L[ℂ] ColumnL2 V := fun n => Ψ.proj (J.1 + n) with hP
  have hbes := projection_successive_differences_bessel P T
    (fun n _ => Ψ.isStarProjection_proj _)
    (fun i _ j _ hij => Ψ.proj_nested (by omega)) z₀
  rw [Fin.sum_univ_eq_sum_range (fun n => ‖(P (n + 1) - P n) z₀‖ ^ 2) T] at hbes
  -- each increment
  set a : ℤ → ℝ := fun h => ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2,
      ‖(Ψ.proj (h + 1) z : ℝ → ColumnHilbert V) y - (Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2
    with ha
  have ha0 : ∀ h, 0 ≤ a h := fun h => integral_nonneg fun _ => by positivity
  have hle : ∀ h, a h ≤ ‖(Ψ.proj (h + 1) - Ψ.proj h) z‖ ^ 2 := by
    intro h
    rw [columnInput_norm_sq_integral]
    calc a h ≤ ∫ y, ‖(Ψ.proj (h + 1) z : ℝ → ColumnHilbert V) y -
          (Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
          refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun _ => by positivity)
          exact (((Lp.memLp _).sub (Lp.memLp _)).integrable_norm_pow two_ne_zero)
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub (Ψ.proj (h + 1) z) (Ψ.proj h z)] with y hy
          rw [sub_apply, hy, Pi.sub_apply]
  have hzero : ∀ h, ¬ (J.1 ≤ h ∧ h < Ψ.N) → a h = 0 := by
    intro h hh
    have hd : Ψ.depth (h + 1) = Ψ.depth h := by
      unfold ColumnDepthFamily.depth
      rcases not_and_or.mp hh with h1 | h1 <;> push Not at h1
      · rw [hJ] at h1
        rw [max_eq_left (by omega), max_eq_left (by omega)]
      · rw [min_eq_right (by omega), min_eq_right (by omega)]
    simp only [ha, Ψ.proj_eq_of_depth hd, sub_self, norm_zero]
    simp
  have hinc : ∀ h, J.1 ≤ h → h < Ψ.N →
      a h ≤ ‖(P ((h - J.1).toNat + 1) - P (h - J.1).toNat) z₀‖ ^ 2 := by
    intro h h1 h2
    refine (hle h).trans (le_of_eq ?_)
    have e1 : J.1 + (((h - J.1).toNat + 1 : ℕ) : ℤ) = h + 1 := by push_cast; omega
    have e2 : J.1 + ((h - J.1).toNat : ℤ) = h := by omega
    simp only [hP, e1, e2, sub_apply]
    rw [Ψ.proj_restrict_root, Ψ.proj_restrict_root]
  have hz₀ : ‖z₀‖ ^ 2 = ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2,
      ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := columnL2Restriction_norm_sq _ _ z
  rw [← hz₀]
  calc ∑ h ∈ Hs, a h = ∑ h ∈ Hs.filter (fun h => J.1 ≤ h ∧ h < Ψ.N), a h := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs with hh
        · rfl
        · exact hzero h hh
    _ ≤ ∑ h ∈ Hs.filter (fun h => J.1 ≤ h ∧ h < Ψ.N),
          ‖(P ((h - J.1).toNat + 1) - P (h - J.1).toNat) z₀‖ ^ 2 :=
        Finset.sum_le_sum fun h hh => hinc h (Finset.mem_filter.mp hh).2.1
          (Finset.mem_filter.mp hh).2.2
    _ = ∑ n ∈ (Hs.filter (fun h => J.1 ≤ h ∧ h < Ψ.N)).image (fun h => (h - J.1).toNat),
          ‖(P (n + 1) - P n) z₀‖ ^ 2 := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        have := (Finset.mem_filter.mp hx).2; have := (Finset.mem_filter.mp hy).2
        simp only at hxy; omega
    _ ≤ ∑ n ∈ Finset.range T, ‖(P (n + 1) - P n) z₀‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
          (fun _ _ _ => by positivity)
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
        have := (Finset.mem_filter.mp hh).2
        rw [Finset.mem_range, hT]; omega
    _ ≤ ‖z₀‖ ^ 2 := hbes

theorem measurable_column_coord (z : ColumnL2 V) (i : Option V) :
    Measurable fun y => (z : ℝ → ColumnHilbert V) y i :=
  (EuclideanSpace.proj i : ColumnHilbert V →L[ℂ] ℂ).continuous.measurable.comp
    (Lp.stronglyMeasurable z).measurable

theorem memLp_column_coord (z : ColumnL2 V) (i : Option V) :
    MemLp (fun y => (z : ℝ → ColumnHilbert V) y i) 2 volume :=
  ContinuousLinearMap.comp_memLp (EuclideanSpace.proj i : ColumnHilbert V →L[ℂ] ℂ) z

theorem ColumnDepthFamily.measurable_resid (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} (hψm : Measurable ψa) (h : ℤ) :
    Measurable (Ψ.resid f ψa h) :=
  ((Lp.stronglyMeasurable f).measurable.sub (measurable_column_coord _ none)).mul hψm

theorem ColumnDepthFamily.memLp_resid (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} (hψm : Measurable ψa)
    (hψ : ∀ y, ‖ψa y‖ ≤ 1) (h : ℤ) : MemLp (Ψ.resid f ψa h) 2 volume := by
  have hg := (Lp.memLp f).sub (memLp_column_coord (Ψ.proj h (physicalColumnInput f)) none)
  refine hg.of_le (Ψ.measurable_resid f hψm h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [ColumnDepthFamily.resid, norm_mul, Pi.sub_apply]
  exact mul_le_of_le_one_right (norm_nonneg _) (hψ y)

/-- `|E_h g| ≤ |I_h|^{-1/2} ‖g‖₂` pointwise. -/
theorem norm_depthExpectation_le_L2 (G : RealDyadicGrid) (h : ℤ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (y : ℝ) :
    ‖depthExpectation G h g y‖ ≤
      (Real.sqrt (dyadicGridLength G h))⁻¹ * Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
  set m := dyadicIndex G h y
  set Q := dyadicGridCell G h m
  have hl := dyadicGridLength_pos G h
  have hfin : volume Q < ⊤ := by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
  have h1 := setIntegral_norm_le_sqrt hfin (hg.restrict Q)
  rw [volume_real_cell] at h1
  have h2 : ∫ x in Q, ‖g x‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 :=
    setIntegral_le_integral (hg.integrable_norm_pow two_ne_zero)
      (Filter.Eventually.of_forall fun _ => by positivity)
  unfold depthExpectation cellAverage
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs := Real.sqrt_pos.mpr hl
  calc (dyadicGridLength G h)⁻¹ * ‖∫ x in Q, g x‖
      ≤ (dyadicGridLength G h)⁻¹ * (Real.sqrt (dyadicGridLength G h) *
          Real.sqrt (∫ x, ‖g x‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
          (h1.trans ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [← mul_assoc]; congr 1
        rw [show (dyadicGridLength G h)⁻¹ = (Real.sqrt (dyadicGridLength G h) *
            Real.sqrt (dyadicGridLength G h))⁻¹ by rw [Real.mul_self_sqrt hl.le]]
        field_simp

theorem memLp_depthExpectation (G : RealDyadicGrid) (h : ℤ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (s : Set ℝ) (hs : volume s < ⊤) :
    MemLp (depthExpectation G h g) 2 (volume.restrict s) := by
  have : IsFiniteMeasure (volume.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  exact MemLp.of_bound (measurable_depthExpectation G h g).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_depthExpectation_le_L2 G h hg))

theorem norm_coord_le (x : ColumnHilbert V) (i : Option V) : ‖x i‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le x i

theorem ColumnDepthFamily.resid_sub_le (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} (hψ : ∀ y, ‖ψa y‖ ≤ 1) (h : ℤ) (y : ℝ) :
    ‖Ψ.resid f ψa h y - Ψ.resid f ψa (h + 1) y‖ ^ 2 ≤
      ‖(Ψ.proj (h + 1) (physicalColumnInput f) : ℝ → ColumnHilbert V) y -
        (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  set a := (Ψ.proj (h + 1) (physicalColumnInput f) : ℝ → ColumnHilbert V) y
  set b := (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y
  have e : Ψ.resid f ψa h y - Ψ.resid f ψa (h + 1) y = (a - b) none * ψa y := by
    simp only [ColumnDepthFamily.resid, a, b, PiLp.sub_apply]; ring
  rw [e, norm_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact (mul_le_of_le_one_right (norm_nonneg _) (hψ y)).trans (norm_coord_le _ _)

theorem ColumnDepthFamily.moment_sub_ae (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} {p : V}
    (hscal : ∀ y, Ψ.D.scalar p y = star (ψa y)) {I : ℤ × ℤ}
    (hI : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
    (havail : ∀ c ∈ Ψ.D.cells, dyadicGridCell Ψ.D.grid c.1 c.2 ⊆
      dyadicGridCell Ψ.D.grid I.1 I.2 → p ∈ Ψ.A.labels c)
    {h : ℤ} (hIh : I.1 ≤ h) (hhN : h < Ψ.N) :
    ∀ᵐ y ∂volume.restrict (dyadicGridCell Ψ.D.grid I.1 I.2),
      ‖depthExpectation Ψ.D.grid (h + 1) (Ψ.resid f ψa (h + 1)) y -
        depthExpectation Ψ.D.grid h (Ψ.resid f ψa h) y‖ ^ 2 ≤
      Ψ.D.privateWeight p *
        ‖(Ψ.proj (h + 1) (physicalColumnInput f) : ℝ → ColumnHilbert V) y -
          (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  filter_upwards [Ψ.moment_ae f hscal hI havail (h := h + 1) (by omega) (by omega),
    Ψ.moment_ae f hscal hI havail hIh hhN.le] with y h1 h2
  rw [h1, h2, ← mul_sub, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Ψ.D.privateWeight_pos p).le]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    (Ψ.D.privateWeight_pos p).le
  rw [← PiLp.sub_apply]
  exact norm_coord_le _ _

theorem integral_physical_sq (f : Lp ℂ 2 (volume : Measure ℝ)) (s : Set ℝ) :
    ∫ y in s, ‖(physicalColumnInput (V := V) f : ℝ → ColumnHilbert V) y‖ ^ 2 =
      ∫ y in s, ‖(f : ℝ → ℂ) y‖ ^ 2 :=
  integral_congr_ae (ae_restrict_of_ae ((physicalColumnInput_ae (V := V) f).mono
    fun y hy => by simp only [hy.1]))

/-- Blueprint lem:delay, lines 1549–1553: a position-`a` projection family carrying the
predictor `(ψBar_a, √ε e_p)` on every use cell and its descendants, down to the depth `N`,
gives the scalar delay data: the residuals `(f_a - (P_h F_a)_phys) ψ_a`, their dyadic
conditional expectations, and the energies of the projection increments. -/
noncomputable def ColumnDepthFamily.delayData (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} (hψm : Measurable ψa)
    (hψ : ∀ y, ‖ψa y‖ ≤ 1) {p : V} (hscal : ∀ y, Ψ.D.scalar p y = star (ψa y))
    (hε1 : Ψ.D.privateWeight p ≤ 1) (S : Finset (ℤ × ℤ))
    (hS : ∀ I ∈ S, dyadicGridCell Ψ.D.grid I.1 I.2 ⊆
      dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
    (hSN : ∀ I ∈ S, I.1 ≤ Ψ.N)
    (havail : ∀ I ∈ S, ∀ c ∈ Ψ.D.cells, dyadicGridCell Ψ.D.grid c.1 c.2 ⊆
      dyadicGridCell Ψ.D.grid I.1 I.2 → p ∈ Ψ.A.labels c) :
    DelayData Ψ.D.grid Ψ.D.root S where
  N := Ψ.N
  D := Ψ.resid f ψa
  μ := fun h => depthExpectation Ψ.D.grid h (Ψ.resid f ψa h)
  e := fun h y => ‖(Ψ.proj (h + 1) (physicalColumnInput f) : ℝ → ColumnHilbert V) y -
    (Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2
  ε := Ψ.D.privateWeight p
  E := ∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2, ‖(f : ℝ → ℂ) y‖ ^ 2
  ε_nonneg := (Ψ.D.privateWeight_pos p).le
  ε_le_one := hε1
  sub := hS
  D_meas := Ψ.measurable_resid f hψm
  D_memLp := fun I _ h => (Ψ.memLp_resid f hψm hψ h).restrict _
  μ_memLp := fun I _ h => memLp_depthExpectation _ h (Ψ.memLp_resid f hψm hψ h) _
    (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top)
  μ_const := fun I _ j _ => depthConst_locConst le_rfl (depthConst_depthExpectation _ _ _)
  moment := fun I _ j _ Q hQ => by
    have hd := dyadicGeneration_depth _ _ _ hQ
    have := cell_isFiniteMeasure Ψ.D.grid Q.1 Q.2
    exact (setIntegral_depthExpectation_of_le _ Q (le_of_eq hd)
      (((Ψ.memLp_resid f hψm hψ _).restrict _).integrable one_le_two)).symm
  e_nonneg := fun h y => by positivity
  e_int := fun h => (((Lp.memLp _).sub (Lp.memLp _)).integrable_norm_pow two_ne_zero).integrableOn
  e_D := fun I _ h _ _ => Filter.Eventually.of_forall (Ψ.resid_sub_le f hψ h)
  e_μ := fun I hI h hIh hhN => Ψ.moment_sub_ae f hscal (hS I hI) (havail I hI) hIh hhN
  energy := fun Hs => by
    have h := Ψ.increment_energy (physicalColumnInput f) Hs
    rwa [integral_physical_sq] at h
  mass := fun y => ‖(f : ℝ → ℂ) y‖ ^ 2
  mass_nonneg := fun y => by positivity
  mass_int := ((Lp.memLp f).integrable_norm_pow two_ne_zero).integrableOn
  mass_le := le_rfl
  D_final := fun I hI => by
    have hroot : Ψ.D.root.1 ≤ I.1 := dyadicGridCell_depth_le_of_subset _ _ _ (hS I hI)
    have hc := Ψ.setIntegral_proj_le Ψ.N (physicalColumnInput f) (hS I hI)
      (by rw [Ψ.depth_eq (hroot.trans (hSN I hI)) le_rfl]; exact hSN I hI)
    rw [integral_physical_sq] at hc
    have hpt : ∀ y, ‖Ψ.resid f ψa Ψ.N y‖ ^ 2 ≤ 2 * ‖(f : ℝ → ℂ) y‖ ^ 2 +
        2 * ‖(Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 := by
      intro y
      have h1 : ‖Ψ.resid f ψa Ψ.N y‖ ≤ ‖(f : ℝ → ℂ) y‖ +
          ‖(Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ := by
        simp only [ColumnDepthFamily.resid, norm_mul]
        calc _ ≤ ‖(f : ℝ → ℂ) y - (Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V)
              y none‖ := mul_le_of_le_one_right (norm_nonneg _) (hψ y)
          _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl (norm_coord_le _ _))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖(f : ℝ → ℂ) y‖ -
        ‖(Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖)]
    have hi1 := ((Lp.memLp f).integrable_norm_pow two_ne_zero).integrableOn
      (s := dyadicGridCell Ψ.D.grid I.1 I.2)
    have hi2 := integrableOn_norm_sq_Lp (Ψ.proj Ψ.N (physicalColumnInput f))
      (dyadicGridCell Ψ.D.grid I.1 I.2)
    calc ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖Ψ.resid f ψa Ψ.N y‖ ^ 2
        ≤ ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, (2 * ‖(f : ℝ → ℂ) y‖ ^ 2 +
            2 * ‖(Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
            ((hi1.const_mul 2).add (hi2.const_mul 2)) (Filter.Eventually.of_forall hpt)
      _ = 2 * (∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖(f : ℝ → ℂ) y‖ ^ 2) +
          2 * ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
            ‖(Ψ.proj Ψ.N (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖(f : ℝ → ℂ) y‖ ^ 2 := by linarith
  μ_energy := fun S' hS' s hs h hsh hhN => by
    rcases S'.eq_empty_or_nonempty with he | ⟨I₀, hI₀⟩
    · rw [he, Finset.sum_empty]
      exact mul_nonneg (Ψ.D.privateWeight_pos p).le (integral_nonneg fun _ => by positivity)
    have hroot : Ψ.D.root.1 ≤ s := by
      rw [← hs I₀ hI₀]; exact dyadicGridCell_depth_le_of_subset _ _ _ (hS I₀ (hS' hI₀))
    have hdep : Ψ.depth h = h := Ψ.depth_eq (hroot.trans hsh) hhN
    have hcell : ∀ I ∈ S', ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
        ‖depthExpectation Ψ.D.grid h (Ψ.resid f ψa h) y‖ ^ 2 ≤
        Ψ.D.privateWeight p * ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
          ‖(f : ℝ → ℂ) y‖ ^ 2 := by
      intro I hI
      have hIS := hS' hI
      have hm := Ψ.moment_ae f hscal (hS I hIS) (havail I hIS) (h := h)
        (by rw [hs I hI]; exact hsh) hhN
      have hc := Ψ.setIntegral_proj_le h (physicalColumnInput f) (hS I hIS)
        (by rw [hdep, hs I hI]; exact hsh)
      rw [integral_physical_sq] at hc
      have hi := integrableOn_norm_sq_Lp (Ψ.proj h (physicalColumnInput f))
        (dyadicGridCell Ψ.D.grid I.1 I.2)
      calc ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
            ‖depthExpectation Ψ.D.grid h (Ψ.resid f ψa h) y‖ ^ 2
          ≤ ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, Ψ.D.privateWeight p *
              ‖(Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
              (hi.const_mul _) ?_
            filter_upwards [hm] with y hy
            rw [hy, norm_mul, mul_pow, Complex.norm_real,
              Real.norm_of_nonneg (Real.sqrt_nonneg _),
              Real.sq_sqrt (Ψ.D.privateWeight_pos p).le]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
              (norm_coord_le _ _) 2) (Ψ.D.privateWeight_pos p).le
        _ = Ψ.D.privateWeight p * ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
              ‖(Ψ.proj h (physicalColumnInput f) : ℝ → ColumnHilbert V) y‖ ^ 2 :=
            integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (Ψ.D.privateWeight_pos p).le
    calc ∑ I ∈ S', ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
          ‖depthExpectation Ψ.D.grid h (Ψ.resid f ψa h) y‖ ^ 2
        ≤ ∑ I ∈ S', Ψ.D.privateWeight p * ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
            ‖(f : ℝ → ℂ) y‖ ^ 2 := Finset.sum_le_sum hcell
      _ = Ψ.D.privateWeight p * ∑ I ∈ S', ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
            ‖(f : ℝ → ℂ) y‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_depth_cells_le _ _ S' s
            (fun I hI => ⟨hs I hI, hS I (hS' hI)⟩) (fun _ => by positivity)
            ((Lp.memLp f).integrable_norm_pow two_ne_zero).integrableOn)
          (Ψ.D.privateWeight_pos p).le

/-- The separated form is additive (subtractive) in the position-`a` input. -/
theorem separatedLocalForm_sub_left {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {a b : Fin 4} (hab : a ≠ b)
    {Q : ℝ → ℂ} (hQ : Measurable Q) {C : ℝ} (hQb : ∀ t, ‖Q t‖ ≤ C)
    {Fa₁ Fa₂ Fb : ℝ → ℂ} (hF₁m : Measurable Fa₁) (hF₂m : Measurable Fa₂)
    (hFbm : Measurable Fb)
    (hF₁ : MemLp Fa₁ 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    (hF₂ : MemLp Fa₂ 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    (hFb : MemLp Fb 2 (volume.restrict (Set.Ico a₀ (a₀ + r)))) :
    separatedLocalForm r w Q a b (fun y => Fa₁ y - Fa₂ y) Fb =
      separatedLocalForm r w Q a b Fa₁ Fb - separatedLocalForm r w Q a b Fa₂ Fb := by
  set s := Set.Ico a₀ (a₀ + r)
  have hsm : MeasurableSet s := measurableSet_Ico
  rw [separatedLocalForm_indicator hr hw, separatedLocalForm_indicator hr hw (Fa := Fa₁),
    separatedLocalForm_indicator hr hw (Fa := Fa₂)]
  have hGbm : Measurable (s.indicator Fb) := hFbm.indicator hsm
  have hGb : Integrable (s.indicator Fb) :=
    (integrable_indicator_iff hsm).mpr (hFb.integrable (by norm_num))
  have hd := fin_cast_sub_ne hab
  have hab' : (a : ℝ) ≠ (b : ℝ) := fun h => hd (by rw [h, sub_self])
  have hwm : Measurable w := hw.smooth.continuous.measurable
  have hint : ∀ F : ℝ → ℂ, Measurable F → MemLp F 2 (volume.restrict s) →
      Integrable (fun z : ℝ × ℝ => w z * Q z.2 * s.indicator F (realProgressionCoordinate a z) *
        s.indicator Fb (realProgressionCoordinate b z)) := by
    intro F hFm hF
    have hGm : Measurable (s.indicator F) := hFm.indicator hsm
    have hG : Integrable (s.indicator F) :=
      (integrable_indicator_iff hsm).mpr (hF.integrable (by norm_num))
    obtain ⟨hΦi, _⟩ := real_progression_pair_integral_norm hGm hGbm hG hGb hab'
    refine (hΦi.const_mul (localKernelSupBound κ * C)).mono' ?_ ?_
    · exact ((hwm.mul (hQ.comp measurable_snd)).mul
        (hGm.comp (continuous_realProgressionCoordinate a).measurable)).mul
        (hGbm.comp (continuous_realProgressionCoordinate b).measurable) |>.aestronglyMeasurable
    · filter_upwards with z
      simp only [norm_mul, realProgressionCoordinate]
      have h1 := admissibleLocalKernel_norm_le hw z
      have h2 := hQb z.2
      calc ‖w z‖ * ‖Q z.2‖ * ‖s.indicator F (z.1 + (a : ℝ) * z.2)‖ *
            ‖s.indicator Fb (z.1 + (b : ℝ) * z.2)‖
          = (‖w z‖ * ‖Q z.2‖) * (‖s.indicator F (z.1 + (a : ℝ) * z.2)‖ *
            ‖s.indicator Fb (z.1 + (b : ℝ) * z.2)‖) := by ring
        _ ≤ (localKernelSupBound κ * C) * (‖s.indicator F (z.1 + (a : ℝ) * z.2)‖ *
            ‖s.indicator Fb (z.1 + (b : ℝ) * z.2)‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _)
              (localKernelSupBound_nonneg κ)) (by positivity)
  have hsub : s.indicator (fun y => Fa₁ y - Fa₂ y) = fun y => s.indicator Fa₁ y -
      s.indicator Fa₂ y := by
    funext y; by_cases hy : y ∈ s <;> simp [Set.indicator, hy]
  unfold separatedLocalForm
  rw [← mul_sub, ← integral_sub (hint Fa₁ hF₁m hF₁) (hint Fa₂ hF₂m hF₂), hsub]
  congr 2; funext z; ring

/-- Blueprint lem:delay (Declaration delay, line 1566), `eq:delay-error`: let the position-`a`
projection family `P_h` (nested direct-sum projections on the depth-`h` partitions of the root
`J`, complete down to depth `N`) contain the predictor `(ψBar_a, √ε e_p)` on every use cell and
its descendants. Replacing the input `f_a ψ_a` at each use cell `I` of depth `s` by
`(P_{s+K₀} F_a)_phys ψ_a` changes the length-weighted scale sum of a fixed predictor term
`w_I(x,t) e(λ_* t²)`, `|λ_*| |I|² ≤ D_pred`, against an admissible opponent by at most
`C (2^{-K₀} + (1 + K₀) √ε) (1 + D_pred)⁴ K_b ‖1_J F_a‖ ‖1_J F_b‖` (the transfer constant `K_b`
of the opponent carries the polynomial in `log(2 D_h)` and `1 + L`). -/
theorem delayedPredictorReplacement (κ : LocalKernelClass) (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) {ψa : ℝ → ℂ} (hψm : Measurable ψa)
    (hψ : ∀ y, ‖ψa y‖ ≤ 1) {p : V} (hscal : ∀ y, Ψ.D.scalar p y = star (ψa y))
    (hε1 : Ψ.D.privateWeight p ≤ 1) (S : Finset (ℤ × ℤ))
    (hS : ∀ I ∈ S, dyadicGridCell Ψ.D.grid I.1 I.2 ⊆
      dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2)
    (havail : ∀ I ∈ S, ∀ c ∈ Ψ.D.cells, dyadicGridCell Ψ.D.grid c.1 c.2 ⊆
      dyadicGridCell Ψ.D.grid I.1 I.2 → p ∈ Ψ.A.labels c)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft Ψ.D.grid I.1 I.2)
      (dyadicGridLength Ψ.D.grid I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) (lam : ℝ) {Dp : ℝ} (hDp0 : 0 ≤ Dp)
    (hDp : ∀ I ∈ S, |lam| * dyadicGridLength Ψ.D.grid I.1 ^ 2 ≤ Dp)
    {ψb : ℝ → ℂ} (hψbm : Measurable ψb) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fb : ℝ → ℂ} {zb : ℤ × ℤ → ℝ → ℂ} {Kb : ℝ} (hKb : 0 ≤ Kb)
    (hzb : IsAdmissibleOpponent Ψ.D.grid Ψ.D.root Fb zb Kb) (hzbm : ∀ I, Measurable (zb I))
    (hzb2 : ∀ I ∈ S, MemLp (zb I) 2 (volume.restrict (dyadicGridCell Ψ.D.grid I.1 I.2)))
    (K₀ : ℕ) (hN : ∀ I ∈ S, I.1 + K₀ ≤ Ψ.N) :
    ∑ I ∈ S, dyadicGridLength Ψ.D.grid I.1 *
      ‖separatedLocalForm (dyadicGridLength Ψ.D.grid I.1) (w I)
          (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b
          (fun y => (f : ℝ → ℂ) y * ψa y) (fun y => ψb y * zb I y) -
        separatedLocalForm (dyadicGridLength Ψ.D.grid I.1) (w I)
          (fun t => (Real.fourierChar (lam * t ^ 2) : ℂ)) a b
          (fun y => (Ψ.proj (I.1 + K₀) (physicalColumnInput f) : ℝ → ColumnHilbert V) y none *
            ψa y) (fun y => ψb y * zb I y)‖ ≤
      delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt (Ψ.D.privateWeight p)) *
        (1 + Dp) ^ 4 *
        Real.sqrt (∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2,
          ‖(f : ℝ → ℂ) y‖ ^ 2) * Kb *
        Real.sqrt (∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2, ‖Fb y‖ ^ 2) := by
  set! Δ := Ψ.delayData f hψm hψ hscal hε1 S hS (fun I hI => by have := hN I hI; omega) havail
  have h := delay_error_bound κ Δ w hw hab lam hDp0 hDp hψbm hψb hKb hzb hzbm hzb2 K₀ hN
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_)) h
  congr 2
  have hr := dyadicGridLength_pos Ψ.D.grid I.1
  have hEq : Measurable (fun t : ℝ => (Real.fourierChar (lam * t ^ 2) : ℂ)) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul (continuous_pow 2)))).measurable
  have hfm : Measurable fun y => (f : ℝ → ℂ) y * ψa y :=
    (Lp.stronglyMeasurable f).measurable.mul hψm
  have hpm : Measurable fun y =>
      (Ψ.proj (I.1 + K₀) (physicalColumnInput f) : ℝ → ColumnHilbert V) y none * ψa y :=
    (measurable_column_coord _ none).mul hψm
  have hf2 : MemLp (fun y => (f : ℝ → ℂ) y * ψa y) 2 volume :=
    (Lp.memLp f).of_le hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hψ y))
  have hp2 : MemLp (fun y => (Ψ.proj (I.1 + K₀) (physicalColumnInput f) :
      ℝ → ColumnHilbert V) y none * ψa y) 2 volume :=
    (memLp_column_coord _ none).of_le hpm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hψ y))
  rw [← separatedLocalForm_sub_left hr (hw I hI) hab hEq (C := 1)
    (Fb := fun y => ψb y * zb I y)
    (fun t => by rw [Circle.norm_coe]) hfm hpm (hψbm.mul (hzbm I)) (hf2.restrict _)
    (hp2.restrict _) (memLp_mul_bounded_restrict hψbm hψb (hzb2 I hI))]
  congr 1
  funext y
  simp only [Δ, ColumnDepthFamily.delayData, ColumnDepthFamily.resid]
  ring

/-- Blueprint lem:delay, lines 1563–1565 (sequential replacement): the rolling differences
`(P_{s+K₀} - P_s) F` restricted to the cells `I` of depth `s` have square energy at most
`K₀² ‖1_J F‖²` (each increment is counted at most `K₀` times), so they form an admissible
square-energy opponent with transfer constant `K₀`. -/
theorem ColumnDepthFamily.rolling_energy (Ψ : ColumnDepthFamily V) (z : ColumnL2 V) (K₀ : ℕ)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ I ∈ S, dyadicGridCell Ψ.D.grid I.1 I.2 ⊆
      dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2) :
    ∑ I ∈ S, ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
      ‖(Ψ.proj (I.1 + K₀) z : ℝ → ColumnHilbert V) y -
        (Ψ.proj I.1 z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      (K₀ : ℝ) ^ 2 * ∫ y in dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2,
        ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  classical
  set J := Ψ.D.root
  set! e : ℤ → ℝ → ℝ := fun h y => ‖(Ψ.proj (h + 1) z : ℝ → ColumnHilbert V) y -
    (Ψ.proj h z : ℝ → ColumnHilbert V) y‖ ^ 2 with he
  set E := ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2
  have hei : ∀ h, IntegrableOn (e h) (dyadicGridCell Ψ.D.grid J.1 J.2) := fun h =>
    (((Lp.memLp _).sub (Lp.memLp _)).integrable_norm_pow two_ne_zero).integrableOn
  have hcast : ∀ (s : ℤ) (j : ℕ), s + ((j + 1 : ℕ) : ℤ) = s + j + 1 := fun s j => by
    push_cast; ring
  -- pointwise Cauchy–Schwarz over the `K₀` increments
  have hpt : ∀ I : ℤ × ℤ, ∀ y, ‖(Ψ.proj (I.1 + K₀) z : ℝ → ColumnHilbert V) y -
      (Ψ.proj I.1 z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      K₀ * ∑ j ∈ Finset.range K₀, e (I.1 + j) y := by
    intro I y
    have htel := Finset.sum_range_sub
      (fun j : ℕ => (Ψ.proj (I.1 + j) z : ℝ → ColumnHilbert V) y) K₀
    simp only [Nat.cast_zero, add_zero] at htel
    rw [← htel]
    calc ‖∑ j ∈ Finset.range K₀, ((Ψ.proj (I.1 + ((j + 1 : ℕ) : ℤ)) z : ℝ → ColumnHilbert V) y -
          (Ψ.proj (I.1 + j) z : ℝ → ColumnHilbert V) y)‖ ^ 2
        ≤ (∑ j ∈ Finset.range K₀, ‖(Ψ.proj (I.1 + ((j + 1 : ℕ) : ℤ)) z :
            ℝ → ColumnHilbert V) y - (Ψ.proj (I.1 + j) z : ℝ → ColumnHilbert V) y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Finset.range K₀).card * ∑ j ∈ Finset.range K₀, ‖(Ψ.proj (I.1 + ((j + 1 : ℕ) : ℤ)) z :
            ℝ → ColumnHilbert V) y - (Ψ.proj (I.1 + j) z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = K₀ * ∑ j ∈ Finset.range K₀, e (I.1 + j) y := by
          rw [Finset.card_range]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [he, hcast]
  have hE := fun Hs => Ψ.increment_energy z Hs
  calc ∑ I ∈ S, ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
        ‖(Ψ.proj (I.1 + K₀) z : ℝ → ColumnHilbert V) y -
          (Ψ.proj I.1 z : ℝ → ColumnHilbert V) y‖ ^ 2
      ≤ ∑ I ∈ S, ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
          (K₀ : ℝ) * ∑ j ∈ Finset.range K₀, e (I.1 + j) y := by
        refine Finset.sum_le_sum fun I hI => integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => by positivity) ?_
          (Filter.Eventually.of_forall (hpt I))
        exact (integrable_finsetSum _ fun j _ => (hei _).mono_set (hS I hI)).const_mul _
    _ = ∑ I ∈ S, (K₀ : ℝ) * ∑ j ∈ Finset.range K₀,
          ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, e (I.1 + j) y :=
        Finset.sum_congr rfl fun I hI => by
          rw [integral_const_mul, integral_finsetSum _ fun j _ => (hei _).mono_set (hS I hI)]
    _ = (K₀ : ℝ) * ∑ j ∈ Finset.range K₀, ∑ I ∈ S,
          ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, e (I.1 + j) y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (K₀ : ℝ) * ∑ j ∈ Finset.range K₀, E :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          sum_cells_energy_le _ J S hS e (fun _ _ => by positivity) hei hE j) (by positivity)
    _ = (K₀ : ℝ) ^ 2 * E := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### Current projections as admissible opponents -/

/-- The tree cell used for a row cell `I`: its ancestor at depth `min I.1 N`. -/
noncomputable def ColumnDepthFamily.anc (Ψ : ColumnDepthFamily V) (I : ℤ × ℤ) : ℤ × ℤ :=
  (min I.1 Ψ.N, dyadicIndex Ψ.D.grid (min I.1 Ψ.N) (dyadicGridLeft Ψ.D.grid I.1 I.2))

theorem ColumnDepthFamily.cell_sub_anc (Ψ : ColumnDepthFamily V) (I : ℤ × ℤ) :
    dyadicGridCell Ψ.D.grid I.1 I.2 ⊆
      dyadicGridCell Ψ.D.grid (Ψ.anc I).1 (Ψ.anc I).2 := by
  obtain ⟨m, hm⟩ := dyadicGridCell_ancestor Ψ.D.grid (min_le_left I.1 Ψ.N) I.2
  have hl := hm (dyadicGridCell_left_mem Ψ.D.grid I.1 I.2)
  have he : dyadicIndex Ψ.D.grid (min I.1 Ψ.N) (dyadicGridLeft Ψ.D.grid I.1 I.2) = m :=
    dyadicIndex_eq hl
  simp only [ColumnDepthFamily.anc, he]
  exact hm

theorem ColumnDepthFamily.cell_sub_anc_root (Ψ : ColumnDepthFamily V) {I : ℤ × ℤ}
    (hI : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2) :
    dyadicGridCell Ψ.D.grid (Ψ.anc I).1 (Ψ.anc I).2 ⊆
      dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 := by
  have hroot : Ψ.D.root.1 ≤ I.1 := dyadicGridCell_depth_le_of_subset _ _ _ hI
  have hk : Ψ.D.root.1 ≤ (Ψ.anc I).1 := le_min hroot Ψ.root_le
  rcases dyadicGridCell_nested_or_disjoint_of_le Ψ.D.grid hk Ψ.D.root.2 (Ψ.anc I).2 with
    hd | hs
  · exfalso
    have hy := dyadicGridCell_left_mem Ψ.D.grid I.1 I.2
    exact Set.disjoint_left.mp hd (hI hy) (Ψ.cell_sub_anc I hy)
  · exact hs

theorem ColumnDepthFamily.anc_mem (Ψ : ColumnDepthFamily V) {I : ℤ × ℤ}
    (hI : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2) :
    Ψ.anc I ∈ Ψ.D.cells :=
  Ψ.complete _ (Ψ.cell_sub_anc_root hI) (min_le_right _ _)

open scoped Classical in
/-- The current projection opponent `z_I = (P_{u(I)} F)_phys` (blueprint sec:base, line 1482;
lem:predictors, line 1532), with `u(I)` the tree cell above `I`. -/
noncomputable def ColumnDepthFamily.current (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (I : ℤ × ℤ) (y : ℝ) : ℂ :=
  if h : Ψ.anc I ∈ Ψ.D.cells then
    (cellColumnProjection Ψ.D Ψ.A h (physicalColumnInput f) : ℝ → ColumnHilbert V) y none
  else 0

/-- The physical coordinate as a contraction `L²(ℝ; ℂ ⊕ ℓ²(V)) → L²(ℝ)`. -/
noncomputable def physicalCoordLp (V : Type*) [Fintype V] :
    ColumnL2 V →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (EuclideanSpace.proj (none : Option V) : ColumnHilbert V →L[ℂ] ℂ).compLpL 2 volume

theorem physicalCoordLp_coeFn (w : ColumnL2 V) :
    (physicalCoordLp V w : ℝ → ℂ) =ᵐ[volume] fun y => (w : ℝ → ColumnHilbert V) y none :=
  ContinuousLinearMap.coeFn_compLp _ _

theorem norm_physicalCoordLp_le (w : ColumnL2 V) : ‖physicalCoordLp V w‖ ≤ ‖w‖ := by
  have hP : ‖(EuclideanSpace.proj (none : Option V) : ColumnHilbert V →L[ℂ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact norm_coord_le x none
  calc ‖physicalCoordLp V w‖ ≤ ‖physicalCoordLp V‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.norm_compLpL_le _).trans hP) (norm_nonneg _)
    _ = ‖w‖ := one_mul _

/-- The value of a row on a column input. -/
theorem cellRow_inner {G : RealDyadicGrid} {ι : Type} (R : CellRowFamily G ι) (i : ι)
    (w : ColumnL2 V) :
    inner ℂ ((cellRow_memLp R i).toLp (R.test i)) (physicalCoordLp V w) =
      ∫ y, conj (R.test i y) * (w : ℝ → ColumnHilbert V) y none := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (cellRow_memLp R i), physicalCoordLp_coeFn w] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- The compression constant of lem:compression with one projection layer. -/
noncomputable def compressionOneConst (D : ColumnTreeData V) : ℝ :=
  (512 * ((1 : ℕ) + 1 : ℝ) ^ 512 * Real.log (2 * D.budget)) ^ (512 * (1 + 1))

/-- Blueprint lem:predictors, proof line 1532, and sec:base, line 1482: the current projection
`z_I = (P_{u(I)} F)_phys` is an admissible opponent: every local Bessel row family over cells of
the root, applied to the current projections at the row cells, is controlled by the compression
constant of lem:compression (`eq:compression` with `m = 1`, a polynomial in `log(2 D)`). -/
theorem ColumnDepthFamily.current_admissible (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    IsAdmissibleOpponent Ψ.D.grid Ψ.D.root (f : ℝ → ℂ) (Ψ.current f)
      (compressionOneConst Ψ.D) := by
  classical
  intro ι R hR
  set z := physicalColumnInput (V := V) f with hz
  set J := Ψ.D.root
  set z₀ := columnL2Restriction (dyadicGridCell Ψ.D.grid J.1 J.2)
    (dyadicGridCell_measurable _ _ _) z with hz₀
  set B := R.bound with hB
  have hB0 : 0 ≤ B := R.bound_nonneg
  have hmem : ∀ i ∈ R.index, Ψ.anc (R.cell i) ∈ Ψ.D.cells := fun i hi => Ψ.anc_mem (hR i hi)
  -- the value of each term through the decision-cell projection
  have hterm : ∀ i (hi : i ∈ R.index), ∫ y, conj (R.test i y) * Ψ.current f (R.cell i) y =
      inner ℂ ((cellRow_memLp R i).toLp (R.test i)) (physicalCoordLp V
        (cellColumnProjection Ψ.D Ψ.A (hmem i hi) z₀)) := by
    intro i hi
    rw [cellRow_inner]
    have hsup : cellColumnProjection Ψ.D Ψ.A (hmem i hi) z₀ =
        cellColumnProjection Ψ.D Ψ.A (hmem i hi) z :=
      cellColumnProjection_input_superset _ _ _ _ (Ψ.cell_sub_anc_root (hR i hi)) z
    rw [hsup]
    simp only [ColumnDepthFamily.current, hmem i hi, ↓reduceDIte]; rfl
  -- the Bessel bound gives each term individually
  have hterm_le : ∀ i (hi : i ∈ R.index), ‖∫ y, conj (R.test i y) *
      Ψ.current f (R.cell i) y‖ ^ 2 ≤ B ^ 2 * ‖physicalCoordLp V
        (cellColumnProjection Ψ.D Ψ.A (hmem i hi) z₀)‖ ^ 2 := by
    intro i hi
    have hb := R.bessel (physicalCoordLp V (cellColumnProjection Ψ.D Ψ.A (hmem i hi) z₀))
    refine le_trans ?_ hb
    rw [hterm i hi, cellRow_inner_Lp]
    exact Finset.single_le_sum (f := fun j => ‖∫ y, conj (R.test j y) *
      (physicalCoordLp V (cellColumnProjection Ψ.D Ψ.A (hmem i hi) z₀) : ℝ → ℂ) y‖ ^ 2)
      (fun _ _ => by positivity) hi
  rcases hB0.eq_or_lt with hB0' | hBpos
  · -- vanishing Bessel bound: every term vanishes
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun i hi => ?_)) (by positivity)
    have h := hterm_le i hi
    rw [← hB0', zero_pow two_ne_zero, zero_mul] at h
    exact le_antisymm h (by positivity)
  -- normalized rows
  set! c : ℝ := B⁻¹ with hc
  set! ιs := {i // i ∈ R.index}
  set! Brow : ColumnRowFamily Ψ.D ιs ℂ :=
    { decision := fun i => Ψ.anc (R.cell i.val)
      decision_mem := fun i => hmem i.val i.property
      row := fun i => ((c : ℝ) : ℂ) • (innerSL ℂ ((cellRow_memLp R i.val).toLp
        (R.test i.val))).comp (physicalCoordLp V)
      bound := c * B
      bound_nonneg := by positivity
      square_sum := fun w => by
        have hb := R.bessel (physicalCoordLp V w)
        have hn := norm_physicalCoordLp_le w
        calc ∑ i : ιs, ‖(((c : ℝ) : ℂ) • (innerSL ℂ ((cellRow_memLp R i.val).toLp
              (R.test i.val))).comp (physicalCoordLp V)) w‖ ^ 2
            = c ^ 2 * ∑ i ∈ R.index, ‖∫ y, conj (R.test i y) *
                (physicalCoordLp V w : ℝ → ℂ) y‖ ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_coe_sort R.index]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
                cellRow_inner_Lp, norm_smul, mul_pow, Complex.norm_real,
                Real.norm_of_nonneg (by positivity)]
          _ ≤ c ^ 2 * (B ^ 2 * ‖physicalCoordLp V w‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ ≤ (c * B) ^ 2 * ‖w‖ ^ 2 := by
              rw [mul_pow, mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)) (by positivity)
      input_locality := fun i => by
        ext w
        simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply]
        congr 1
        rw [cellRow_inner, cellRow_inner]
        refine integral_congr_ae ?_
        filter_upwards [columnL2Indicator_coeFn (dyadicGridCell Ψ.D.grid
          (Ψ.anc (R.cell i.val)).1 (Ψ.anc (R.cell i.val)).2)
          (dyadicGridCell_measurable _ _ _) w] with y hy
        change conj (R.test i.val y) * (columnL2Indicator _ (dyadicGridCell_measurable _ _ _) w :
            ℝ → ColumnHilbert V) y none =
          conj (R.test i.val y) * (w : ℝ → ColumnHilbert V) y none
        rw [hy]
        by_cases hyc : y ∈ dyadicGridCell Ψ.D.grid (Ψ.anc (R.cell i.val)).1
            (Ψ.anc (R.cell i.val)).2
        · rw [Set.indicator_of_mem hyc]
        · have hyi : y ∉ dyadicGridCell Ψ.D.grid (R.cell i.val).1 (R.cell i.val).2 :=
            fun h => hyc (Ψ.cell_sub_anc _ h)
          rw [R.local_support i.val y hyi]; simp }
  have hBrow : Brow.bound ≤ 1 := by
    change c * B ≤ 1; rw [hc, inv_mul_cancel₀ hBpos.ne']
  have hcomp := columnSpatialCompression Ψ.D (fun _ => Ψ.A) 1 z₀ Brow hBrow
  rw [← compressionOneConst] at hcomp
  have hsq := pow_le_pow_left₀ (finiteRowNorm_nonneg _) hcomp 2
  rw [finiteRowNorm_sq] at hsq
  have hz₀n : ‖z₀‖ ^ 2 = ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2, ‖(f : ℝ → ℂ) y‖ ^ 2 := by
    rw [hz₀, columnL2Restriction_norm_sq, integral_physical_sq]
  have hrows : ∑ i : ιs, ‖Brow.row i (cellColumnProduct Ψ.D (fun _ => Ψ.A)
      (Brow.decision_mem i) 1 z₀)‖ ^ 2 = c ^ 2 * ∑ i ∈ R.index,
        ‖∫ y, conj (R.test i y) * Ψ.current f (R.cell i) y‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_coe_sort R.index]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm i.val i.property]
    change ‖(((c : ℝ) : ℂ) • (innerSL ℂ ((cellRow_memLp R i.val).toLp
        (R.test i.val))).comp (physicalCoordLp V))
        (cellColumnProjection Ψ.D Ψ.A (hmem i.val i.property)
          (ContinuousLinearMap.id ℂ _ z₀))‖ ^ 2 = _
    rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.id_apply, norm_smul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hrows, mul_pow, hz₀n] at hsq
  have hc2 : c ^ 2 * B ^ 2 = 1 := by rw [hc, ← mul_pow, inv_mul_cancel₀ hBpos.ne', one_pow]
  have hX : ∑ i ∈ R.index, ‖∫ y, conj (R.test i y) * Ψ.current f (R.cell i) y‖ ^ 2 =
      B ^ 2 * (c ^ 2 * ∑ i ∈ R.index, ‖∫ y, conj (R.test i y) *
        Ψ.current f (R.cell i) y‖ ^ 2) := by
    rw [← mul_assoc, mul_comm (B ^ 2), hc2, one_mul]
  rw [hX]
  calc B ^ 2 * (c ^ 2 * ∑ i ∈ R.index, ‖∫ y, conj (R.test i y) *
        Ψ.current f (R.cell i) y‖ ^ 2)
      ≤ B ^ 2 * (compressionOneConst Ψ.D ^ 2 *
          ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2, ‖(f : ℝ → ℂ) y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-- The attempt-level data of an adaptive fit (blueprint sec:reduction, line 429: an inherited
column family continues below a cut by retaining its columns): for each attempt root `K`, counts
`cnt K c` and atoms `atm K c` on the whole tree below `K`, extending along paths, given by bounded
charts, and agreeing with the segment lists on the segment cells. -/
def IsAttemptData (c₂ : ℕ) (B : ℝ) (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (M : ℕ)
    (roots : Finset (ℤ × ℤ)) (seg : ℤ × ℤ → ℤ × ℤ) (n : ℤ × ℤ → ℕ)
    (a : ℤ × ℤ → ℕ → ℝ → ℂ) (cnt : ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ) : Prop :=
  (∀ I ∈ dyadicFiniteTree G J N, cnt (seg I) I = n I ∧ ∀ i, atm (seg I) I i = a I i) ∧
  (∀ K ∈ roots, ∀ c ∈ dyadicFiniteTree G J N, ∀ d ∈ dyadicFiniteTree G J N,
    dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2 →
    dyadicGridCell G d.1 d.2 ⊆ dyadicGridCell G K.1 K.2 →
    cnt K d ≤ cnt K c ∧ ∀ i < cnt K d, atm K c i = atm K d i) ∧
  (∀ K ∈ roots, ∀ c ∈ dyadicFiniteTree G J N,
    dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G K.1 K.2 →
    cnt K c ≤ M ∧ ∀ i < cnt K c, ∃ (d : ℕ) (Φ : QuadraticChartData d),
      QuadraticChartComplexity c₂ B Φ ∧ IsBoundedQuadraticChart Φ ∧
        atm K c i = quadraticChartAtom Φ)

/-! ### Pair norms and the staggered replacement estimate -/

/-- Inputs `X` in slot `p` and `Y` in slot `p'`, spectators `z` elsewhere. -/
def slotPair (z : Fin 4 → ℝ → ℂ) (p p' : Fin 4) (X Y : ℝ → ℂ) : Fin 4 → ℝ → ℂ :=
  Function.update (Function.update z p X) p' Y

theorem slotPair_left {z : Fin 4 → ℝ → ℂ} {p p' : Fin 4} (h : p ≠ p') (X Y : ℝ → ℂ) :
    slotPair z p p' X Y p = X := by
  simp [slotPair, Function.update_of_ne h]

theorem slotPair_right (z : Fin 4 → ℝ → ℂ) (p p' : Fin 4) (X Y : ℝ → ℂ) :
    slotPair z p p' X Y p' = Y := by
  simp [slotPair]

theorem slotPair_other {z : Fin 4 → ℝ → ℂ} {p p' l : Fin 4} (hl : l ≠ p) (hl' : l ≠ p')
    (X Y : ℝ → ℂ) : slotPair z p p' X Y l = z l := by
  simp [slotPair, Function.update_of_ne hl, Function.update_of_ne hl']

theorem slotPair_comm (z : Fin 4 → ℝ → ℂ) {p p' : Fin 4} (h : p ≠ p') (X Y : ℝ → ℂ) :
    slotPair z p p' X Y = slotPair z p' p Y X := by
  unfold slotPair
  exact Function.update_comm h X Y z

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

section Delayed
variable {V : Type*} [Fintype V]

/-- The delayed opponent `z_I = (P_{I + K₀} F)_phys` (blueprint lem:delay, line 1565). -/
noncomputable def ColumnDepthFamily.delayed (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (K₀ : ℕ) (I : ℤ × ℤ) (y : ℝ) : ℂ :=
  (Ψ.proj (I.1 + K₀) (physicalColumnInput f) : ℝ → ColumnHilbert V) y none

theorem ColumnDepthFamily.memLp_coord_restrict (z : ColumnL2 V) (s : Set ℝ) :
    MemLp (fun y => (z : ℝ → ColumnHilbert V) y none) 2 (volume.restrict s) :=
  (memLp_column_coord z none).restrict s

/-- Delayed opponents have depth energy with constant one. -/
theorem ColumnDepthFamily.delayed_depthEnergy (Ψ : ColumnDepthFamily V)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (K₀ : ℕ) :
    HasDepthEnergy Ψ.D.grid Ψ.D.root (f : ℝ → ℂ) (Ψ.delayed f K₀) 1 := by
  classical
  intro s S hS
  rw [one_pow, one_mul]
  set z := physicalColumnInput (V := V) f
  set J := Ψ.D.root
  have hdisj : (S : Set (ℤ × ℤ)).PairwiseDisjoint
      (fun I => dyadicGridCell Ψ.D.grid I.1 I.2) := by
    intro I hI I' hI' hne
    have h1 : I.1 = I'.1 := by rw [(hS I hI).1, (hS I' hI').1]
    have h2 : I.2 ≠ I'.2 := fun h => hne (Prod.ext h1 h)
    have := dyadicGridCell_pairwiseDisjoint Ψ.D.grid I.1 h2
    simpa [Function.onFun, h1] using this
  calc ∑ I ∈ S, ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2, ‖Ψ.delayed f K₀ I y‖ ^ 2
      ≤ ∑ I ∈ S, ∫ y in dyadicGridCell Ψ.D.grid I.1 I.2,
          ‖(Ψ.proj (s + K₀) z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
        refine Finset.sum_le_sum fun I hI => ?_
        rw [← (hS I hI).1]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (integrableOn_norm_sq_Lp _ _) (Filter.Eventually.of_forall fun y => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le _ _) 2
    _ = ∫ y in ⋃ I ∈ S, dyadicGridCell Ψ.D.grid I.1 I.2,
          ‖(Ψ.proj (s + K₀) z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
        (integral_biUnion_finset S (fun I _ => dyadicGridCell_measurable _ _ _) hdisj
          (fun I _ => integrableOn_norm_sq_Lp _ _)).symm
    _ ≤ ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2,
          ‖(Ψ.proj (s + K₀) z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
        setIntegral_mono_set (integrableOn_norm_sq_Lp _ _)
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall (Set.iUnion₂_subset fun I hI => (hS I hI).2))
    _ ≤ ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
        Ψ.setIntegral_proj_le _ z subset_rfl (Ψ.root_le_depth _)
    _ = ∫ y in dyadicGridCell Ψ.D.grid J.1 J.2, ‖(f : ℝ → ℂ) y‖ ^ 2 := integral_physical_sq _ _

end Delayed

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### The replacement of both high inputs on a common root -/

theorem slots4_swap {a i k b : Fin 4} (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k)
    (hib : i ≠ b) (hkb : k ≠ b) (za φ φ' zb : ℝ → ℂ) :
    slots4 a i k za φ φ' zb = slots4 b i k zb φ φ' za := by
  funext l
  rcases fin_four_cover hai hak hab hik hib hkb l with rfl | rfl | rfl | rfl
  · rw [slots4_a]; simp [slots4, hab, hai, hak]
  · rw [slots4_i hai, slots4_i hib.symm]
  · rw [slots4_k hak hik, slots4_k hkb.symm hik]
  · rw [slots4_a]; simp [slots4, hab.symm, hib.symm, hkb.symm]

theorem memLp_restrict_of_normalized {a r : ℝ} (hr : 0 < r) {g : ℝ → ℂ}
    (hg : MemLp g 2 (normalizedIntervalMeasure a r)) : MemLp g 2 (volume.restrict (Set.Ico a (a +
        r))) := by
  unfold normalizedIntervalMeasure at hg
  have h1 : MemLp g 2 (volume.restrict (Set.Icc a (a + r))) := by
    have e : volume.restrict (Set.Icc a (a + r)) =
        ENNReal.ofReal r • (ENNReal.ofReal r⁻¹ • volume.restrict (Set.Icc a (a + r))) := by
      rw [smul_smul, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one,
        one_smul]
    rw [e]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact h1.mono_measure (Measure.restrict_mono Set.Ico_subset_Icc_self le_rfl)

end TrilinearHT.Auto

end
