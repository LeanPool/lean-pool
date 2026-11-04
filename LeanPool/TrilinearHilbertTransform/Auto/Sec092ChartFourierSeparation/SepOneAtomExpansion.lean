/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec092ChartFourierSeparation.SepOneAtomLattice

/-!
# Trilinear Hilbert transform: sep_one_atom_expansion
-/

@[expose] public section

section
open scoped FourierTransform
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform

open scoped Classical in
private def SepOneAtomExpansionConclusion1Statement : Prop :=
  ∀ (d : ℕ)
    (_ : (1 : ℕ) ≤ d)
    (A : QuadraticChartData d)
    (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (_ : ∀ (x : ℝ), |x| ≤ (1 : ℝ) → ψ x = (1 : ℝ))
    (hψ0 : ∀ (x : ℝ), (2 : ℝ) ≤ |x| → ψ x = (0 : ℝ))
    (i : ℤ)
    (a : ℤ)
    (b : ℤ)
    (_ : a ≠ b)
    (x : ℝ)
    (t : ℝ),
  ∀ (ki kb : Fin d → ℤ), HasSum (fun (p : Fin (d + d + d) → ℤ) => sepCoeff A.amplitude
    ψ i a b ki kb p * quadraticChartAtom (sepChartA A hψ hψ0 i a b ki (tripleFst p))
    (x + (↑a : ℝ) * t) * quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb (tripleSnd
    p)) (x + (↑b : ℝ) * t) * quadraticChartAtom (sepChartT A hψ hψ0 i a b (tripleThd
    p)) t) (sepFamilyValue A ψ i a b x t ki kb)




private theorem sep_one_atom_expansion_conclusion_1 : SepOneAtomExpansionConclusion1Statement := by
  classical
  intro d hd A ψ hψ hψ1 hψ0 i a b hab x t ki kb
  classical
  set θ := A.horizontal with hθ
  set ua : Fin d → ℝ := fun l => θ l * (x + a * t) with hua
  set ub : Fin d → ℝ := fun l => θ l * (x + b * t) with hub
  set ut : Fin d → ℝ := fun l => θ l * t with hut
  set ui : Fin d → ℝ := fun l => θ l * (x + i * t) with hui
  set F := sepCoupledVec A.amplitude ψ i a b ki kb with hF
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := sepCoupledVec_smooth A.smooth hψ i a b ki kb
  have hFsupp : ∀ v, F v ≠ 0 → ∀ l, |v l| ≤ 3 / 4 := fun v hv l => sepCoupledVec_support hv l
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_Icc (a := fun _ : Fin (d + d + d) => -(3 / 4 : ℝ))
      (b := fun _ => 3 / 4))
    intro v hv
    by_contra h
    exact hv ⟨fun l => (abs_le.mp (hFsupp v h l)).1, fun l => (abs_le.mp (hFsupp v h l)).2⟩
  obtain ⟨A₀, hA₀⟩ := exists_iteratedFDeriv_bound hFs hFc 0
  obtain ⟨Am, hAm⟩ := exists_iteratedFDeriv_bound hFs hFc (d + d + d + 1)
  have hA₀' : ∀ w, ‖F w‖ ≤ A₀ := fun w => by
    have := hA₀ w; rwa [norm_iteratedFDeriv_zero] at this
  obtain ⟨hexp, -, -, -⟩ := compact_cutoff_fourier_expansion (n := d + d + d)
    (m := d + d + d + 1) (by omega) (by omega) hFs (R := 3 / 4) (L := 3) (by norm_num)
    (by norm_num) (by norm_num) hFsupp (Φ := tensorCutoff ψ (3 / 4))
    (fun w hw => tensorCutoff_eq_one hψ1 (by norm_num) hw)
    (fun w hw l => (tensorCutoff_ne_zero_bound hψ0 (by norm_num) hw l).le.trans
      (by norm_num)) hA₀' hAm
  -- phase factors of the three charts
  set! αa : ℚ := (i - b) / (b - a)
  set! αb : ℚ := (a - i) / (b - a)
  set! Sq : ℚ := (i - a) * (i - b)
  set! Bk := chartMatrixPhase A.matrix θ (fun l => (ki l : ℝ))
  set! Bkb := chartMatrixPhase A.matrix θ (fun l => (kb l : ℝ))
  set! Pa : (Fin d → ℤ) → ℂ := fun da =>
    (Real.fourierChar ((-(αa : ℝ) * A.quadratic) * (x + a * t) ^ 2 +
      (-(αa : ℝ) * A.linear + αa * Bk) * (x + a * t)) : ℂ) *
    (Real.fourierChar (chartMatrixPhase (-αa • A.matrix) ua (ua - fun l => (da l : ℝ))) : ℂ)
    with hPa
  set! Pb : (Fin d → ℤ) → ℂ := fun db =>
    (Real.fourierChar ((-(αb : ℝ) * A.quadratic) * (x + b * t) ^ 2 +
      (-(αb : ℝ) * A.linear + αb * Bk - αb * Bkb) * (x + b * t)) : ℂ) *
    (Real.fourierChar (chartMatrixPhase (-αb • A.matrix) ub (ub - fun l => (db l : ℝ))) : ℂ)
    with hPb
  set! Pt : (Fin d → ℤ) → ℂ := fun dd =>
    (Real.fourierChar (((Sq : ℝ) * A.quadratic) * t ^ 2 + 0 * t) : ℂ) *
    (Real.fourierChar (chartMatrixPhase (Sq • A.matrix) ut (ut - fun l => (dd l : ℝ))) : ℂ)
    with hPt
  set! vD : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → Fin (d + d + d) → ℝ := fun D =>
    tripleVec (ua - fun l => (D.1 l : ℝ)) (ub - fun l => (D.2.1 l : ℝ))
      (ut - fun l => (D.2.2 l : ℝ)) with hvD
  -- the per-point identity
  have hD (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
      (Real.fourierChar (A.quadratic * (x + i * t) ^ 2 + A.linear * (x + i * t)) : ℂ) *
        (sepCoupledAmplitude A.amplitude ψ i a b ki kb (ua - fun l => (D.1 l : ℝ))
            (ub - fun l => (D.2.1 l : ℝ)) (ut - fun l => (D.2.2 l : ℝ)) *
          (Real.fourierChar (chartMatrixPhase A.matrix ui
            (ui - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ))) : ℂ)) =
      F (vD D) * (Pa D.1 * Pb D.2.1 * Pt D.2.2) := by
    have hFv : F (vD D) = sepCoupledAmplitude A.amplitude ψ i a b ki kb
        (ua - fun l => (D.1 l : ℝ)) (ub - fun l => (D.2.1 l : ℝ))
        (ut - fun l => (D.2.2 l : ℝ)) := by
      simp only [hF, hvD, sepCoupledVec, tripleFst_tripleVec, tripleSnd_tripleVec,
        tripleThd_tripleVec]
    rw [hFv]
    by_cases hc : D.2.1 = fun l => D.1 l + (b - a) * D.2.2 l + kb l
    · have hsplit : A.quadratic * (x + i * t) ^ 2 + A.linear * (x + i * t) +
          chartMatrixPhase A.matrix ui
            (ui - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ)) =
          ((-(αa : ℝ) * A.quadratic) * (x + a * t) ^ 2 +
              (-(αa : ℝ) * A.linear + αa * Bk) * (x + a * t) +
              chartMatrixPhase (-αa • A.matrix) ua (ua - fun l => (D.1 l : ℝ))) +
            ((-(αb : ℝ) * A.quadratic) * (x + b * t) ^ 2 +
                (-(αb : ℝ) * A.linear + αb * Bk - αb * Bkb) * (x + b * t) +
              chartMatrixPhase (-αb • A.matrix) ub (ub - fun l => (D.2.1 l : ℝ))) +
            (((Sq : ℝ) * A.quadratic) * t ^ 2 + 0 * t +
              chartMatrixPhase (Sq • A.matrix) ut (ut - fun l => (D.2.2 l : ℝ))) :=
        separation_phase_split A.matrix θ A.quadratic A.linear i a b hab x t
          D.1 D.2.1 D.2.2 ki kb hc
      simp only [hPa, hPb, hPt]
      rw [mul_comm (Real.fourierChar _ : ℂ), mul_assoc]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_comm, hsplit]
      simp only [AddChar.map_add_eq_mul, Circle.coe_mul]
    · have harg : (ua - fun l => (D.1 l : ℝ)) - (ub - fun l => (D.2.1 l : ℝ)) +
          ((b - a : ℤ) : ℝ) • (ut - fun l => (D.2.2 l : ℝ)) - (fun l => (kb l : ℝ)) =
          fun l => (((D.2.1 - fun l => D.1 l + (b - a) * D.2.2 l + kb l) l : ℤ) : ℝ) := by
        funext l
        simp only [hua, hub, hut, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      have hE0 : tensorCutoff ψ (1 / 3) ((ua - fun l => (D.1 l : ℝ)) -
          (ub - fun l => (D.2.1 l : ℝ)) + ((b - a : ℤ) : ℝ) • (ut - fun l => (D.2.2 l : ℝ)) -
            (fun l => (kb l : ℝ))) = 0 := by
        rw [harg, tensorCutoff_int hψ1 hψ0]
        simp [sub_ne_zero.mpr hc]
      simp only [sepCoupledAmplitude, hE0, mul_zero, zero_mul]
  -- the modulated factor amplitudes
  set! Ma : (Fin (d + d + d) → ℤ) → (Fin d → ℤ) → ℂ := fun p da =>
    modulatedCutoff ψ (3 / 4) 3 (tripleFst p) (ua - fun l => (da l : ℝ)) with hMa
  set! Mb : (Fin (d + d + d) → ℤ) → (Fin d → ℤ) → ℂ := fun p db =>
    modulatedCutoff ψ (3 / 4) 3 (tripleSnd p) (ub - fun l => (db l : ℝ)) with hMb
  set! Mt : (Fin (d + d + d) → ℤ) → (Fin d → ℤ) → ℂ := fun p dd =>
    modulatedCutoff ψ (3 / 4) 3 (tripleThd p) (ut - fun l => (dd l : ℝ)) with hMt
  have hDsum (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
      HasSum (fun p => sepCoeff A.amplitude ψ i a b ki kb p *
          ((Ma p D.1 * Pa D.1) * (Mb p D.2.1 * Pb D.2.1) * (Mt p D.2.2 * Pt D.2.2)))
        (F (vD D) * (Pa D.1 * Pb D.2.1 * Pt D.2.2)) := by
    have h := (hexp (vD D)).mul_right (Pa D.1 * Pb D.2.1 * Pt D.2.2)
    convert h using 1
    funext p
    rw [show (tensorCutoff ψ (3 / 4) (vD D) *
        (Real.fourierChar (∑ l, (p l : ℝ) * (vD D l / 3)) : ℂ)) =
        Ma p D.1 * Mb p D.2.1 * Mt p D.2.2 from modulated_tripleVec ψ (3 / 4) 3 p _ _ _]
    simp only [sepCoeff]
    ring
  -- a finite box of lattice points
  set! B' := chartLatticeBox (3 / 2) ua ×ˢ (chartLatticeBox (3 / 2) ub ×ˢ
    chartLatticeBox (3 / 2) ut) with hB'
  have hbox (z : Fin d → ℝ) (k : Fin d → ℤ)
      (hk : ∀ l, |z l - k l| ≤ 3 / 2) : k ∈ chartLatticeBox (3 / 2) z :=
    mem_chartLatticeBox_of_bound hk
  have hPbox (z : Fin d → ℝ) (k : Fin d → ℤ)
      (hk : sepPartition (z - fun l => (k l : ℝ)) ≠ 0) : k ∈ chartLatticeBox (3 / 2) z :=
    hbox z k fun l => by
      have := sepPartition_ne_zero hk l
      simp only [Pi.sub_apply] at this
      linarith
  have hMbox (z : Fin d → ℝ) (k q : Fin d → ℤ)
      (hk : modulatedCutoff ψ (3 / 4) 3 q (z - fun l => (k l : ℝ)) ≠ 0) :
      k ∈ chartLatticeBox (3 / 2) z :=
    hbox z k fun l => by
      have h1 : tensorCutoff ψ (3 / 4) (z - fun l => (k l : ℝ)) ≠ 0 := by
        intro h0; apply hk; simp only [modulatedCutoff, h0, zero_mul]
      have := tensorCutoff_ne_zero_bound hψ0 (by norm_num) h1 l
      simp only [Pi.sub_apply] at this
      linarith
  have hval : sepFamilyValue A ψ i a b x t ki kb =
      ∑ D ∈ B', F (vD D) * (Pa D.1 * Pb D.2.1 * Pt D.2.2) := by
    unfold sepFamilyValue
    rw [← tsum_mul_left]
    rw [tsum_eq_sum (s := B')]
    · exact Finset.sum_congr rfl fun D _ => hD D
    · intro D hDB
      have h0 : sepCoupledAmplitude A.amplitude ψ i a b ki kb (ua - fun l => (D.1 l : ℝ))
          (ub - fun l => (D.2.1 l : ℝ)) (ut - fun l => (D.2.2 l : ℝ)) = 0 := by
        by_contra h
        apply hDB
        unfold sepCoupledAmplitude at h
        have ha := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
        have hb := right_ne_zero_of_mul (left_ne_zero_of_mul h)
        have ht := right_ne_zero_of_mul h
        exact Finset.mem_product.mpr ⟨hPbox _ _ ha, Finset.mem_product.mpr
          ⟨hPbox _ _ hb, hPbox _ _ ht⟩⟩
      change (Real.fourierChar _ : ℂ) * (sepCoupledAmplitude A.amplitude ψ i a b ki kb
        (ua - fun l => (D.1 l : ℝ)) (ub - fun l => (D.2.1 l : ℝ))
        (ut - fun l => (D.2.2 l : ℝ)) * _) = 0
      rw [h0, zero_mul, mul_zero]
  have hatomA (p : Fin (d + d + d) → ℤ) :
      quadraticChartAtom (sepChartA A hψ hψ0 i a b ki (tripleFst p)) (x + a * t) =
        ∑ da ∈ chartLatticeBox (3 / 2) ua, Ma p da * Pa da := by
    unfold sepChartA
    rw [mkQuadraticChart_atom, tsum_eq_sum (s := chartLatticeBox (3 / 2) ua), Finset.mul_sum]
    · apply Finset.sum_congr rfl; intro da _
      simp only [hMa, hPa]
      ring
    · intro da hda
      have h0 : Ma p da = 0 := by
        by_contra h; exact hda (hMbox _ _ _ h)
      simp only [hMa] at h0
      rw [h0, zero_mul]
  have hatomB (p : Fin (d + d + d) → ℤ) :
      quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)) (x + b * t) =
        ∑ db ∈ chartLatticeBox (3 / 2) ub, Mb p db * Pb db := by
    unfold sepChartB
    rw [mkQuadraticChart_atom, tsum_eq_sum (s := chartLatticeBox (3 / 2) ub), Finset.mul_sum]
    · apply Finset.sum_congr rfl; intro db _
      simp only [hMb, hPb]
      ring
    · intro db hdb
      have h0 : Mb p db = 0 := by
        by_contra h; exact hdb (hMbox _ _ _ h)
      simp only [hMb] at h0
      rw [h0, zero_mul]
  have hatomT (p : Fin (d + d + d) → ℤ) :
      quadraticChartAtom (sepChartT A hψ hψ0 i a b (tripleThd p)) t =
        ∑ dd ∈ chartLatticeBox (3 / 2) ut, Mt p dd * Pt dd := by
    unfold sepChartT
    rw [mkQuadraticChart_atom, tsum_eq_sum (s := chartLatticeBox (3 / 2) ut), Finset.mul_sum]
    · apply Finset.sum_congr rfl; intro dd _
      simp only [hMt, hPt]
      ring
    · intro dd hdd
      have h0 : Mt p dd = 0 := by
        by_contra h; exact hdd (hMbox _ _ _ h)
      simp only [hMt] at h0
      rw [h0, zero_mul]
  rw [hval]
  convert hasSum_sum (s := B') (fun D _ => hDsum D) using 1
  funext p
  rw [hatomA, hatomB, hatomT, triple_sum_factor]
  simp only [hB', Finset.sum_product]


/-- Blueprint lem:separation, lines 1402–1407 (first part): the exact separation of
one atom in slot `i` along the other slots `a, b` and the time variable. The atom is
a finite sum over bounded carries of absolutely convergent series of products of
three chart atoms with matrices `-α_a C`, `-α_b C`, `S C`. -/
theorem sep_one_atom_expansion {d : ℕ} (hd : 1 ≤ d) (A : QuadraticChartData d) {H : ℝ}
    (hχ : ∀ w, A.amplitude w ≠ 0 → ∀ l, |w l| ≤ H) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i a b : ℤ) (hab : a ≠ b) (x t : ℝ) :
    (∀ ki kb : Fin d → ℤ, HasSum (fun p : Fin (d + d + d) → ℤ =>
        sepCoeff A.amplitude ψ i a b ki kb p *
          quadraticChartAtom (sepChartA A hψ hψ0 i a b ki (tripleFst p)) (x + a * t) *
          quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)) (x + b * t) *
          quadraticChartAtom (sepChartT A hψ hψ0 i a b (tripleThd p)) t)
        (sepFamilyValue A ψ i a b x t ki kb)) ∧
      quadraticChartAtom A (x + i * t) =
        ∑ ki ∈ slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊,
          ∑ kb ∈ slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊,
            sepFamilyValue A ψ i a b x t ki kb := by
  constructor
  · expose_names
    exact @sep_one_atom_expansion_conclusion_1 d hd A ψ hψ hψ1 hψ0 i a b hab x t
  · have h := sep_one_atom_lattice A.amplitude hχ hψ1 hψ0 A.matrix A.horizontal i a b x t
    simp only at h
    have hl : quadraticChartAtom A (x + i * t) =
        (Real.fourierChar (A.quadratic * (x + i * t) ^ 2 + A.linear * (x + i * t)) : ℂ) *
          ∑' n : Fin d → ℤ, A.amplitude ((fun l => A.horizontal l * (x + i * t)) -
              fun l => (n l : ℝ)) *
            (Real.fourierChar (chartMatrixPhase A.matrix (fun l => A.horizontal l * (x + i * t))
              ((fun l => A.horizontal l * (x + i * t)) - fun l => (n l : ℝ))) : ℂ) := rfl
    rw [hl, h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ki _
    rw [Finset.mul_sum]
    rfl

theorem tensorCutoff_norm_le_one {d : ℕ} {ψ : ℝ → ℝ} (hψ1 : ∀ x, |ψ x| ≤ 1) (r : ℝ)
    (w : Fin d → ℝ) : ‖tensorCutoff ψ r w‖ ≤ 1 :=
  chartCoordinateProduct_norm_le_one (fun t => ψ (t / r)) (fun _ => hψ1 _) w

theorem modulatedCutoff_norm_le_one {d : ℕ} {ψ : ℝ → ℝ} (hψ1 : ∀ x, |ψ x| ≤ 1) (r L : ℝ)
    (p : Fin d → ℤ) (w : Fin d → ℝ) : ‖modulatedCutoff ψ r L p w‖ ≤ 1 := by
  unfold modulatedCutoff
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact tensorCutoff_norm_le_one hψ1 r w

/-- An atom whose amplitude is a modulated plateau cutoff of radius `3/4` is bounded
by `6^d`, uniformly in the modulation and all phase parameters. -/
theorem modulatedChart_atom_norm_le {d : ℕ} {ψ : ℝ → ℝ} (hψ1 : ∀ x, |ψ x| ≤ 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (θ : Fin d → ℝ) (lam β : ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (p : Fin d → ℤ) (hG : ContDiff ℝ (⊤ : ℕ∞)
      (modulatedCutoff ψ (3 / 4) 3 p)) (hGc : HasCompactSupport (modulatedCutoff ψ (3 / 4) 3 p))
    (y : ℝ) :
    ‖quadraticChartAtom (mkQuadraticChart θ lam β C (modulatedCutoff ψ (3 / 4) 3 p) hG hGc) y‖ ≤
      6 ^ d := by
  classical
  rw [mkQuadraticChart_atom, norm_mul, Circle.norm_coe, one_mul]
  set u : Fin d → ℝ := fun l => θ l * y
  have hzero : ∀ n ∉ chartLatticeBox (3 / 2) u,
      modulatedCutoff ψ (3 / 4) 3 p (u - fun l => (n l : ℝ)) *
        (Real.fourierChar (chartMatrixPhase C u (u - fun l => (n l : ℝ))) : ℂ) = 0 := by
    intro n hn
    have h0 : modulatedCutoff ψ (3 / 4) 3 p (u - fun l => (n l : ℝ)) = 0 := by
      by_contra h
      apply hn
      apply mem_chartLatticeBox_of_bound
      intro l
      have h1 : tensorCutoff ψ (3 / 4) (u - fun l => (n l : ℝ)) ≠ 0 := by
        intro h0; apply h; simp only [modulatedCutoff, h0, zero_mul]
      have := tensorCutoff_ne_zero_bound hψ0 (by norm_num) h1 l
      simp only [Pi.sub_apply] at this
      linarith
    rw [h0, zero_mul]
  rw [tsum_eq_sum hzero]
  calc ‖∑ n ∈ chartLatticeBox (3 / 2) u, modulatedCutoff ψ (3 / 4) 3 p (u - fun l => (n l : ℝ)) *
        (Real.fourierChar (chartMatrixPhase C u (u - fun l => (n l : ℝ))) : ℂ)‖ ≤
      ∑ _n ∈ chartLatticeBox (3 / 2) u, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, Circle.norm_coe, mul_one]
        exact modulatedCutoff_norm_le_one hψ1 _ _ _ _
    _ = (chartLatticeBox (3 / 2) u).card := by simp
    _ ≤ (2 * (3 / 2) + 3) ^ d := chartLatticeBox_card_le (by norm_num) u
    _ = 6 ^ d := by norm_num

/-- The separation coefficients are absolutely summable. -/
theorem sepCoeff_summable {d : ℕ} (hd : 1 ≤ d) {χ : (Fin d → ℝ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0)
    (i a b : ℤ) (ki kb : Fin d → ℤ) :
    Summable (fun p => ‖sepCoeff χ ψ i a b ki kb p‖) := by
  set F := sepCoupledVec χ ψ i a b ki kb
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := sepCoupledVec_smooth hχ hψ i a b ki kb
  have hFsupp : ∀ v, F v ≠ 0 → ∀ l, |v l| ≤ 3 / 4 := fun v hv l => sepCoupledVec_support hv l
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_Icc (a := fun _ : Fin (d + d + d) => -(3 / 4 : ℝ))
      (b := fun _ => 3 / 4))
    intro v hv
    by_contra h
    exact hv ⟨fun l => (abs_le.mp (hFsupp v h l)).1, fun l => (abs_le.mp (hFsupp v h l)).2⟩
  obtain ⟨A₀, hA₀⟩ := exists_iteratedFDeriv_bound hFs hFc 0
  obtain ⟨Am, hAm⟩ := exists_iteratedFDeriv_bound hFs hFc (d + d + d + 1)
  have hA₀' : ∀ w, ‖F w‖ ≤ A₀ := fun w => by
    have := hA₀ w; rwa [norm_iteratedFDeriv_zero] at this
  exact (compact_cutoff_fourier_expansion (n := d + d + d) (m := d + d + d + 1) (by omega)
    (by omega) hFs (R := 3 / 4) (L := 3) (by norm_num) (by norm_num) (by norm_num) hFsupp
    (Φ := tensorCutoff ψ (3 / 4)) (fun w hw => tensorCutoff_eq_one hψ1 (by norm_num) hw)
    (fun w hw l => (tensorCutoff_ne_zero_bound hψ0 (by norm_num) hw l).le.trans
      (by norm_num)) hA₀' hAm).2.1

/-- One term of the one-atom separation series. -/
noncomputable def sepTerm {d : ℕ} (A : QuadraticChartData d) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i a b : ℤ) (x t : ℝ)
    (ki kb : Fin d → ℤ) (p : Fin (d + d + d) → ℤ) : ℂ :=
  sepCoeff A.amplitude ψ i a b ki kb p *
    quadraticChartAtom (sepChartA A hψ hψ0 i a b ki (tripleFst p)) (x + a * t) *
    quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)) (x + b * t) *
    quadraticChartAtom (sepChartT A hψ hψ0 i a b (tripleThd p)) t

theorem sepTerm_norm_le {d : ℕ} (A : QuadraticChartData d) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0)
    (i a b : ℤ) (x t : ℝ) (ki kb : Fin d → ℤ) (p : Fin (d + d + d) → ℤ) :
    ‖sepTerm A hψ hψ0 i a b x t ki kb p‖ ≤
      ‖sepCoeff A.amplitude ψ i a b ki kb p‖ * 6 ^ (3 * d) := by
  unfold sepTerm
  rw [norm_mul, norm_mul, norm_mul]
  have hA' : ‖quadraticChartAtom (sepChartA A hψ hψ0 i a b ki (tripleFst p)) (x + a * t)‖ ≤
      6 ^ d := by
    unfold sepChartA; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _
  have hB' : ‖quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)) (x + b * t)‖ ≤
      6 ^ d := by
    unfold sepChartB; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _
  have hT' : ‖quadraticChartAtom (sepChartT A hψ hψ0 i a b (tripleThd p)) t‖ ≤ 6 ^ d := by
    unfold sepChartT; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _
  have hc := norm_nonneg (sepCoeff A.amplitude ψ i a b ki kb p)
  calc _ ≤ ‖sepCoeff A.amplitude ψ i a b ki kb p‖ * 6 ^ d * 6 ^ d * 6 ^ d := by gcongr
    _ = _ := by rw [show 3 * d = d + d + d by ring, pow_add, pow_add]; ring

/-- Blueprint lem:separation, line 1407: two atoms in distinct slots `i, k` are
separated along the remaining slots `a, b` and the time variable; their product is
an absolutely convergent series of products of separated factor atoms. -/
theorem sep_pair_expansion {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e)
    (A : QuadraticChartData d) (A' : QuadraticChartData e) {H H' : ℝ}
    (hχ : ∀ w, A.amplitude w ≠ 0 → ∀ l, |w l| ≤ H)
    (hχ' : ∀ w, A'.amplitude w ≠ 0 → ∀ l, |w l| ≤ H') {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i k a b : ℤ) (hab : a ≠ b) (x t : ℝ) :
    let Ki := slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊
    let Kb := slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
    let Ki' := slowValueBox e ⌈H' + 1 + |((k - a : ℤ) : ℝ)|⌉₊
    let Kb' := slowValueBox e ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
    HasSum (fun q : ((Ki × Kb) × (Ki' × Kb')) × ((Fin (d + d + d) → ℤ) × (Fin (e + e + e) → ℤ)) =>
        sepTerm A hψ hψ0 i a b x t q.1.1.1 q.1.1.2 q.2.1 *
          sepTerm A' hψ hψ0 k a b x t q.1.2.1 q.1.2.2 q.2.2)
      (quadraticChartAtom A (x + i * t) * quadraticChartAtom A' (x + k * t)) := by
  intro Ki Kb Ki' Kb'
  classical
  obtain ⟨hs, hsum⟩ := sep_one_atom_expansion hd A hχ hψ hψ1 hψ0 i a b hab x t
  obtain ⟨hs', hsum'⟩ := sep_one_atom_expansion he A' hχ' hψ hψ1 hψ0 k a b hab x t
  change quadraticChartAtom A (x + i * t) =
    ∑ ki ∈ Ki, ∑ kb ∈ Kb, sepFamilyValue A ψ i a b x t ki kb at hsum
  change quadraticChartAtom A' (x + k * t) =
    ∑ ki ∈ Ki', ∑ kb ∈ Kb', sepFamilyValue A' ψ k a b x t ki kb at hsum'
  clear_value Ki Kb Ki' Kb'
  have hpair (c : (Ki × Kb) × (Ki' × Kb')) :
      HasSum (fun r : (Fin (d + d + d) → ℤ) × (Fin (e + e + e) → ℤ) =>
          sepTerm A hψ hψ0 i a b x t c.1.1 c.1.2 r.1 *
            sepTerm A' hψ hψ0 k a b x t c.2.1 c.2.2 r.2)
        (sepFamilyValue A ψ i a b x t c.1.1 c.1.2 *
          sepFamilyValue A' ψ k a b x t c.2.1 c.2.2) := by
    have h1 := hs c.1.1 c.1.2
    have h2 := hs' c.2.1 c.2.2
    refine HasSum.mul h1 h2 ?_
    apply summable_mul_of_summable_norm
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun p => sepTerm_norm_le A hψ hψ1' hψ0 i a b x t c.1.1 c.1.2 p) ?_
      exact (sepCoeff_summable hd A.smooth hψ hψ1 hψ0 i a b c.1.1 c.1.2).mul_right _
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun p => sepTerm_norm_le A' hψ hψ1' hψ0 k a b x t c.2.1 c.2.2 p) ?_
      exact (sepCoeff_summable he A'.smooth hψ hψ1 hψ0 k a b c.2.1 c.2.2).mul_right _
  have hval : quadraticChartAtom A (x + i * t) * quadraticChartAtom A' (x + k * t) =
      ∑ c : (Ki × Kb) × (Ki' × Kb'), sepFamilyValue A ψ i a b x t c.1.1 c.1.2 *
        sepFamilyValue A' ψ k a b x t c.2.1 c.2.2 := by
    have e1 : (∑ ki ∈ Ki, ∑ kb ∈ Kb, sepFamilyValue A ψ i a b x t ki kb) =
        ∑ c : Ki × Kb, sepFamilyValue A ψ i a b x t c.1 c.2 := by
      rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Ki]
      apply Finset.sum_congr rfl; intro c _
      rw [← Finset.sum_coe_sort Kb]
    have e2 : (∑ ki ∈ Ki', ∑ kb ∈ Kb', sepFamilyValue A' ψ k a b x t ki kb) =
        ∑ c : Ki' × Kb', sepFamilyValue A' ψ k a b x t c.1 c.2 := by
      rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Ki']
      apply Finset.sum_congr rfl; intro c _
      rw [← Finset.sum_coe_sort Kb']
    rw [hsum, hsum', e1, e2, Finset.sum_mul_sum, ← Finset.univ_product_univ,
      Finset.sum_product]
    conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [hval]
  exact hasSum_prod_of_fintype hpair

/-- Normalizing a chart whose atom is bounded by `M > 0` to a bounded atom. -/
theorem scaleChart_bounded {d : ℕ} (A : QuadraticChartData d) {M : ℝ} (hM : 0 < M)
    (hA : ∀ y, ‖quadraticChartAtom A y‖ ≤ M) :
    IsBoundedQuadraticChart (scaleQuadraticChartAmplitude ((M : ℂ)⁻¹) A) := by
  intro y
  rw [scaleQuadraticChartAmplitude_atom, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hM]
  rw [inv_mul_le_iff₀ hM, mul_one]
  exact hA y

section SepPair
variable {d e : ℕ} (A : QuadraticChartData d) (A' : QuadraticChartData e) {ψ : ℝ → ℝ}
  (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i k a b : ℤ)

/-- The bounded slot-`a` factor of a separated pair. -/
noncomputable def sepPairChartA (ki : Fin d → ℤ) (kj : Fin e → ℤ)
    (p : Fin (d + d + d) → ℤ) (p' : Fin (e + e + e) → ℤ) : QuadraticChartData (d + e) :=
  productQuadraticChart
    (scaleQuadraticChartAmplitude (((6 ^ d : ℝ) : ℂ)⁻¹)
      (sepChartA A hψ hψ0 i a b ki (tripleFst p)))
    (scaleQuadraticChartAmplitude (((6 ^ e : ℝ) : ℂ)⁻¹)
      (sepChartA A' hψ hψ0 k a b kj (tripleFst p')))

/-- The bounded slot-`b` factor of a separated pair. -/
noncomputable def sepPairChartB (ki kb : Fin d → ℤ) (kj kc : Fin e → ℤ)
    (p : Fin (d + d + d) → ℤ) (p' : Fin (e + e + e) → ℤ) : QuadraticChartData (d + e) :=
  productQuadraticChart
    (scaleQuadraticChartAmplitude (((6 ^ d : ℝ) : ℂ)⁻¹)
      (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)))
    (scaleQuadraticChartAmplitude (((6 ^ e : ℝ) : ℂ)⁻¹)
      (sepChartB A' hψ hψ0 k a b kj kc (tripleSnd p')))

/-- The bounded time factor of a separated pair. -/
noncomputable def sepPairChartT (p : Fin (d + d + d) → ℤ) (p' : Fin (e + e + e) → ℤ) :
    QuadraticChartData (d + e) :=
  productQuadraticChart
    (scaleQuadraticChartAmplitude (((6 ^ d : ℝ) : ℂ)⁻¹)
      (sepChartT A hψ hψ0 i a b (tripleThd p)))
    (scaleQuadraticChartAmplitude (((6 ^ e : ℝ) : ℂ)⁻¹)
      (sepChartT A' hψ hψ0 k a b (tripleThd p')))

end SepPair

theorem sepChart_atom_bounds {d : ℕ} (A : QuadraticChartData d) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0)
    (i a b : ℤ) (ki kb pa pb pt : Fin d → ℤ) (y : ℝ) :
    ‖quadraticChartAtom (sepChartA A hψ hψ0 i a b ki pa) y‖ ≤ 6 ^ d ∧
      ‖quadraticChartAtom (sepChartB A hψ hψ0 i a b ki kb pb) y‖ ≤ 6 ^ d ∧
      ‖quadraticChartAtom (sepChartT A hψ hψ0 i a b pt) y‖ ≤ 6 ^ d := by
  refine ⟨?_, ?_, ?_⟩
  · unfold sepChartA; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _
  · unfold sepChartB; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _
  · unfold sepChartT; exact modulatedChart_atom_norm_le hψ1' hψ0 _ _ _ _ _ _ _ _

/-- The factors of a separated pair are bounded atoms. -/
theorem sepPairCharts_bounded {d e : ℕ} (A : QuadraticChartData d) (A' : QuadraticChartData e)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i k a b : ℤ) (ki kb : Fin d → ℤ) (kj kc : Fin e → ℤ)
    (p : Fin (d + d + d) → ℤ) (p' : Fin (e + e + e) → ℤ) :
    IsBoundedQuadraticChart (sepPairChartA A A' hψ hψ0 i k a b ki kj p p') ∧
      IsBoundedQuadraticChart (sepPairChartB A A' hψ hψ0 i k a b ki kb kj kc p p') ∧
      IsBoundedQuadraticChart (sepPairChartT A A' hψ hψ0 i k a b p p') := by
  have h6d : (0 : ℝ) < 6 ^ d := by positivity
  have h6e : (0 : ℝ) < 6 ^ e := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact productQuadraticChart_bounded
      (scaleChart_bounded _ h6d fun y => (sepChart_atom_bounds A hψ hψ1' hψ0 i a b ki ki
        (tripleFst p) (tripleFst p) (tripleFst p) y).1)
      (scaleChart_bounded _ h6e fun y => (sepChart_atom_bounds A' hψ hψ1' hψ0 k a b kj kj
        (tripleFst p') (tripleFst p') (tripleFst p') y).1)
  · exact productQuadraticChart_bounded
      (scaleChart_bounded _ h6d fun y => (sepChart_atom_bounds A hψ hψ1' hψ0 i a b ki kb
        (tripleSnd p) (tripleSnd p) (tripleSnd p) y).2.1)
      (scaleChart_bounded _ h6e fun y => (sepChart_atom_bounds A' hψ hψ1' hψ0 k a b kj kc
        (tripleSnd p') (tripleSnd p') (tripleSnd p') y).2.1)
  · exact productQuadraticChart_bounded
      (scaleChart_bounded _ h6d fun y => (sepChart_atom_bounds A hψ hψ1' hψ0 i a b ki kb
        (tripleThd p) (tripleThd p) (tripleThd p) y).2.2)
      (scaleChart_bounded _ h6e fun y => (sepChart_atom_bounds A' hψ hψ1' hψ0 k a b kj kc
        (tripleThd p') (tripleThd p') (tripleThd p') y).2.2)

/-- Blueprint lem:separation, eq:separation: the exact expansion
`φ_i(y_i) φ_k(y_k) = Σ c ψ_a(y_a) ψ_b(y_b) Q(t)` with bounded factor atoms. -/
theorem sep_pair_expansion_normalized {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e)
    (A : QuadraticChartData d) (A' : QuadraticChartData e) {H H' : ℝ}
    (hχ : ∀ w, A.amplitude w ≠ 0 → ∀ l, |w l| ≤ H)
    (hχ' : ∀ w, A'.amplitude w ≠ 0 → ∀ l, |w l| ≤ H') {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i k a b : ℤ) (hab : a ≠ b) (x t : ℝ) :
    let Ki := slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊
    let Kb := slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
    let Ki' := slowValueBox e ⌈H' + 1 + |((k - a : ℤ) : ℝ)|⌉₊
    let Kb' := slowValueBox e ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
    HasSum (fun q : ((Ki × Kb) × (Ki' × Kb')) × ((Fin (d + d + d) → ℤ) × (Fin (e + e + e) → ℤ)) =>
        (sepCoeff A.amplitude ψ i a b q.1.1.1 q.1.1.2 q.2.1 *
            sepCoeff A'.amplitude ψ k a b q.1.2.1 q.1.2.2 q.2.2 *
            (((6 ^ d : ℝ) : ℂ) ^ 3 * ((6 ^ e : ℝ) : ℂ) ^ 3)) *
          quadraticChartAtom (sepPairChartA A A' hψ hψ0 i k a b q.1.1.1 q.1.2.1 q.2.1 q.2.2)
            (x + a * t) *
          quadraticChartAtom (sepPairChartB A A' hψ hψ0 i k a b q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2
            q.2.1 q.2.2) (x + b * t) *
          quadraticChartAtom (sepPairChartT A A' hψ hψ0 i k a b q.2.1 q.2.2) t)
      (quadraticChartAtom A (x + i * t) * quadraticChartAtom A' (x + k * t)) := by
  intro Ki Kb Ki' Kb'
  have h := sep_pair_expansion hd he A A' hχ hχ' hψ hψ1' hψ1 hψ0 i k a b hab x t
  convert h using 1
  funext q
  have h6d : ((6 ^ d : ℝ) : ℂ) ≠ 0 := by norm_num
  have h6e : ((6 ^ e : ℝ) : ℂ) ≠ 0 := by norm_num
  simp only [sepTerm, sepPairChartA, sepPairChartB, sepPairChartT, productQuadraticChart_atom,
    scaleQuadraticChartAmplitude_atom]
  field_simp

/-! ### Quantitative bounds for the separated terms -/

/-- The three coordinate blocks of `ℝ^(d+d+d)` as continuous linear maps. -/
noncomputable def tripleFstCLM (d : ℕ) : (Fin (d + d + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Fin.castAdd d (Fin.castAdd d l))

/-- Continuous linear projection onto the middle block of three coordinate blocks. -/
noncomputable def tripleSndCLM (d : ℕ) : (Fin (d + d + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Fin.castAdd d (Fin.natAdd d l))

/-- Continuous linear projection onto the last block of three coordinate blocks. -/
noncomputable def tripleThdCLM (d : ℕ) : (Fin (d + d + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Fin.natAdd (d + d) l)

theorem pi_proj_norm_le {n d : ℕ} (g : Fin d → Fin n) :
    ‖(ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (g l) :
      (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun l => norm_le_pi_norm x _

theorem tripleFstCLM_norm_le (d : ℕ) : ‖tripleFstCLM d‖ ≤ 1 := pi_proj_norm_le _

theorem tripleSndCLM_norm_le (d : ℕ) : ‖tripleSndCLM d‖ ≤ 1 := pi_proj_norm_le _

theorem tripleThdCLM_norm_le (d : ℕ) : ‖tripleThdCLM d‖ ≤ 1 := pi_proj_norm_le _

/-- Geometric bounds for the tensor Gevrey lattice partition. -/
theorem sepPartition_geomBound {d : ℕ} {Kρ : ℕ} (hK : 1 ≤ Kρ)
    (hder : ∀ n x, |iteratedDeriv n gevreyPartition x| ≤
      ((Kρ : ℝ) * ((n : ℝ) + 1)) ^ (Kρ * (n + 1)))
    (m : ℕ) (w : Fin d → ℝ) :
    GeomBound (sepPartition (d := d)) w 1 ((d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ)) m := by
  intro i hi
  rw [one_mul]
  have hunit : ∀ x, |gevreyPartition x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (gevreyPartition_nonneg x)]; exact gevreyPartition_le_one x
  exact chartCoordinateProduct_derivative_geometric (contDiff_infty.mpr gevreyPartition_contDiff)
    w (by positivity) (fun k hk x => gevrey_derivative_geometric gevreyPartition Kρ hK hunit
      (fun n y => by simpa using hder n y) m k (hk.trans hi) x)

/-- Geometric bounds for a chart amplitude from its complexity. -/
theorem quadraticChartAmplitude_geomBound {d c₀ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) (hc : 1 ≤ c₀) (m : ℕ) (w : Fin d → ℝ) :
    GeomBound A.amplitude w (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀)
      (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) m := by
  intro i hi
  have hH : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  refine (chart_cutoff_iteratedFDeriv_bound hA hc i w).trans ?_
  have him : (i + 1 : ℝ) ≤ m + 1 := by
    have : (i : ℝ) ≤ m := by exact_mod_cast hi
    linarith only [this]
  calc H ^ (2 * c₀ * (i + 1)) * (i + 1 : ℝ) ^ (c₀ * (i + 1)) ≤
        H ^ (2 * c₀ * (i + 1)) * (m + 1 : ℝ) ^ (c₀ * (i + 1)) := by gcongr
    _ = (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) * (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) ^ i := by
      rw [← pow_succ', mul_pow, ← pow_mul, ← pow_mul]

theorem sep_affine_norm_le {d : ℕ} (P Q : (Fin (d + d + d) → ℝ) →L[ℝ] (Fin d → ℝ))
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (s : ℝ) : ‖P + s • Q‖ ≤ 1 + |s| := by
  calc ‖P + s • Q‖ ≤ ‖P‖ + ‖s • Q‖ := norm_add_le _ _
    _ ≤ 1 + |s| * 1 := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add hP (mul_le_mul_of_nonneg_left hQ (abs_nonneg s))
    _ = 1 + |s| := by ring

private theorem absorbTwoPowerBounds {W a b : ℝ} (e : ℕ) (hW : 3 ≤ W)
    (ha : a ≤ W ^ e) (hb : b ≤ W ^ e) : a + 2 * b ≤ W ^ (e + 1) := by
  rw [pow_succ]
  calc a + 2 * b ≤ W ^ e + 2 * W ^ e :=
        add_le_add ha (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = W ^ e * 3 := by ring
    _ ≤ W ^ e * W := mul_le_mul_of_nonneg_left hW
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 3).trans hW) e)

/-- lem:separation, line 1407: explicit geometric derivative bounds of the coupled
amplitude, from the chart complexity, the plateau and the partition Gevrey bounds. -/
theorem sepCoupledVec_geomBound {d c₀ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) (hc : 1 ≤ c₀) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) {Kψ : ℕ} (hKψ : 1 ≤ Kψ)
    (hψd : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    {Kρ : ℕ} (hKρ : 1 ≤ Kρ)
    (hρd : ∀ n x, |iteratedDeriv n gevreyPartition x| ≤
      ((Kρ : ℝ) * ((n : ℝ) + 1)) ^ (Kρ * (n + 1)))
    (i a b : ℤ) (ki kb : Fin d → ℤ) (m : ℕ) (v : Fin (d + d + d) → ℝ) :
    GeomBound (sepCoupledVec A.amplitude ψ i a b ki kb) v (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀)
      ((1 + |((i - a : ℤ) : ℝ)|) * (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) +
        (1 + (1 + |((b - a : ℤ) : ℝ)|)) *
          ((d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3))) +
        3 * ((d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ))) m := by
  set G := H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀ with hG
  set RE := (d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3)) with hRE
  set RP := (d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ) with hRP
  have hH : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hG0 : 0 ≤ G := by positivity
  have hRE0 : 0 ≤ RE := by positivity
  have hRP0 : 0 ≤ RP := by positivity
  set! F1 := tripleFstCLM d
  set! F2 := tripleSndCLM d
  set! F3 := tripleThdCLM d
  set! Lχ := F1 + ((i - a : ℤ) : ℝ) • F3 with hLχ
  set! LE := (F1 - F2) + ((b - a : ℤ) : ℝ) • F3 with hLE
  have hLχn : ‖Lχ‖ ≤ 1 + |((i - a : ℤ) : ℝ)| :=
    sep_affine_norm_le _ _ (tripleFstCLM_norm_le d) (tripleThdCLM_norm_le d) _
  have hF12 : ‖F1 - F2‖ ≤ 1 + 1 :=
    (norm_sub_le _ _).trans (add_le_add (tripleFstCLM_norm_le d) (tripleSndCLM_norm_le d))
  have hLEn : ‖LE‖ ≤ 1 + (1 + |((b - a : ℤ) : ℝ)|) := by
    calc ‖LE‖ ≤ ‖F1 - F2‖ + ‖((b - a : ℤ) : ℝ) • F3‖ := norm_add_le _ _
      _ ≤ (1 + 1) + |((b - a : ℤ) : ℝ)| * 1 := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add hF12 (mul_le_mul_of_nonneg_left (tripleThdCLM_norm_le d)
            (abs_nonneg _))
      _ = _ := by ring
  have cχ := (quadraticChartAmplitude_geomBound hA hc m
    (Lχ v + -fun l => (ki l : ℝ))).comp_affine A.smooth Lχ (-fun l => (ki l : ℝ))
  have cE := (tensorCutoff_geomBound (d := d) hψ hψ1' hKψ hψd (r := 1 / 3) (by norm_num) m
    (LE v + -fun l => (kb l : ℝ))).comp_affine (tensorCutoff_smooth hψ _) LE
      (-fun l => (kb l : ℝ))
  have cP1 := (sepPartition_geomBound (d := d) hKρ hρd m (F1 v + 0)).comp_affine
    sepPartition_smooth F1 0
  have cP2 := (sepPartition_geomBound (d := d) hKρ hρd m (F2 v + 0)).comp_affine
    sepPartition_smooth F2 0
  have cP3 := (sepPartition_geomBound (d := d) hKρ hρd m (F3 v + 0)).comp_affine
    sepPartition_smooth F3 0
  have mχ := cχ.mono le_rfl (by positivity) (mul_le_mul_of_nonneg_right hLχn hG0)
  have mE := cE.mono le_rfl (by positivity) (mul_le_mul_of_nonneg_right hLEn hRE0)
  have m1 := cP1.mono le_rfl (by positivity)
    (mul_le_of_le_one_left hRP0 (tripleFstCLM_norm_le d))
  have m2 := cP2.mono le_rfl (by positivity)
    (mul_le_of_le_one_left hRP0 (tripleSndCLM_norm_le d))
  have m3 := cP3.mono le_rfl (by positivity)
    (mul_le_of_le_one_left hRP0 (tripleThdCLM_norm_le d))
  have sχ : ContDiff ℝ (⊤ : ℕ∞) (fun y => A.amplitude (Lχ y + -fun l => (ki l : ℝ))) :=
    A.smooth.comp (Lχ.contDiff.add contDiff_const)
  have sE : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => tensorCutoff ψ (1 / 3) (LE y + -fun l => (kb l : ℝ))) :=
    (tensorCutoff_smooth hψ _).comp (LE.contDiff.add contDiff_const)
  have s1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => sepPartition (F1 y + 0)) :=
    sepPartition_smooth.comp (F1.contDiff.add contDiff_const)
  have s2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => sepPartition (F2 y + 0)) :=
    sepPartition_smooth.comp (F2.contDiff.add contDiff_const)
  have s3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => sepPartition (F3 y + 0)) :=
    sepPartition_smooth.comp (F3.contDiff.add contDiff_const)
  have p1 := GeomBound.mul sχ sE (by positivity) mχ mE
  have p2 := GeomBound.mul (sχ.mul sE) s1 (by positivity) p1 m1
  have p3 := GeomBound.mul ((sχ.mul sE).mul s1) s2 (by positivity) p2 m2
  have p4 := GeomBound.mul (((sχ.mul sE).mul s1).mul s2) s3 (by positivity) p3 m3
  have hfun : sepCoupledVec A.amplitude ψ i a b ki kb = fun y =>
      A.amplitude (Lχ y + -fun l => (ki l : ℝ)) *
        tensorCutoff ψ (1 / 3) (LE y + -fun l => (kb l : ℝ)) *
        sepPartition (F1 y + 0) * sepPartition (F2 y + 0) * sepPartition (F3 y + 0) := by
    funext y
    simp only [sepCoupledVec, sepCoupledAmplitude, F1, F2, F3, add_zero]
    rfl
  rw [hfun]
  refine p4.mono (by simp [hG]) (by positivity) (le_of_eq ?_)
  ring

/-- The derivative budget `‖Dᵐ F‖ ≤ K Rᵐ` of the coupled amplitude (lem:separation). -/
noncomputable def sepDerivBudget (d c₀ Kψ Kρ : ℕ) (H : ℝ) (i a b : ℤ) (m : ℕ) : ℝ :=
  (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) *
    ((1 + |((i - a : ℤ) : ℝ)|) * (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) +
        (1 + (1 + |((b - a : ℤ) : ℝ)|)) *
          ((d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3))) +
        3 * ((d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ))) ^ m

theorem sepDerivBudget_nonneg {d c₀ Kψ Kρ : ℕ} {H : ℝ} (hH : 0 ≤ H) (i a b : ℤ) (m : ℕ) :
    0 ≤ sepDerivBudget d c₀ Kψ Kρ H i a b m := by
  unfold sepDerivBudget; positivity

/-- lem:separation, line 1407: coefficient envelope and shell masses of the
separation coefficients, with the integration-by-parts order exceeding the
Fourier dimension `3d` by `q + 1`. -/
theorem sepCoeff_shell_bounds {d c₀ : ℕ} (hd : 1 ≤ d) {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) (hc : 1 ≤ c₀) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hKψ : 1 ≤ Kψ)
    (hψd : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    {Kρ : ℕ} (hKρ : 1 ≤ Kρ)
    (hρd : ∀ n x, |iteratedDeriv n gevreyPartition x| ≤
      ((Kρ : ℝ) * ((n : ℝ) + 1)) ^ (Kρ * (n + 1)))
    (i a b : ℤ) (ki kb : Fin d → ℤ) :
    let Am : ℕ → ℝ := fun m => 4 ^ (d + d + d) * (3 ^ m * sepDerivBudget d c₀ Kψ Kρ H i a b m)
    Summable (fun p => ‖sepCoeff A.amplitude ψ i a b ki kb p‖) ∧
      (∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        (∑ p ∈ frequencyShell (d + d + d) T, ‖sepCoeff A.amplitude ψ i a b ki kb p‖) * T ^ q ≤
          7 ^ (d + d + d) * Am (q + (d + d + d) + 1) *
            Real.sqrt (d + d + d : ℕ) ^ (q + (d + d + d) + 1)) ∧
      (∑' p, ‖sepCoeff A.amplitude ψ i a b ki kb p‖) ≤
        Am 0 + 2 * (7 ^ (d + d + d) * Am ((d + d + d) + 1) *
          Real.sqrt (d + d + d : ℕ) ^ ((d + d + d) + 1)) := by
  intro Am
  have hH : 0 ≤ H := (quadraticChartComplexity_parameter_pos hA).le
  set F := sepCoupledVec A.amplitude ψ i a b ki kb
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := sepCoupledVec_smooth A.smooth hψ i a b ki kb
  have hFsupp : ∀ v, F v ≠ 0 → ∀ l, |v l| ≤ 3 / 4 := fun v hv l => sepCoupledVec_support hv l
  have hgeo (m : ℕ) (w) : ‖iteratedFDeriv ℝ m F w‖ ≤ sepDerivBudget d c₀ Kψ Kρ H i a b m :=
    sepCoupledVec_geomBound hA hc hψ hψ1' hKψ hψd hKρ hρd i a b ki kb m w m le_rfl
  have hA₀ : ∀ w, ‖F w‖ ≤ sepDerivBudget d c₀ Kψ Kρ H i a b 0 := fun w => by
    have := hgeo 0 w; rwa [norm_iteratedFDeriv_zero] at this
  have hexp (m : ℕ) (hm : d + d + d < m) := compact_cutoff_fourier_expansion
    (n := d + d + d) (m := m) (by omega) hm hFs (R := 3 / 4) (L := 3) (by norm_num)
    (by norm_num) (by norm_num) hFsupp (Φ := tensorCutoff ψ (3 / 4))
    (fun w hw => tensorCutoff_eq_one hψ1 (by norm_num) hw)
    (fun w hw l => (tensorCutoff_ne_zero_bound hψ0 (by norm_num) hw l).le.trans
      (by norm_num)) hA₀ (hgeo m)
  have hsum := (hexp (d + d + d + 1) (by omega)).2.1
  have h := fourier_coeff_envelope_bounds (sepCoeff A.amplitude ψ i a b ki kb) hsum (A := Am)
    (fun m => by have := sepDerivBudget_nonneg (d := d) (c₀ := c₀) (Kψ := Kψ) (Kρ := Kρ) hH i a b m
                 positivity)
    (fun v => by
      have := (hexp (d + d + d + 1) (by omega)).2.2.2 v
      simpa [Am, sepDerivBudget, sepCoeff] using this)
    (fun m hm v hv => by
      have := (hexp m hm).2.2.1 v hv
      simpa only [Am, mul_assoc, sepCoeff] using this)
  exact ⟨hsum, h.2.1, h.2.2⟩

/-- The coupled-amplitude derivative budget is a power of any common bound `W`
of its parameters, with exponent linear in the order. -/
theorem sepDerivBudget_le_pow {d c₀ Kψ Kρ m : ℕ} {H W : ℝ} {i a b : ℤ} (hW : 3 ≤ W)
    (hH1 : 1 ≤ H) (hHW : H ≤ W) (hKψW : (Kψ : ℝ) ≤ W) (hKρW : (Kρ : ℝ) ≤ W)
    (hmW : (m + 1 : ℝ) ≤ W) (hdW : (d : ℝ) ≤ W) (hia : 1 + |((i - a : ℤ) : ℝ)| ≤ W)
    (hba : 1 + (1 + |((b - a : ℤ) : ℝ)|) ≤ W) :
    PowLe W (3 * c₀ + (3 * c₀ + 4 * Kψ + 4 * Kρ + 5) * m)
      (sepDerivBudget d c₀ Kψ Kρ H i a b m) := by
  have hW1 : 1 ≤ W := by linarith
  have hW2 : 2 ≤ W := by linarith
  have hm0 : (0 : ℝ) ≤ m + 1 := by positivity
  have hG : PowLe W (2 * c₀ + c₀) (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) := by
    have h := ((PowLe.const (by linarith) hHW).pow (2 * c₀)).mul ((PowLe.const hm0 hmW).pow c₀)
    simpa only [one_mul] using h
  have hX (K : ℕ) (hKW : (K : ℝ) ≤ W) :
      PowLe W (2 * K + 2 * K) (((K : ℝ) * (m + 1 : ℝ)) ^ (2 * K)) := by
    have h := ((PowLe.const (Nat.cast_nonneg K) hKW).mul (PowLe.const hm0 hmW)).pow (2 * K)
    exact PowLe.of_le (by positivity) le_rfl (h.mono hW1 (by omega))
  have h1 : PowLe W (1 + (2 * c₀ + c₀)) ((1 + |((i - a : ℤ) : ℝ)|) *
      (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀)) :=
    (PowLe.const (by positivity) hia).mul hG
  have h2 : PowLe W (1 + (1 + (2 * Kψ + 2 * Kψ + 1))) ((1 + (1 + |((b - a : ℤ) : ℝ)|)) *
      ((d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3)))) := by
    have h3 : PowLe W (2 * Kψ + 2 * Kψ + 1) ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3)) := by
      have := (hX Kψ hKψW).mul (PowLe.const (by norm_num : (0 : ℝ) ≤ 3) hW)
      exact PowLe.of_le (by positivity) (le_of_eq (by ring)) this
    exact (PowLe.const (by positivity) hba).mul ((PowLe.const (Nat.cast_nonneg d) hdW).mul h3)
  have h3 : PowLe W (1 + (1 + (2 * Kρ + 2 * Kρ)))
      (3 * ((d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ))) :=
    (PowLe.const (by norm_num) hW).mul ((PowLe.const (Nat.cast_nonneg d) hdW).mul (hX Kρ hKρW))
  have hR : PowLe W (3 * c₀ + 4 * Kψ + 4 * Kρ + 5)
      ((1 + |((i - a : ℤ) : ℝ)|) * (H ^ (2 * c₀) * (m + 1 : ℝ) ^ c₀) +
        (1 + (1 + |((b - a : ℤ) : ℝ)|)) *
          ((d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / (1 / 3))) +
        3 * ((d : ℝ) * ((Kρ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kρ))) := by
    have h := PowLe.add hW2 (PowLe.add hW2 h1 h2) h3
    exact h.mono hW1 (by omega)
  have h := hG.mul (hR.pow m)
  unfold sepDerivBudget
  exact h.mono hW1 (by omega)

theorem pow_le_exp_mul_sq {W X c₁ c₂ : ℝ} {e : ℕ} (hW : 1 ≤ W)
    (hlog : Real.log W ≤ c₂ * X) (he : (e : ℝ) ≤ c₁ * X) :
    W ^ e ≤ Real.exp (c₁ * c₂ * X ^ 2) := by
  have hW0 : 0 < W := by linarith
  rw [← Real.exp_log (pow_pos hW0 e), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hl0 : 0 ≤ Real.log W := Real.log_nonneg hW
  have hX : 0 ≤ c₂ * X := hl0.trans hlog
  calc (e : ℝ) * Real.log W ≤ (c₁ * X) * (c₂ * X) :=
        mul_le_mul he hlog hl0 ((Nat.cast_nonneg e).trans he)
    _ = c₁ * c₂ * X ^ 2 := by ring

/-- lem:separation, line 1407: the shell masses of the separation coefficients
are at most `exp(D X^D) T^{-q}` and their total mass at most `exp(D X^D)`, where
`X = 1 + log H` and `D` depends only on the fixed Gevrey orders, `q` and the slot gaps. -/
theorem sepCoeff_budget (c₀ Kψ Kρ q S : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {d : ℕ} {H : ℝ} {i a b : ℤ}, 1 ≤ d → Real.exp 2 ≤ H →
      (d : ℝ) ≤ Real.log H → |((i - a : ℤ) : ℝ)| ≤ S → |((b - a : ℤ) : ℝ)| ≤ S →
      let Am : ℕ → ℝ := fun m => 4 ^ (d + d + d) * (3 ^ m * sepDerivBudget d c₀ Kψ Kρ H i a b m)
      7 ^ (d + d + d) * Am (q + (d + d + d) + 1) *
          Real.sqrt (d + d + d : ℕ) ^ (q + (d + d + d) + 1) ≤
        Real.exp (D * (1 + Real.log H) ^ D) ∧
      Am 0 + 2 * (7 ^ (d + d + d) * Am ((d + d + d) + 1) *
          Real.sqrt (d + d + d : ℕ) ^ ((d + d + d) + 1)) ≤
        Real.exp (D * (1 + Real.log H) ^ D) := by
  set f : ℝ := (q + S + Kψ + Kρ + 12 : ℝ) with hf
  set eR := 3 * c₀ + 4 * Kψ + 4 * Kρ + 5 with heR
  set c₁ : ℝ := (eR + 4) * (q + 5) + 3 * c₀ + 2 with hc₁
  set c₂ : ℝ := Real.log f + 1 with hc₂
  have hf1 : 12 ≤ f := by
    rw [hf]; have : (0 : ℝ) ≤ q + S + Kψ + Kρ := by positivity
    linarith
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ f); linarith
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨⌈3 * c₁ * c₂⌉₊ + 2, by omega, ?_⟩
  intro d H i a b hd hH hdH hia hba Am
  set X := 1 + Real.log H with hX
  have hH1 : 1 ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hH0 : 0 < H := by linarith
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hX1 : 1 ≤ X := by linarith
  have hdlt : (d : ℝ) ≤ H := hdH.trans (Real.log_le_self hH0.le)
  set! W := f * H with hW
  have hW3 : 12 ≤ W := hf1.trans (le_mul_of_one_le_right (by linarith) hH1)
  have hW1 : 1 ≤ W := by linarith
  have hlogW : Real.log W ≤ c₂ * X := by
    rw [hW, Real.log_mul (by linarith) hH0.ne', hc₂]
    have hlf := Real.log_nonneg (by linarith : (1 : ℝ) ≤ f)
    have := mul_nonneg hlf hlogH
    calc Real.log f + Real.log H ≤ Real.log f + Real.log f * Real.log H + 1 + Real.log H := by
          linarith
      _ = (Real.log f + 1) * X := by rw [hX]; ring
  have hfH (y : ℝ) (hy : y ≤ f) : y ≤ W := hy.trans (le_mul_of_one_le_right (by linarith) hH1)
  have hn3 : ((d + d + d : ℕ) : ℝ) ≤ 3 * H := by push_cast; linarith
  set n := d + d + d with hn
  have hn0 : ((n : ℕ) : ℝ) ≤ 3 * (X - 1) := by rw [hn]; push_cast; linarith
  have hsq : Real.sqrt (n : ℕ) ≤ W := by
    have h3W : 3 * H ≤ W := mul_le_mul_of_nonneg_right (by linarith) hH0.le
    have hWW : W ≤ W ^ 2 := by nlinarith only [hW3]
    have hWsq : (n : ℝ) ≤ W ^ 2 := by linarith
    calc Real.sqrt (n : ℕ) ≤ Real.sqrt (W ^ 2) := Real.sqrt_le_sqrt hWsq
      _ = W := Real.sqrt_sq (by linarith)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hKψ0 : (0 : ℝ) ≤ Kψ := Nat.cast_nonneg Kψ
  have hKρ0 : (0 : ℝ) ≤ Kρ := Nat.cast_nonneg Kρ
  have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
  have hS1 : 1 + |((i - a : ℤ) : ℝ)| ≤ W := hfH _ (by rw [hf]; linarith)
  have hS2 : 1 + (1 + |((b - a : ℤ) : ℝ)|) ≤ W := hfH _ (by rw [hf]; linarith)
  have hHW : H ≤ W := le_mul_of_one_le_left hH0.le (by linarith)
  have key : ∀ M : ℕ, (M + 1 : ℝ) ≤ W →
      PowLe W (n + (n + (M + (3 * c₀ + eR * M))) + M)
        (7 ^ n * Am M * Real.sqrt (n : ℕ) ^ M) := by
    intro M hM
    have hB := sepDerivBudget_le_pow (d := d) (c₀ := c₀) (Kψ := Kψ) (Kρ := Kρ) (m := M)
      (i := i) (a := a) (b := b) (by linarith) hH1 hHW
      (hfH _ (by rw [hf]; linarith)) (hfH _ (by rw [hf]; linarith)) hM
      (hdlt.trans hHW) hS1 hS2
    have h7 : PowLe W n ((7 : ℝ) ^ n) := by
      simpa only [one_mul] using (PowLe.const (by norm_num) (by linarith : (7 : ℝ) ≤ W)).pow n
    have h4 : PowLe W n ((4 : ℝ) ^ n) := by
      simpa only [one_mul] using (PowLe.const (by norm_num) (by linarith : (4 : ℝ) ≤ W)).pow n
    have h3 : PowLe W M ((3 : ℝ) ^ M) := by
      simpa only [one_mul] using (PowLe.const (by norm_num) (by linarith : (3 : ℝ) ≤ W)).pow M
    have hs : PowLe W M (Real.sqrt (n : ℕ) ^ M) := by
      simpa only [one_mul] using (PowLe.const (Real.sqrt_nonneg _) hsq).pow M
    exact (h7.mul (h4.mul (h3.mul hB))).mul hs
  have hnX : (n : ℝ) ≤ 3 * X := by linarith
  have hMW (M : ℕ) (hM : M ≤ q + n + 1) : (M + 1 : ℝ) ≤ W := by
    have : (M : ℝ) ≤ q + n + 1 := by exact_mod_cast hM
    have hq2 := mul_le_mul_of_nonneg_left hH1 (by linarith : (0 : ℝ) ≤ q + 2)
    have h1 : (M + 1 : ℝ) ≤ (q + 5) * H := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (by rw [hf]; linarith) hH0.le)
  have hE : ∀ N M e : ℕ, (N : ℝ) ≤ M → (M : ℝ) ≤ (q + 4) * X →
      ((e : ℝ) + 4) * (q + 4) + 3 * c₀ + 1 ≤ c₁ →
      ((N + (N + (M + (3 * c₀ + e * M))) + M + 1 : ℕ) : ℝ) ≤ c₁ * X := by
    intro N M e hNM hM' hec
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have hcX := mul_le_mul_of_nonneg_left hX1 hc0
    have heM := mul_le_mul_of_nonneg_left hM' (by linarith : (0 : ℝ) ≤ e + 4)
    push_cast
    calc (N : ℝ) + (N + (M + (3 * c₀ + e * M))) + M + 1 ≤ (e + 4) * M + 3 * c₀ + 1 := by
          linarith
      _ ≤ ((e + 4) * (q + 4) + 3 * c₀ + 1) * X := by linarith
      _ ≤ c₁ * X := mul_le_mul_of_nonneg_right hec (by linarith)
  have hec : ((eR : ℝ) + 4) * (q + 4) + 3 * c₀ + 1 ≤ c₁ := by
    rw [hc₁]
    have : (0 : ℝ) ≤ eR := Nat.cast_nonneg eR
    have := mul_le_mul_of_nonneg_left (show (q : ℝ) + 4 ≤ q + 5 by linarith)
      (show (0 : ℝ) ≤ eR + 4 by linarith)
    linarith
  have hMX (M : ℕ) (hM : M ≤ q + n + 1) : (M : ℝ) ≤ (q + 4) * X := by
    have : (M : ℝ) ≤ q + n + 1 := by exact_mod_cast hM
    have := mul_le_mul_of_nonneg_left hX1 hq0
    linarith
  have hDexp : Real.exp (c₁ * c₂ * X ^ 2) ≤ Real.exp (((⌈3 * c₁ * c₂⌉₊ + 2 : ℕ) : ℝ) *
      X ^ (⌈3 * c₁ * c₂⌉₊ + 2)) :=
    exp_poly_le hX1 (by omega) (by
      push_cast
      have := Nat.le_ceil (3 * c₁ * c₂)
      have : 0 ≤ c₁ * c₂ := mul_nonneg hc₁0 hc₂0
      linarith)
  constructor
  · have hk := key (q + n + 1) (hMW _ le_rfl)
    have hE1 := hE n (q + n + 1) eR (by push_cast; linarith) (hMX _ le_rfl) hec
    refine hk.2.trans ((pow_le_exp_mul_sq hW1 hlogW ?_).trans hDexp)
    push_cast at hE1 ⊢
    linarith
  · have hk := key (n + 1) (hMW _ (by omega))
    have hE2 := hE n (n + 1) eR (by push_cast; linarith) (hMX _ (by omega)) hec
    set E2 := n + (n + (n + 1 + (3 * c₀ + eR * (n + 1)))) + (n + 1) with hE2def
    have h0 : Am 0 ≤ W ^ E2 := by
      have hB := sepDerivBudget_le_pow (d := d) (c₀ := c₀) (Kψ := Kψ) (Kρ := Kρ) (m := 0)
        (i := i) (a := a) (b := b) (by linarith) hH1 hHW
        (hfH _ (by rw [hf]; linarith)) (hfH _ (by rw [hf]; linarith)) (by push_cast; linarith)
        (hdlt.trans hHW) hS1 hS2
      have h4 : PowLe W n ((4 : ℝ) ^ n) := by
        simpa only [one_mul] using (PowLe.const (by norm_num) (by linarith : (4 : ℝ) ≤ W)).pow n
      have h := h4.mul ((PowLe.one (W := W)).mul hB)
      have h' : PowLe W E2 (Am 0) := by
        refine (PowLe.of_le h.1 (le_of_eq ?_) h).mono hW1 (by omega)
        simp only [one_mul]
      exact h'.2
    have h3 : Am 0 + 2 * (7 ^ n * Am (n + 1) * Real.sqrt (n : ℕ) ^ (n + 1)) ≤ W ^ (E2 + 1) := by
      exact absorbTwoPowerBounds E2 (by linarith only [hW3]) h0 hk.2
    refine h3.trans ((pow_le_exp_mul_sq hW1 hlogW ?_).trans hDexp)
    exact_mod_cast hE2

theorem abs_rat_le_rationalHeight (q : ℚ) : |(q : ℝ)| ≤ rationalHeight q := by
  have h1 : (q : ℝ) = q.num / q.den := by rw [← Rat.cast_def]
  have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [h1, abs_div, abs_of_pos (show (0 : ℝ) < q.den by linarith)]
  calc |(q.num : ℝ)| / q.den ≤ |(q.num : ℝ)| := div_le_self (abs_nonneg _) hd1
    _ = (q.num.natAbs : ℝ) := by simp [Nat.cast_natAbs]
    _ ≤ rationalHeight q := by exact_mod_cast le_max_left _ _

/-- Heights of products of rationals. -/
theorem rationalHeight_mul_le (q r : ℚ) :
    (rationalHeight (q * r) : ℝ) ≤ 2 * ((rationalHeight q : ℝ) * rationalHeight r) ^ 2 := by
  have hD : 0 < q.den * r.den := Nat.mul_pos q.den_pos r.den_pos
  have h := rationalHeight_le_of_mul_int (q * r) hD ⟨q.num * r.num, by
    push_cast
    rw [show (q.den : ℚ) * r.den * (q * r) = (q.den * q) * (r.den * r) by ring,
      Rat.den_mul_eq_num, Rat.den_mul_eq_num]⟩
  have hq := abs_rat_le_rationalHeight q
  have hr := abs_rat_le_rationalHeight r
  have hqd : (q.den : ℝ) ≤ rationalHeight q := by exact_mod_cast le_max_right _ _
  have hrd : (r.den : ℝ) ≤ rationalHeight r := by exact_mod_cast le_max_right _ _
  have hq1 : (1 : ℝ) ≤ rationalHeight q := by
    have : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
    linarith
  have hr1 : (1 : ℝ) ≤ rationalHeight r := by
    have : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    linarith
  set P := (rationalHeight q : ℝ) * rationalHeight r
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hq1 hr1
  have hDP : ((q.den * r.den : ℕ) : ℝ) ≤ P := by
    push_cast; exact mul_le_mul hqd hrd (by positivity) (by linarith)
  have hqr : |((q * r : ℚ) : ℝ)| ≤ P := by
    push_cast; rw [abs_mul]; exact mul_le_mul hq hr (abs_nonneg _) (by linarith)
  calc (rationalHeight (q * r) : ℝ) ≤ ((q.den * r.den : ℕ) : ℝ) * (|((q * r : ℚ) : ℝ)| + 1) := h
    _ ≤ P * (P + 1) := mul_le_mul hDP (by linarith) (by positivity) (by linarith)
    _ ≤ 2 * P ^ 2 := by nlinarith only [hP1]

/-- Higher derivatives of a real affine function are bounded by powers of its linear part. -/
theorem norm_iteratedFDeriv_affine_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : E →L[ℝ] ℝ) (c : ℝ) (x : E) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y => Λ y + c) x‖ ≤ ‖Λ‖ ^ i := by
  have he : (fun y => Λ y + c) = (fun z : ℝ => z + c) ∘ Λ := rfl
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => z + c) := contDiff_id.add contDiff_const
  rw [he, Λ.iteratedFDeriv_comp_right hfc x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hsh : iteratedFDeriv ℝ i (fun z : ℝ => z + c) (Λ x) =
      iteratedFDeriv ℝ i (fun s : ℝ => s) (Λ x + c) :=
    congrFun (iteratedFDeriv_comp_add_right' (f := fun s : ℝ => s) i c) (Λ x)
  rw [hsh]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hid : ‖iteratedFDeriv ℝ i (fun s : ℝ => s) (Λ x + c)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hid' : (fun s : ℝ => s) = id := rfl
    rw [hid', iteratedDeriv_id]
    rcases i with _ | _ | i
    · omega
    · simp
    · simp only [show i + 1 + 1 ≠ 0 by omega, show i + 1 + 1 ≠ 1 by omega, ite_false, norm_zero]
      norm_num
  calc _ ≤ 1 * ‖Λ‖ ^ i := mul_le_mul_of_nonneg_right hid (by positivity)
    _ = _ := one_mul _

/-- The Fourier character of an affine phase. -/
theorem GeomBound.fourierChar_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : E →L[ℝ] ℝ) (c : ℝ) (x : E) (m : ℕ) :
    GeomBound (fun y => (Real.fourierChar (Λ y + c) : ℂ)) x 1
      ((m + 1) * (2 * Real.pi) * ‖Λ‖) m := by
  intro n hn
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i (fun t : ℝ => (Real.fourierChar t : ℂ))
      (Λ x + c)‖ ≤ (2 * Real.pi) ^ n := fun i hi => by
    rw [chart_fourierChar_derivative_norm]
    exact pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hi
  have hcomp := norm_iteratedFDeriv_comp_le (n := n) chart_fourierChar_smooth
    ((Λ.contDiff.add contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun y => Λ y + c))) (by simp) x hC
    (fun i hi _ => norm_iteratedFDeriv_affine_le Λ c x hi)
  change ‖iteratedFDeriv ℝ n (fun y => (Real.fourierChar (Λ y + c) : ℂ)) x‖ ≤ _ at hcomp
  have hfact : (n.factorial : ℝ) ≤ (m + 1 : ℝ) ^ n := by
    calc (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (by
          have : (n : ℝ) ≤ m := by exact_mod_cast hn
          linarith only [this]) _
  refine hcomp.trans ?_
  calc (n.factorial : ℝ) * (2 * Real.pi) ^ n * ‖Λ‖ ^ n ≤
        (m + 1 : ℝ) ^ n * (2 * Real.pi) ^ n * ‖Λ‖ ^ n := by gcongr
    _ = _ := by rw [one_mul, ← mul_pow, ← mul_pow]

/-- The linear modulation phase `w ↦ Σ_l p_l w_l / L` as a continuous linear functional. -/
noncomputable def modulationFunctional {d : ℕ} (L : ℝ) (p : Fin d → ℤ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ l, ((p l : ℝ) / L) • ContinuousLinearMap.proj l

theorem modulationFunctional_apply {d : ℕ} (L : ℝ) (p : Fin d → ℤ) (w : Fin d → ℝ) :
    modulationFunctional L p w = ∑ l, (p l : ℝ) * (w l / L) := by
  simp only [modulationFunctional, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro l _
  rw [ContinuousLinearMap.proj_apply]; ring

theorem modulationFunctional_norm_le {d : ℕ} {L : ℝ} (hL : 0 < L) (p : Fin d → ℤ) :
    ‖modulationFunctional L p‖ ≤ ∑ l, |(p l : ℝ)| / L := by
  unfold modulationFunctional
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hL]
  calc |(p l : ℝ)| / L * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) l‖ ≤
      |(p l : ℝ)| / L * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          fun x => by rw [one_mul, ContinuousLinearMap.proj_apply]; exact norm_le_pi_norm x l)
          (by positivity)
    _ = _ := mul_one _

/-- Geometric derivative bounds for a modulated plateau cutoff. -/
theorem modulatedCutoff_geomBound {d : ℕ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1' : ∀ x, |ψ x| ≤ 1) {Kψ : ℕ} (hK : 1 ≤ Kψ)
    (hder : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    {r : ℝ} (hr : 0 < r) (L : ℝ) (p : Fin d → ℤ) (m : ℕ) (w : Fin d → ℝ) :
    GeomBound (modulatedCutoff ψ r L p) w 1
      ((d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / r) +
        (m + 1) * (2 * Real.pi) * ‖modulationFunctional L p‖) m := by
  have h1 := tensorCutoff_geomBound (d := d) hψ hψ1' hK hder hr m w
  have h2 := GeomBound.fourierChar_affine (modulationFunctional L p) 0 w m
  have h := GeomBound.mul (tensorCutoff_smooth hψ r)
    (chart_fourierChar_smooth.comp ((modulationFunctional L p).contDiff.add contDiff_const))
    (by positivity) h1 h2
  have he : modulatedCutoff ψ r L p = fun y => tensorCutoff ψ r y *
      (Real.fourierChar (modulationFunctional L p y + 0) : ℂ) := by
    funext y; rw [modulatedCutoff, add_zero, modulationFunctional_apply]
  rw [he]
  rw [one_mul] at h
  exact h

theorem norm_coordinateWordDerivative_le {d m : ℕ} (χ : (Fin d → ℝ) → ℂ)
    (word : Fin m → Fin d) (z : Fin d → ℝ) :
    ‖coordinateWordDerivative m χ word z‖ ≤ ‖iteratedFDeriv ℝ m χ z‖ := by
  unfold coordinateWordDerivative
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  have : ∀ i, ‖(Pi.single (word i) (1 : ℝ) : Fin d → ℝ)‖ = 1 := fun i => by
    rw [Pi.norm_single, norm_one]
  simp [this]

/-- lem:separation, line 1407: complexity of a modulated-cutoff chart at Gevrey order
`2Kψ`. The parameter `W` must dominate the dimension, matrix heights, support and the
first-order derivative scale. -/
theorem modulatedChart_complexity {d : ℕ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hK : 1 ≤ Kψ)
    (hder : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    {r L : ℝ} (hr : 0 < r) (hL : 0 < L) (p : Fin d → ℤ) (θ : Fin d → ℝ) (lam β : ℝ)
    (M : Matrix (Fin d) (Fin d) ℚ) (hG : ContDiff ℝ (⊤ : ℕ∞) (modulatedCutoff ψ r L p))
    (hGc : HasCompactSupport (modulatedCutoff ψ r L p)) {W : ℝ} (hW : Real.exp 2 ≤ W)
    (hdW : (d : ℝ) ≤ Real.log W) (hMW : ∀ i j, (chartRationalHeight (M i j) : ℝ) ≤ W)
    (hrW : 2 * r ≤ W)
    (hBW : (d : ℝ) * (Kψ : ℝ) ^ (2 * Kψ) / r + 2 * Real.pi * ∑ l, |(p l : ℝ)| / L ≤ W) :
    QuadraticChartComplexity (2 * Kψ) W (mkQuadraticChart θ lam β M _ hG hGc) := by
  have hW1 : 1 ≤ W := by linarith [Real.add_one_le_exp (2 : ℝ)]
  refine ⟨hW, hdW, hMW, ?_, ?_⟩
  · intro z hz l
    have hz' : tensorCutoff ψ r z ≠ 0 := left_ne_zero_of_mul hz
    exact (tensorCutoff_ne_zero_bound hψ0 hr hz' l).le.trans hrW
  · intro m word z
    refine (norm_coordinateWordDerivative_le _ word z).trans ?_
    have h := modulatedCutoff_geomBound (d := d) hψ hψ1' hK hder hr L p m z m le_rfl
    refine h.trans ?_
    rw [one_mul]
    set B := (d : ℝ) * (Kψ : ℝ) ^ (2 * Kψ) / r + 2 * Real.pi * ∑ l, |(p l : ℝ)| / L with hB
    have hm1 : (1 : ℝ) ≤ m + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    have hmK : (m + 1 : ℝ) ≤ (m + 1) ^ (2 * Kψ) := le_self_pow₀ hm1 (by omega)
    have hΛ := modulationFunctional_norm_le hL p
    have hsum0 : 0 ≤ ∑ l, |(p l : ℝ)| / L := Finset.sum_nonneg fun l _ => by positivity
    have hR : (d : ℝ) * ((((Kψ : ℝ) * (m + 1 : ℝ)) ^ (2 * Kψ)) / r) +
        (m + 1) * (2 * Real.pi) * ‖modulationFunctional L p‖ ≤ (m + 1 : ℝ) ^ (2 * Kψ) * B := by
      rw [hB, mul_pow]
      have hpi : 0 ≤ 2 * Real.pi := by positivity
      have h1 : (m + 1) * (2 * Real.pi) * ‖modulationFunctional L p‖ ≤
          (m + 1 : ℝ) ^ (2 * Kψ) * (2 * Real.pi * ∑ l, |(p l : ℝ)| / L) := by
        calc (m + 1) * (2 * Real.pi) * ‖modulationFunctional L p‖ ≤
            (m + 1 : ℝ) * (2 * Real.pi * ∑ l, |(p l : ℝ)| / L) := by
              rw [mul_assoc]; gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_right hmK (by positivity)
      have h2 : (d : ℝ) * ((Kψ : ℝ) ^ (2 * Kψ) * (m + 1 : ℝ) ^ (2 * Kψ) / r) =
          (m + 1 : ℝ) ^ (2 * Kψ) * ((d : ℝ) * (Kψ : ℝ) ^ (2 * Kψ) / r) := by ring
      rw [h2, mul_add]
      linarith only [h1]
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    calc _ ≤ ((m + 1 : ℝ) ^ (2 * Kψ) * B) ^ m := pow_le_pow_left₀ (by positivity) hR m
      _ = (m + 1 : ℝ) ^ (2 * Kψ * m) * B ^ m := by rw [mul_pow, ← pow_mul]
      _ ≤ (m + 1 : ℝ) ^ (2 * Kψ * (m + 1)) * W ^ (2 * Kψ * (m + 1)) := by
          apply mul_le_mul (pow_le_pow_right₀ hm1 (by nlinarith only)) _ (by positivity)
            (by positivity)
          calc B ^ m ≤ W ^ m := pow_le_pow_left₀ hB0 hBW m
            _ ≤ _ := pow_le_pow_right₀ hW1 (by nlinarith only [hK])
      _ = _ := mul_comm _ _

theorem quadraticChartComplexity_order_mono {d c₀ c₁ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) (hc : c₀ ≤ c₁) : QuadraticChartComplexity c₁ H A where
  lower := hA.lower
  dimension := hA.dimension
  height := hA.height
  support := hA.support
  derivative := by
    intro m word z
    have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
    have hm1 : (1 : ℝ) ≤ m + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    refine (hA.derivative m word z).trans ?_
    exact mul_le_mul (pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right _ hc))
      (pow_le_pow_right₀ hm1 (Nat.mul_le_mul_right _ hc)) (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith) _)

/-- A one-dimensional chart whose atom is identically one, at a fixed Gevrey order. -/
theorem exists_unit_chart : ∃ (c : ℕ) (W₀ : ℝ) (E : QuadraticChartData 1), 1 ≤ c ∧
    Real.exp 2 ≤ W₀ ∧ (∀ y, quadraticChartAtom E y = 1) ∧
    ∀ W, W₀ ≤ W → QuadraticChartComplexity c W E := by
  obtain ⟨ψ, Kψ, hKψ, hψ, hψ1', hψ1, hψ0, hψd⟩ := exists_plateau_cutoff
  set E : QuadraticChartData 1 := mkQuadraticChart (fun _ => 0) 0 0 0
    (modulatedCutoff ψ (1 / 3) 1 0) (modulatedCutoff_smooth hψ _ _ _)
    (modulatedCutoff_hasCompactSupport hψ0 (by norm_num) _ _) with hE
  set W₀ : ℝ := Real.exp 2 + 3 * (Kψ : ℝ) ^ (2 * Kψ) + 1 with hW₀
  refine ⟨2 * Kψ, W₀, E, by omega, by
    rw [hW₀]; have : (0 : ℝ) ≤ 3 * (Kψ : ℝ) ^ (2 * Kψ) := by positivity
    linarith, ?_, ?_⟩
  · intro y
    rw [hE, mkQuadraticChart_atom]
    simp only [zero_mul, add_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
    rw [tsum_eq_single 0]
    · simp [modulatedCutoff, tensorCutoff, chartMatrixPhase, hψ1 0 (by norm_num)]
    · intro n hn
      have hn0 : n 0 ≠ 0 := fun h => hn (funext fun l => by
        rw [Subsingleton.elim l 0]; exact h)
      have h1 : (1 : ℝ) ≤ |(n 0 : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
      have hz : modulatedCutoff ψ (1 / 3) 1 0
          ((fun _ : Fin 1 => (0 : ℝ)) - fun l : Fin 1 => (n l : ℝ)) = 0 := by
        unfold modulatedCutoff tensorCutoff
        rw [Fin.prod_univ_one]
        have h3 : 2 ≤ |((fun _ : Fin 1 => (0 : ℝ)) - fun l : Fin 1 => (n l : ℝ)) 0 / (1 / 3)| := by
          simp only [Pi.sub_apply, zero_sub, abs_div, abs_neg]
          norm_num
          linarith
        rw [hψ0 _ h3]; simp
      rw [hz, zero_mul]
  · intro W hW
    have hK0 : (0 : ℝ) ≤ 3 * (Kψ : ℝ) ^ (2 * Kψ) := by positivity
    have hW2 : Real.exp 2 ≤ W := by
      have : Real.exp 2 ≤ W₀ := by rw [hW₀]; linarith
      linarith
    exact modulatedChart_complexity hψ hψ1' hψ0 hKψ hψd (by norm_num) one_pos 0 _ 0 0 0 _ _ hW2
      (by
        have := Real.log_le_log (Real.exp_pos 2) hW2
        rw [Real.log_exp] at this; push_cast; linarith)
      (fun i j => by simp [chartRationalHeight]; linarith [Real.add_one_le_exp (2 : ℝ)])
      (by linarith [Real.add_one_le_exp (2 : ℝ)])
      (by
        simp only [Nat.cast_one, one_mul, Pi.zero_apply, Int.cast_zero, abs_zero, zero_div,
          Finset.sum_const_zero, mul_zero, add_zero]
        rw [div_le_iff₀ (by norm_num)]
        have : (0 : ℝ) ≤ (Kψ : ℝ) ^ (2 * Kψ) := by positivity
        nlinarith [Real.add_one_le_exp (2 : ℝ)])

/-- Padding a chart to positive dimension without changing its atom. -/
theorem exists_pad_chart : ∃ (c : ℕ) (W₀ : ℝ), 1 ≤ c ∧ Real.exp 2 ≤ W₀ ∧
    ∀ {d c₀ : ℕ} {H : ℝ} (A : QuadraticChartData d), QuadraticChartComplexity c₀ H A →
      1 ≤ c₀ → ∃ A' : QuadraticChartData (d + 1), (∀ y, quadraticChartAtom A' y =
        quadraticChartAtom A y) ∧
        QuadraticChartComplexity (max c₀ c) (max H W₀ ^ 6) A' ∧
        (IsBoundedQuadraticChart A → IsBoundedQuadraticChart A') := by
  obtain ⟨c, W₀, E, hc, hW₀, hE1, hEc⟩ := exists_unit_chart
  refine ⟨c, W₀, hc, hW₀, ?_⟩
  intro d c₀ H A hA hc₀
  refine ⟨productQuadraticChart A E, fun y => by rw [productQuadraticChart_atom, hE1, mul_one],
    ?_, fun hb y => by rw [productQuadraticChart_atom, hE1, mul_one]; exact hb y⟩
  have hA' : QuadraticChartComplexity (max c₀ c) (max H W₀) A :=
    quadraticChartComplexity_order_mono (quadraticChartComplexity_mono hA (le_max_left _ _))
      (le_max_left _ _)
  have hE' : QuadraticChartComplexity (max c₀ c) (max H W₀) E :=
    quadraticChartComplexity_order_mono (hEc _ (le_max_right _ _)) (le_max_right _ _)
  exact productQuadraticChart_complexity hA' hE' (le_trans hc₀ (le_max_left _ _))

/-- The fixed constant in the factor-chart complexity bound of lem:separation. -/
noncomputable def sepFactorConst (Kψ : ℕ) : ℝ := 2 * (Kψ : ℝ) ^ (2 * Kψ) + 3

/-- lem:separation, line 1407: a factor chart `ψ_p` with matrix `q C` has complexity
at most `W` at Gevrey order `2Kψ` whenever `W ≥ K Q² H² (1 + Σ_l |p_l|)`, where `Q`
bounds the height of the fixed rational `q`. -/
theorem sepFactor_complexity {d c₀ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hK : 1 ≤ Kψ)
    (hder : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    (q : ℚ) {Q : ℝ} (hQ1 : 1 ≤ Q) (hq : (rationalHeight q : ℝ) ≤ Q) (p : Fin d → ℤ)
    (θ : Fin d → ℝ) (lam β : ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) (modulatedCutoff ψ (3 / 4) 3 p))
    (hGc : HasCompactSupport (modulatedCutoff ψ (3 / 4) 3 p)) {W : ℝ}
    (hW : sepFactorConst Kψ * Q ^ 2 * H ^ 2 * (1 + ∑ l, |(p l : ℝ)|) ≤ W) :
    QuadraticChartComplexity (2 * Kψ) W (mkQuadraticChart θ lam β (q • A.matrix) _ hG hGc) := by
  have hH : Real.exp 2 ≤ H := hA.lower
  have hH1 : 1 ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hdH : (d : ℝ) ≤ H := hA.dimension.trans (Real.log_le_self (by linarith))
  have hKc : 5 ≤ sepFactorConst Kψ := by
    unfold sepFactorConst
    have : (1 : ℝ) ≤ (Kψ : ℝ) ^ (2 * Kψ) := one_le_pow₀ (by exact_mod_cast hK)
    linarith
  have hS0 : 0 ≤ ∑ l, |(p l : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set P := 1 + ∑ l, |(p l : ℝ)| with hP
  have hP1 : 1 ≤ P := by linarith
  have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
  have hH2 : H ≤ H ^ 2 := le_self_pow₀ hH1 (by norm_num)
  have hbase : sepFactorConst Kψ * Q ^ 2 * H ^ 2 ≤ W := by
    refine le_trans ?_ hW
    exact le_mul_of_one_le_right (by positivity) hP1
  have hHW : H ≤ W := by
    refine le_trans ?_ hbase
    calc H ≤ H ^ 2 := hH2
      _ = 1 * 1 * H ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  refine modulatedChart_complexity hψ hψ1' hψ0 hK hder (by norm_num) (by norm_num) p θ lam β
    (q • A.matrix) hG hGc (hH.trans hHW) (hA.dimension.trans (Real.log_le_log (by linarith) hHW))
    ?_ ?_ ?_
  · intro i j
    have h1 := rationalHeight_mul_le q (A.matrix i j)
    have h2 : (rationalHeight (A.matrix i j) : ℝ) ≤ H := hA.height i j
    have h3 : (chartRationalHeight ((q • A.matrix) i j) : ℝ) =
        rationalHeight (q * A.matrix i j) := by
      rw [Matrix.smul_apply, smul_eq_mul]; rfl
    rw [h3]
    refine h1.trans (le_trans ?_ hbase)
    have h4 : (rationalHeight q : ℝ) * rationalHeight (A.matrix i j) ≤ Q * H :=
      mul_le_mul hq h2 (Nat.cast_nonneg _) (by linarith)
    calc 2 * ((rationalHeight q : ℝ) * rationalHeight (A.matrix i j)) ^ 2 ≤ 2 * (Q * H) ^ 2 := by
          gcongr
      _ ≤ sepFactorConst Kψ * Q ^ 2 * H ^ 2 := by
          rw [mul_pow, ← mul_assoc]; gcongr; linarith
  · have : (3 : ℝ) ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  · refine le_trans ?_ hW
    have hpi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have hsum : 2 * Real.pi * ∑ l, |(p l : ℝ)| / 3 ≤ 3 * ∑ l, |(p l : ℝ)| := by
      rw [← Finset.sum_div, mul_div_assoc']
      rw [div_le_iff₀ (by norm_num)]
      nlinarith only [hS0, hpi]
    have hKp : (0 : ℝ) ≤ (Kψ : ℝ) ^ (2 * Kψ) := by positivity
    have h1 : (d : ℝ) * (Kψ : ℝ) ^ (2 * Kψ) / (3 / 4) ≤ 2 * (Kψ : ℝ) ^ (2 * Kψ) * H := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith only [hdH, hKp]
    have hQH : H ≤ Q ^ 2 * H ^ 2 := by nlinarith only [hH1, hQ2]
    have hQH0 : 0 ≤ Q ^ 2 * H ^ 2 := by positivity
    calc (d : ℝ) * (Kψ : ℝ) ^ (2 * Kψ) / (3 / 4) + 2 * Real.pi * ∑ l, |(p l : ℝ)| / 3 ≤
        2 * (Kψ : ℝ) ^ (2 * Kψ) * (Q ^ 2 * H ^ 2) + 3 * (Q ^ 2 * H ^ 2) * ∑ l, |(p l : ℝ)| := by
          have := mul_le_mul_of_nonneg_left hQH (by positivity : (0 : ℝ) ≤ 2 * (Kψ : ℝ) ^ (2 * Kψ))
          have h5 : 3 * ∑ l, |(p l : ℝ)| ≤ 3 * (Q ^ 2 * H ^ 2) * ∑ l, |(p l : ℝ)| := by
            have h6 : (1 : ℝ) ≤ Q ^ 2 * H ^ 2 := by nlinarith only [hH1, hQ2]
            nlinarith only [hH1, hS0, hQH]
          linarith only [hsum, h1, this, h5]
      _ ≤ sepFactorConst Kψ * Q ^ 2 * H ^ 2 * P := by
          unfold sepFactorConst
          have e : (2 * (Kψ : ℝ) ^ (2 * Kψ) + 3) * Q ^ 2 * H ^ 2 * P -
              (2 * (Kψ : ℝ) ^ (2 * Kψ) * (Q ^ 2 * H ^ 2) +
                3 * (Q ^ 2 * H ^ 2) * ∑ l, |(p l : ℝ)|) =
              2 * (Kψ : ℝ) ^ (2 * Kψ) * (Q ^ 2 * H ^ 2) * ∑ l, |(p l : ℝ)| +
                3 * (Q ^ 2 * H ^ 2) := by rw [hP]; ring
          have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKp) hQH0) hS0
          linarith

/-- A bound for the heights of the fixed separation rationals `α_a, α_b, S`. -/
noncomputable def sepQ (i a b : ℤ) : ℝ :=
  1 + |((i - b : ℤ) : ℝ)| + |((a - i : ℤ) : ℝ)| + |((b - a : ℤ) : ℝ)| +
    |(((i - a) * (i - b) : ℤ) : ℝ)|

theorem one_le_sepQ (i a b : ℤ) : 1 ≤ sepQ i a b := by
  unfold sepQ; have := abs_nonneg ((i - b : ℤ) : ℝ); have := abs_nonneg ((a - i : ℤ) : ℝ)
  have := abs_nonneg ((b - a : ℤ) : ℝ); have := abs_nonneg ((((i - a) * (i - b) : ℤ) : ℝ))
  linarith

theorem rationalHeight_int_div_le_sepQ {u v : ℤ} {Q : ℝ}
    (hQ : 1 + |(u : ℝ)| + |(v : ℝ)| ≤ Q) :
    (rationalHeight (-((u : ℚ) / v)) : ℝ) ≤ Q := by
  rw [rationalHeight_neg]
  have hu := abs_nonneg (u : ℝ)
  have hv := abs_nonneg (v : ℝ)
  by_cases hv0 : v = 0
  · subst hv0
    simp only [Int.cast_zero, div_zero]
    have : rationalHeight (0 : ℚ) = 1 := by simp [rationalHeight]
    rw [this]; push_cast; linarith
  · have h := rationalHeight_div_int_le u v hv0
    have h' : (rationalHeight ((u : ℚ) / v) : ℝ) ≤ (u.natAbs : ℝ) + v.natAbs := by
      have : (rationalHeight ((u : ℚ) / v) : ℝ) ≤ ((max u.natAbs v.natAbs : ℕ) : ℝ) := by
        exact_mod_cast h
      refine this.trans ?_
      push_cast
      exact max_le (by linarith [(Nat.cast_nonneg v.natAbs : (0 : ℝ) ≤ v.natAbs)])
        (by linarith [(Nat.cast_nonneg u.natAbs : (0 : ℝ) ≤ u.natAbs)])
    simp only [Nat.cast_natAbs, Int.cast_abs] at h'
    linarith

theorem sep_heights_le (i a b : ℤ) :
    (rationalHeight (-((i - b) / (b - a) : ℚ)) : ℝ) ≤ sepQ i a b ∧
      (rationalHeight (-((a - i) / (b - a) : ℚ)) : ℝ) ≤ sepQ i a b ∧
      (rationalHeight ((i - a) * (i - b) : ℚ) : ℝ) ≤ sepQ i a b := by
  have h1 := abs_nonneg ((i - b : ℤ) : ℝ)
  have h2 := abs_nonneg ((a - i : ℤ) : ℝ)
  have h3 := abs_nonneg ((b - a : ℤ) : ℝ)
  have h4 := abs_nonneg ((((i - a) * (i - b) : ℤ) : ℝ))
  refine ⟨?_, ?_, ?_⟩
  · have := rationalHeight_int_div_le_sepQ (u := i - b) (v := b - a) (Q := sepQ i a b)
      (by unfold sepQ; linarith)
    simpa only [Int.cast_sub] using this
  · have := rationalHeight_int_div_le_sepQ (u := a - i) (v := b - a) (Q := sepQ i a b)
      (by unfold sepQ; linarith)
    simpa only [Int.cast_sub] using this
  · have := rationalHeight_intCast_bound ((i - a) * (i - b)) (one_le_sepQ i a b)
      (by unfold sepQ; linarith)
    simpa only [Int.cast_mul, Int.cast_sub] using this

theorem sum_abs_triple_le {d : ℕ} (p : Fin (d + d + d) → ℤ) :
    ∑ l, |((tripleFst p l : ℤ) : ℝ)| ≤ ∑ l, |(p l : ℝ)| ∧
      ∑ l, |((tripleSnd p l : ℤ) : ℝ)| ≤ ∑ l, |(p l : ℝ)| ∧
      ∑ l, |((tripleThd p l : ℤ) : ℝ)| ≤ ∑ l, |(p l : ℝ)| := by
  have h := sum_tripleVec (fun l => |(p l : ℝ)|)
  have h1 : 0 ≤ ∑ l : Fin d, |(p (Fin.castAdd d (Fin.castAdd d l)) : ℝ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ l : Fin d, |(p (Fin.castAdd d (Fin.natAdd d l)) : ℝ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 : 0 ≤ ∑ l : Fin d, |(p (Fin.natAdd (d + d) l) : ℝ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨?_, ?_, ?_⟩ <;> simp only [tripleFst, tripleSnd, tripleThd] <;> linarith

/-- lem:separation, line 1407: complexity of the three factor charts of one separated atom. -/
theorem sepCharts_complexity {d c₀ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hK : 1 ≤ Kψ)
    (hder : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    (i a b : ℤ) (ki kb : Fin d → ℤ) (p : Fin (d + d + d) → ℤ) {W : ℝ}
    (hW : sepFactorConst Kψ * sepQ i a b ^ 2 * H ^ 2 * (1 + ∑ l, |(p l : ℝ)|) ≤ W) :
    QuadraticChartComplexity (2 * Kψ) W (sepChartA A hψ hψ0 i a b ki (tripleFst p)) ∧
      QuadraticChartComplexity (2 * Kψ) W (sepChartB A hψ hψ0 i a b ki kb (tripleSnd p)) ∧
      QuadraticChartComplexity (2 * Kψ) W (sepChartT A hψ hψ0 i a b (tripleThd p)) := by
  obtain ⟨hqa, hqb, hqt⟩ := sep_heights_le i a b
  obtain ⟨s1, s2, s3⟩ := sum_abs_triple_le p
  have hQ1 := one_le_sepQ i a b
  have hc : 0 ≤ sepFactorConst Kψ * sepQ i a b ^ 2 * H ^ 2 := by
    unfold sepFactorConst; positivity
  refine ⟨?_, ?_, ?_⟩
  · exact sepFactor_complexity hA hψ hψ1' hψ0 hK hder _ hQ1 hqa _ _ _ _ _ _
      (le_trans (mul_le_mul_of_nonneg_left (by linarith) hc) hW)
  · exact sepFactor_complexity hA hψ hψ1' hψ0 hK hder _ hQ1 hqb _ _ _ _ _ _
      (le_trans (mul_le_mul_of_nonneg_left (by linarith) hc) hW)
  · exact sepFactor_complexity hA hψ hψ1' hψ0 hK hder _ hQ1 hqt _ _ _ _ _ _
      (le_trans (mul_le_mul_of_nonneg_left (by linarith) hc) hW)

/-- lem:separation, line 1407: the normalized bounded factors of a separated pair have
complexity at most `W⁶` at the fixed Gevrey order `2Kψ`, where
`W ≥ K Q² H² (1 + Σ|p_l| + Σ|p'_l|)`. -/
theorem sepPairCharts_complexity {d e c₀ c₀' : ℕ} {H : ℝ} {A : QuadraticChartData d}
    {A' : QuadraticChartData e} (hA : QuadraticChartComplexity c₀ H A)
    (hA' : QuadraticChartComplexity c₀' H A') {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hK : 1 ≤ Kψ)
    (hder : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    (i k a b : ℤ) (ki kb : Fin d → ℤ) (kj kc : Fin e → ℤ)
    (p : Fin (d + d + d) → ℤ) (p' : Fin (e + e + e) → ℤ) {W : ℝ}
    (hW : sepFactorConst Kψ * max (sepQ i a b) (sepQ k a b) ^ 2 * H ^ 2 *
      (1 + ∑ l, |(p l : ℝ)| + ∑ l, |(p' l : ℝ)|) ≤ W) :
    QuadraticChartComplexity (2 * Kψ) (W ^ 6) (sepPairChartA A A' hψ hψ0 i k a b ki kj p p') ∧
      QuadraticChartComplexity (2 * Kψ) (W ^ 6)
        (sepPairChartB A A' hψ hψ0 i k a b ki kb kj kc p p') ∧
      QuadraticChartComplexity (2 * Kψ) (W ^ 6) (sepPairChartT A A' hψ hψ0 i k a b p p') := by
  have hQ := one_le_sepQ i a b
  have hS0 : 0 ≤ ∑ l, |(p l : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS0' : 0 ≤ ∑ l, |(p' l : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKc : 0 ≤ sepFactorConst Kψ := by unfold sepFactorConst; positivity
  have hW1 : sepFactorConst Kψ * sepQ i a b ^ 2 * H ^ 2 * (1 + ∑ l, |(p l : ℝ)|) ≤ W := by
    refine le_trans ?_ hW
    have hq : sepQ i a b ^ 2 ≤ max (sepQ i a b) (sepQ k a b) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hKc)
      (by positivity)) (by linarith) (by linarith) (by positivity)
  have hW2 : sepFactorConst Kψ * sepQ k a b ^ 2 * H ^ 2 * (1 + ∑ l, |(p' l : ℝ)|) ≤ W := by
    refine le_trans ?_ hW
    have hq : sepQ k a b ^ 2 ≤ max (sepQ i a b) (sepQ k a b) ^ 2 :=
      pow_le_pow_left₀ (by linarith [one_le_sepQ k a b]) (le_max_right _ _) 2
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hKc)
      (by positivity)) (by linarith) (by linarith) (by positivity)
  obtain ⟨a1, b1, t1⟩ := sepCharts_complexity hA hψ hψ1' hψ0 hK hder i a b ki kb p hW1
  obtain ⟨a2, b2, t2⟩ := sepCharts_complexity hA' hψ hψ1' hψ0 hK hder k a b kj kc p' hW2
  have hs (d' : ℕ) : ‖(((6 ^ d' : ℝ) : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hc : 1 ≤ 2 * Kψ := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact productQuadraticChart_complexity (scaleQuadraticChartAmplitude_complexity a1 (hs d))
      (scaleQuadraticChartAmplitude_complexity a2 (hs e)) hc
  · exact productQuadraticChart_complexity (scaleQuadraticChartAmplitude_complexity b1 (hs d))
      (scaleQuadraticChartAmplitude_complexity b2 (hs e)) hc
  · exact productQuadraticChart_complexity (scaleQuadraticChartAmplitude_complexity t1 (hs d))
      (scaleQuadraticChartAmplitude_complexity t2 (hs e)) hc

/-! ### Separated forms: the kernel expansion and the Fourier supremum bound -/

theorem iteratedDeriv_comp_affine {φ : ℝ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (m : ℕ)
    (L c t : ℝ) :
    iteratedDeriv m (fun s => φ (L * s + c)) t = L ^ m • iteratedDeriv m φ (L * t + c) := by
  have h := iteratedDeriv_comp_const_smul (n := m) (f := fun y => φ (y + c))
    ((hφ.comp (contDiff_id.add contDiff_const)).of_le (by simp)) L
  have h2 := congrFun h t
  rw [h2, iteratedDeriv_comp_add_const]

theorem contDiff_insertNth_line {d : ℕ} (i : Fin (d + 1)) (y : Fin d → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Fin.insertNth i s y : Fin (d + 1) → ℝ)) := by
  apply contDiff_pi.mpr; intro k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k, rfl⟩
  · simp only [Fin.insertNth_apply_same]; exact contDiff_id
  · simp only [Fin.insertNth_apply_succAbove]; exact contDiff_const

/-- Coordinate-line derivatives of a cube periodization. -/
theorem cubePeriodization_line_le {d : ℕ} {F : (Fin (d + 1) → ℝ) → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R L : ℝ} (hL : 0 < L) (hRL : 4 * R ≤ L)
    (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R) (m : ℕ) {A : ℝ}
    (hA : ∀ (i : Fin (d + 1)) (x : Fin d → ℝ) (t : ℝ),
      ‖iteratedDeriv m (fun s => F (i.insertNth s x)) t‖ ≤ A)
    (i : Fin (d + 1)) (x : Fin d → ℝ) (t : ℝ) :
    ‖iteratedDeriv m (fun s => cubePeriodization F L (i.insertNth s x)) t‖ ≤
      4 ^ (d + 1) * (L ^ m * A) := by
  set x₀ : Fin (d + 1) → ℝ := Fin.insertNth i t x
  set B := chartLatticeBox (1 / 2) (-x₀)
  have hcont : Continuous (fun s : ℝ => (Fin.insertNth i s x : Fin (d + 1) → ℝ)) := by
    fun_prop
  have hev : (fun s => cubePeriodization F L (i.insertNth s x)) =ᶠ[nhds t]
      fun s => ∑ j ∈ B, F (L • (i.insertNth s x + fun l => (j l : ℝ))) :=
    (cubePeriodization_eventuallyEq F hL hRL hsupp x₀).comp_tendsto (hcont.tendsto t)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA i x 0)
  have hid (j : Fin (d + 1) → ℤ) (s : ℝ) :
      L • (i.insertNth s x + fun l => (j l : ℝ)) =
        i.insertNth (L * s + L * j i) (fun k => L * (x k + j (i.succAbove k))) := by
    funext k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k, rfl⟩
    · simp [mul_add]
    · simp [mul_add]
  have hterm (j : Fin (d + 1) → ℤ) :
      ‖iteratedDeriv m (fun s => F (L • (i.insertNth s x + fun l => (j l : ℝ)))) t‖ ≤
        L ^ m * A := by
    simp_rw [hid j]
    have hφ : ContDiff ℝ (⊤ : ℕ∞)
        (fun s => F (i.insertNth s (fun k => L * (x k + j (i.succAbove k))))) :=
      hF.comp (contDiff_insertNth_line i _)
    rw [iteratedDeriv_comp_affine hφ, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (hA _ _ _) (by positivity)
  have hs (j : Fin (d + 1) → ℤ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun s => F (L • (i.insertNth s x + fun l => (j l : ℝ)))) := by
    simp_rw [hid j]
    exact hF.comp ((contDiff_insertNth_line i _).comp
      ((contDiff_const.mul contDiff_id).add contDiff_const))
  rw [hev.iteratedDeriv_eq m,
    iteratedDeriv_fun_sum (fun j _ => ((hs j).of_le (by simp)).contDiffAt)]
  calc _ ≤ ∑ j ∈ B, ‖iteratedDeriv m (fun s => F (L • (i.insertNth s x +
          fun l => (j l : ℝ)))) t‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ B, L ^ m * A := Finset.sum_le_sum fun j _ => hterm j
    _ = (B.card : ℝ) * (L ^ m * A) := by simp
    _ ≤ 4 ^ (d + 1) * (L ^ m * A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := chartLatticeBox_card_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (-x₀)
        norm_num at this ⊢
        exact this

/-- The admissible kernel at unit scale, centred at the cell midpoint. -/
noncomputable def kernelUnitRescale (a₀ r : ℝ) (w : ℝ × ℝ → ℂ) (u : Fin 2 → ℝ) : ℂ :=
  w (a₀ + r / 2 + r * u 0, r * u 1)

/-- The derivative constant of the admissible kernel class at order `m`. -/
noncomputable def kernelDerivBound (κ : LocalKernelClass) (m : ℕ) : ℝ :=
  (κ.derivativeConstant * ((m : ℕ) + 2 : ℝ)) ^ (κ.derivativeConstant * ((m : ℕ) + 2 : ℝ))

theorem kernelDerivBound_nonneg (κ : LocalKernelClass) (m : ℕ) : 0 ≤ kernelDerivBound κ m :=
  Real.rpow_nonneg (by have := κ.one_le_derivativeConstant; positivity) _

/-- The uniform absolute Fourier mass of admissible kernels. -/
noncomputable def kernelFourierConst (κ : LocalKernelClass) : ℝ :=
  4 ^ 2 * (16 ^ 0 * kernelDerivBound κ 0) +
    2 * (7 ^ 2 * (4 ^ 2 * (16 ^ 3 * kernelDerivBound κ 3)) * Real.sqrt (2 : ℕ) ^ 3)

theorem kernelUnitRescale_support {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {u : Fin 2 → ℝ}
    (hu : kernelUnitRescale a₀ r w u ≠ 0) (l : Fin 2) : |u l| ≤ 4 := by
  have h0 := hw.support _ hu 0
  have h1 := hw.support _ hu 1
  simp only [realProgressionCoordinate, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    zero_mul, add_zero, one_mul] at h0 h1
  have hm := mul_nonneg κ.margin_pos.le hr.le
  have hu0 : |u 0| ≤ 1 / 2 := by
    rw [abs_le]; constructor
    · by_contra h; push Not at h
      have : r * u 0 < r * (-(1 / 2)) := mul_lt_mul_of_pos_left h hr
      linarith [h0.1]
    · by_contra h; push Not at h
      have : r * (1 / 2) < r * u 0 := mul_lt_mul_of_pos_left h hr
      linarith [h0.2]
  have hu1 : |u 1| ≤ 1 := by
    have hb : |r * u 0| ≤ r / 2 := by
      rw [abs_mul, abs_of_pos hr]; nlinarith only [hr, hu0]
    rw [abs_le] at hb ⊢
    constructor
    · by_contra h; push Not at h
      have : r * u 1 < r * (-1) := mul_lt_mul_of_pos_left h hr
      linarith [h1.1, hb.1, hb.2]
    · by_contra h; push Not at h
      have : r * 1 < r * u 1 := mul_lt_mul_of_pos_left h hr
      linarith [h1.2, hb.1, hb.2]
  fin_cases l
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith

theorem kernelUnitRescale_line_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (m : ℕ) (i : Fin 2)
    (x : Fin 1 → ℝ) (t : ℝ) :
    ‖iteratedDeriv m (fun s => kernelUnitRescale a₀ r w (i.insertNth s x)) t‖ ≤
      kernelDerivBound κ m := by
  have hrm : r ^ m * r⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
  fin_cases i
  · have he : (fun s => kernelUnitRescale a₀ r w ((0 : Fin 2).insertNth s x)) =
        fun s => (fun y => w (y, r * x 0)) (r * s + (a₀ + r / 2)) := by
      funext s; simp [kernelUnitRescale, add_comm]
    simp only [Fin.zero_eta]
    rw [he, iteratedDeriv_comp_affine (φ := fun y => w (y, r * x 0))
      (hw.smooth.comp (contDiff_id.prodMk contDiff_const)), norm_smul,
      Real.norm_eq_abs, abs_pow, abs_of_pos hr]
    have hb := hw.derivativeBound m 0 (r * t + (a₀ + r / 2), r * x 0)
    simp only [localKernelPartial, iteratedDeriv_zero, add_zero] at hb
    calc r ^ m * ‖iteratedDeriv m (fun y => w (y, r * x 0)) (r * t + (a₀ + r / 2))‖ ≤
        r ^ m * (r⁻¹ ^ m * kernelDerivBound κ m) :=
          mul_le_mul_of_nonneg_left (by simpa [kernelDerivBound] using hb) (by positivity)
      _ = kernelDerivBound κ m := by rw [← mul_assoc, hrm, one_mul]
  · have he : (fun s => kernelUnitRescale a₀ r w ((1 : Fin 2).insertNth s x)) =
        fun s => (fun y => w (a₀ + r / 2 + r * x 0, y)) (r * s + 0) := by
      funext s
      have h0 : (Fin.insertNth 1 s x : Fin 2 → ℝ) 0 = x 0 := rfl
      simp [kernelUnitRescale, h0]
    simp only [Fin.mk_one]
    rw [he, iteratedDeriv_comp_affine (φ := fun y => w (a₀ + r / 2 + r * x 0, y))
      (hw.smooth.comp (contDiff_const.prodMk contDiff_id)), norm_smul,
      Real.norm_eq_abs, abs_pow, abs_of_pos hr]
    have hb := hw.derivativeBound 0 m (a₀ + r / 2 + r * x 0, r * t + 0)
    simp only [localKernelPartial, iteratedDeriv_zero, zero_add] at hb
    calc r ^ m * ‖iteratedDeriv m (fun y => w (a₀ + r / 2 + r * x 0, y)) (r * t + 0)‖ ≤
        r ^ m * (r⁻¹ ^ m * kernelDerivBound κ m) :=
          mul_le_mul_of_nonneg_left (by simpa [kernelDerivBound] using hb) (by positivity)
      _ = kernelDerivBound κ m := by rw [← mul_assoc, hrm, one_mul]

/-- lem:separation, line 1409: an admissible kernel has an absolutely convergent
two-variable Fourier expansion near its cell, with absolute coefficient mass
bounded uniformly over the kernel class. Only pure `x`- and `t`-derivatives enter. -/
theorem admissibleKernel_fourier_expansion {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) :
    let c := periodicFourierCoeff (cubePeriodization (kernelUnitRescale a₀ r w) 16)
    Summable (fun v => ‖c v‖) ∧ (∑' v, ‖c v‖) ≤ kernelFourierConst κ ∧
      ∀ x t : ℝ, |x - (a₀ + r / 2)| ≤ 8 * r → |t| ≤ 8 * r →
        HasSum (fun v => c v * (Real.fourierChar ((v 0 : ℝ) * ((x - (a₀ + r / 2)) / r / 16) +
          (v 1 : ℝ) * (t / r / 16)) : ℂ)) (w (x, t)) := by
  intro c
  set F := kernelUnitRescale a₀ r w with hFdef
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := hw.smooth.comp (by fun_prop)
  have hsupp : ∀ u, F u ≠ 0 → ∀ l, |u l| ≤ 4 := fun u hu l => kernelUnitRescale_support hr hw hu l
  set f := cubePeriodization F 16 with hf
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := cubePeriodization_smooth hFs (by norm_num) (by norm_num) hsupp
  set A : ℕ → ℝ := fun m => 4 ^ 2 * (16 ^ m * kernelDerivBound κ m) with hA
  have hline (m : ℕ) (i : Fin 2) (x : Fin 1 → ℝ) (t : ℝ) :
      ‖iteratedDeriv m (fun s => f (i.insertNth s x)) t‖ ≤ A m :=
    cubePeriodization_line_le hFs (by norm_num) (by norm_num) hsupp m
      (fun i x t => kernelUnitRescale_line_le hr hw m i x t) i x t
  have hB (y : Fin 2 → ℝ) : ‖f y‖ ≤ A 0 := by
    have h := cubePeriodization_iteratedFDeriv_le hFs (R := 4) (L := 16) (by norm_num)
      (by norm_num) hsupp 0 (A := kernelDerivBound κ 0) (fun u => by
        rw [norm_iteratedFDeriv_zero]
        change ‖w (a₀ + r / 2 + r * u 0, r * u 1)‖ ≤ _
        have hb := hw.derivativeBound 0 0 (a₀ + r / 2 + r * u 0, r * u 1)
        simpa [localKernelPartial, kernelDerivBound, kernelUnitRescale] using hb) y
    rw [norm_iteratedFDeriv_zero] at h
    simpa [hA] using h
  have hexp (m : ℕ) (hm : 1 + 1 < m) := periodic_fourier_expansion (d := 1) hm f hfs.continuous
    (cubePeriodization_periodic F 16)
    (fun i x => (hfs.comp (contDiff_insertNth_line i x)).of_le (by exact_mod_cast le_top))
    (hline m) hB
  obtain ⟨hsum1, hsumm, -, -⟩ := hexp 3 (by norm_num)
  have henv := fourier_coeff_envelope_bounds (n := 2) c hsumm (A := A)
    (fun m => by have := kernelDerivBound_nonneg κ m; positivity)
    (fun v => (hexp 3 (by norm_num)).2.2.2 v)
    (fun m hm v hv => by
      have := (hexp m (by omega)).2.2.1 v hv
      have h2 : Real.sqrt ((1 : ℕ) + 1 : ℝ) = Real.sqrt ((2 : ℕ) : ℝ) := by norm_num
      rw [h2] at this
      exact this)
  refine ⟨hsumm, henv.2.2.trans (le_of_eq (by simp [kernelFourierConst, hA])), ?_⟩
  intro x t hx ht
  set! u : Fin 2 → ℝ := ![(x - (a₀ + r / 2)) / r, t / r] with hu
  have hu8 : ∀ l, |u l| ≤ 2 * 4 := by
    intro l
    fin_cases l
    · simp only [hu, Fin.zero_eta, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]; linarith
    · simp only [hu, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]; linarith
  have hFu : F u = w (x, t) := by
    simp only [hFdef, kernelUnitRescale, hu, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have e1 : a₀ + r / 2 + r * ((x - (a₀ + r / 2)) / r) = x := by field_simp; ring
    have e2 : r * (t / r) = t := by field_simp
    rw [e1, e2]
  have heq := cubePeriodization_eq F (R := 4) (L := 16) (by norm_num) (by norm_num) (by norm_num)
    hsupp u hu8
  have h := hsum1 (fun l => u l / 16)
  have heq' : f (fun l => u l / 16) = w (x, t) := by rw [hf, heq, hFu]
  rw [heq'] at h
  have hc : periodicFourierCoeff f = c := rfl
  rw [hc] at h
  convert h using 2 with v
  simp [Fin.sum_univ_two, hu]

theorem integrable_correlation_norm {A B : ℝ → ℂ} (hA : Integrable A) (hB : Integrable B) :
    Integrable (fun s => ∫ y, ‖A y‖ * ‖B (y + s)‖) := by
  have hmp := measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)
  have hemb : MeasurableEmbedding (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) :=
    (MeasurableEquiv.shearAddRight ℝ).measurableEmbedding
  have h0 : Integrable (fun z : ℝ × ℝ => ‖A z.1‖ * ‖B z.2‖) (volume.prod volume) :=
    hA.norm.mul_prod hB.norm
  have h1 : Integrable ((fun z : ℝ × ℝ => ‖A z.1‖ * ‖B z.2‖) ∘
      (fun z : ℝ × ℝ => (z.1, z.1 + z.2))) (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).mpr h0
  exact h1.integral_prod_right

theorem integral_progression_section {A B : ℝ → ℂ} (a b t : ℝ) :
    ∫ x, A (x + a * t) * B (x + b * t) = ∫ y, A y * B (y + (b - a) * t) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => A y * B (y + (b - a) * t)) (a * t)
  rw [← h]
  congr 1; funext x; congr 2; ring

/-- Integrability of a pair of `L¹ ∩ L²` inputs along two distinct progression slots. -/
theorem integrable_progression_pair {A B : ℝ → ℂ} (hAm : Measurable A) (hBm : Measurable B)
    (hA1 : Integrable A) (hA2 : MemLp A 2) (hB1 : Integrable B) (hB2 : MemLp B 2)
    {a b : ℝ} (hab : a ≠ b) :
    Integrable (fun z : ℝ × ℝ => A (z.1 + a * z.2) * B (z.1 + b * z.2)) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => A (z.1 + a * z.2) * B (z.1 + b * z.2))
      (volume.prod volume) :=
    ((hAm.comp (measurable_fst.add (measurable_const.mul measurable_snd))).mul
      (hBm.comp (measurable_fst.add (measurable_const.mul measurable_snd)))).aestronglyMeasurable
  change Integrable _ (volume.prod volume)
  refine (integrable_prod_iff' hmeas).mpr ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
  · have h1 : MemLp (fun x => A (x + a * t)) 2 :=
      hA2.comp_measurePreserving (measurePreserving_add_right volume (a * t))
    have h2 : MemLp (fun x => B (x + b * t)) 2 :=
      hB2.comp_measurePreserving (measurePreserving_add_right volume (b * t))
    exact h1.integrable_mul h2
  · have hc := (integrable_correlation_norm hA1 hB1).comp_mul_left' (sub_ne_zero.mpr hab.symm)
    refine hc.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [norm_mul]
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y => ‖A y‖ * ‖B (y + (b - a) * t)‖) (a * t)
    rw [← this]
    congr 1; funext x
    have : x + a * t + (b - a) * t = x + b * t := by ring
    rw [this]

/-- Fubini and the change of variables to a correlation along two progression slots. -/
theorem integral_progression_pair_eq {A B K : ℝ → ℂ} (hAm : Measurable A) (hBm : Measurable B)
    (hA1 : Integrable A) (hA2 : MemLp A 2) (hB1 : Integrable B) (hB2 : MemLp B 2)
    (hKm : Measurable K) (hK1 : ∀ t, ‖K t‖ ≤ 1) {a b : ℝ} (hab : a ≠ b) :
    ∫ z : ℝ × ℝ, A (z.1 + a * z.2) * B (z.1 + b * z.2) * K z.2 =
      ∫ s, ((|b - a|⁻¹ : ℝ) : ℂ) * K (s / (b - a)) * ∫ u, A u * B (u + s) := by
  have hI := integrable_progression_pair hAm hBm hA1 hA2 hB1 hB2 hab
  have hI' : Integrable (fun z : ℝ × ℝ => A (z.1 + a * z.2) * B (z.1 + b * z.2) * K z.2)
      (volume.prod volume) := by
    have := hI.bdd_mul (c := 1) (hKm.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hK1 z.2)
    exact this.congr (Filter.Eventually.of_forall fun z => by
      simp only [Function.comp]; ring)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  change ∫ z : ℝ × ℝ, _ ∂(volume.prod volume) = _
  rw [integral_prod_symm _ hI']
  have e1 : ∀ t, ∫ x, A (x + a * t) * B (x + b * t) * K t =
      K t * ∫ u, A u * B (u + (b - a) * t) := fun t => by
    rw [← integral_progression_section, ← integral_const_mul]
    congr 1; funext x; ring
  simp_rw [e1]
  have h := Measure.integral_comp_mul_left
    (fun s => K (s / (b - a)) * ∫ u, A u * B (u + s)) (b - a)
  simp only [mul_div_cancel_left₀ _ hba] at h
  rw [h, Complex.real_smul, ← integral_const_mul]
  congr 1; funext s
  have e2 : (∫ u, A u * B (u + s)) = ∫ u, A u * B (s + u) := by
    congr 1; funext u; rw [add_comm]
  rw [e2, abs_inv, div_eq_inv_mul]
  push_cast; ring

/-- lem:separation, line 1409: one modulated separated term is bounded by `r A_r` times
the `L²` norms of its two inputs supported in the cell. -/
theorem separated_term_bound {A B : ℝ → ℂ} (hAm : Measurable A) (hBm : Measurable B)
    (hA1 : Integrable A) (hA2 : MemLp A 2) (hB1 : Integrable B) (hB2 : MemLp B 2)
    {a₀ r : ℝ} (hr : 0 < r) (hAs : ∀ y, A y ≠ 0 → y ∈ Set.Icc a₀ (a₀ + r))
    (hBs : ∀ y, B y ≠ 0 → y ∈ Set.Icc a₀ (a₀ + r)) {a b : ℝ} (hab1 : 1 ≤ |b - a|)
    {Q : ℝ → ℂ} (hQm : Measurable Q) (hQ1 : ∀ t, ‖Q t‖ ≤ 1) {ζ : ℝ → ℝ}
    (hζi : Integrable ζ) (hζ1 : ∀ u, |u| ≤ 1 → ζ u = 1) {M : ℝ}
    (hM : ∀ ξ, ‖∫ u, Q (r * u) * (ζ u : ℂ) * (Real.fourierChar (-(ξ * u)) : ℂ)‖ ≤ M)
    (γ : ℝ) :
    ‖∫ z : ℝ × ℝ, A (z.1 + a * z.2) * B (z.1 + b * z.2) *
        ((Real.fourierChar (γ * z.2) : ℂ) * Q z.2)‖ ≤
      r * M * Real.sqrt (∫ x, ‖A x‖ ^ 2) * Real.sqrt (∫ x, ‖B x‖ ^ 2) := by
  have hab : a ≠ b := by
    intro h; rw [h, sub_self, abs_zero] at hab1; norm_num at hab1
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hba0 : 0 < |b - a| := abs_pos.mpr hba
  have hchm : Measurable (fun t : ℝ => (Real.fourierChar t : ℂ)) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).measurable
  set! K : ℝ → ℂ := fun t => (Real.fourierChar (γ * t) : ℂ) * Q t with hKdef
  have hKm : Measurable K := (hchm.comp (measurable_const.mul measurable_id)).mul hQm
  have hK1 : ∀ t, ‖K t‖ ≤ 1 := fun t => by
    simp only [hKdef, norm_mul, Circle.norm_coe, one_mul]; exact hQ1 t
  rw [integral_progression_pair_eq hAm hBm hA1 hA2 hB1 hB2 hKm hK1 hab]
  -- insert the cutoff `ζ(s / ((b - a) r))`
  set! K₂ : ℝ → ℂ := fun s => ((|b - a|⁻¹ : ℝ) : ℂ) * K (s / (b - a)) *
    (ζ (s / ((b - a) * r)) : ℂ) with hK₂
  have hcut : ∀ s, ((|b - a|⁻¹ : ℝ) : ℂ) * K (s / (b - a)) * ∫ u, A u * B (u + s) =
      K₂ s * ∫ u, A u * B (u + s) := by
    intro s
    by_cases hC : ∫ u, A u * B (u + s) = 0
    · rw [hC, mul_zero, mul_zero]
    obtain ⟨u, hu⟩ : ∃ u, A u * B (u + s) ≠ 0 := by
      by_contra h; push Not at h; exact hC (by simp [h])
    have h1 := hAs u (left_ne_zero_of_mul hu)
    have h2 := hBs (u + s) (right_ne_zero_of_mul hu)
    have hs : |s| ≤ r := by
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hz : ζ (s / ((b - a) * r)) = 1 := by
      apply hζ1
      rw [abs_div, abs_mul, abs_of_pos hr, div_le_one (by positivity)]
      calc |s| ≤ r := hs
        _ = 1 * r := (one_mul r).symm
        _ ≤ |b - a| * r := mul_le_mul_of_nonneg_right hab1 hr.le
    simp [hK₂, hz]
  simp_rw [hcut]
  -- the kernel `K₂` is integrable with Fourier transform at most `r M`
  have hc' : (b - a) * r ≠ 0 := mul_ne_zero hba hr.ne'
  have hK₂i : Integrable K₂ := by
    have hζc : Integrable (fun s => ζ (s / ((b - a) * r))) := by
      have := hζi.comp_mul_left' (inv_ne_zero hc')
      simpa [div_eq_inv_mul] using this
    have h0 : Integrable (fun s => ((ζ (s / ((b - a) * r)) : ℝ) : ℂ)) := hζc.ofReal
    have h1 := h0.bdd_mul (c := |b - a|⁻¹ * 1)
      (f := fun s => ((|b - a|⁻¹ : ℝ) : ℂ) * K (s / (b - a)))
      ((measurable_const.mul (hKm.comp (measurable_id.div_const _))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hba0)]
        exact mul_le_mul_of_nonneg_left (hK1 _) (by positivity))
    exact h1
  have hF : ∀ ξ, ‖𝓕 K₂ ξ‖ ≤ r * M := by
    intro ξ
    rw [Real.fourier_real_eq]
    have h := Measure.integral_comp_mul_left
      (fun s => (Real.fourierChar (-(s * ξ)) : ℂ) • K₂ s) ((b - a) * r)
    have hinv : |((b - a) * r)⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hc')
    have h' : ∫ s, (Real.fourierChar (-(s * ξ)) : ℂ) • K₂ s =
        |(b - a) * r| • ∫ u, (Real.fourierChar (-((b - a) * r * u * ξ)) : ℂ) •
          K₂ ((b - a) * r * u) := by
      rw [h, smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hc'), one_smul]
    change ‖∫ s, (Real.fourierChar (-(s * ξ)) : ℂ) • K₂ s‖ ≤ r * M
    rw [h']
    have e : ∀ u, (Real.fourierChar (-((b - a) * r * u * ξ)) : ℂ) • K₂ ((b - a) * r * u) =
        ((|b - a|⁻¹ : ℝ) : ℂ) * (Q (r * u) * (ζ u : ℂ) *
          (Real.fourierChar (-((ξ * (b - a) * r - γ * r) * u)) : ℂ)) := by
      intro u
      have hu1 : (b - a) * r * u / (b - a) = r * u := by field_simp
      have hu2 : (b - a) * r * u / ((b - a) * r) = u := by field_simp
      simp only [hK₂, hKdef, smul_eq_mul, hu1, hu2]
      have : (Real.fourierChar (-((b - a) * r * u * ξ)) : ℂ) *
          (Real.fourierChar (γ * (r * u)) : ℂ) =
          (Real.fourierChar (-((ξ * (b - a) * r - γ * r) * u)) : ℂ) := by
        rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
      rw [← this]; ring
    simp_rw [e]
    have hpos : ‖|(b - a) * r|‖ = |b - a| * r := by
      rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos hr]
    rw [integral_const_mul, norm_smul, hpos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hba0)]
    have hb := hM (ξ * (b - a) * r - γ * r)
    calc |b - a| * r * (|b - a|⁻¹ * ‖∫ u, Q (r * u) * (ζ u : ℂ) *
          (Real.fourierChar (-((ξ * (b - a) * r - γ * r) * u)) : ℂ)‖) =
        r * ‖∫ u, Q (r * u) * (ζ u : ℂ) *
          (Real.fourierChar (-((ξ * (b - a) * r - γ * r) * u)) : ℂ)‖ := by
          rw [mul_comm |b - a| r, mul_assoc, ← mul_assoc |b - a|, mul_inv_cancel₀ hba0.ne',
            one_mul]
      _ ≤ r * M := mul_le_mul_of_nonneg_left hb hr.le
  have := norm_integral_correlation_le hA1 hA2 hB1 hB2 hK₂i hF
  simpa only [mul_assoc] using this

/-- lem:separation, line 1409: the separated single-scale form `r⁻² ∫ w Q(t) F_a(y_a) F_b(y_b)`
in two distinct slots is bounded by `C A_r` times the normalized `L²(I)` norms, where
`A_r ≤ M` bounds `sup_ξ |∫ Q(ru) ζ(u) e(-ξu) du|` and `C` depends only on the kernel class. -/
theorem separated_form_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (a b : Fin 4) (hab : a ≠ b) {Q : ℝ → ℂ}
    (hQm : Measurable Q) (hQ1 : ∀ t, ‖Q t‖ ≤ 1) {ζ : ℝ → ℝ}
    (hζi : Integrable ζ) (hζ1 : ∀ u, |u| ≤ 1 → ζ u = 1) {M : ℝ}
    (hM : ∀ ξ, ‖∫ u, Q (r * u) * (ζ u : ℂ) * (Real.fourierChar (-(ξ * u)) : ℂ)‖ ≤ M)
    {Fa Fb : ℝ → ℂ} (hFam : Measurable Fa) (hFbm : Measurable Fb)
    (hFa2 : MemLp Fa 2 (volume.restrict (Set.Icc a₀ (a₀ + r))))
    (hFb2 : MemLp Fb 2 (volume.restrict (Set.Icc a₀ (a₀ + r)))) :
    ‖(r : ℂ)⁻¹ ^ 2 * ∫ z : ℝ × ℝ, w z * Q z.2 * Fa (realProgressionCoordinate a z) *
        Fb (realProgressionCoordinate b z)‖ ≤
      kernelFourierConst κ * M *
        Real.sqrt (r⁻¹ * ∫ x in Set.Icc a₀ (a₀ + r), ‖Fa x‖ ^ 2) *
        Real.sqrt (r⁻¹ * ∫ x in Set.Icc a₀ (a₀ + r), ‖Fb x‖ ^ 2) := by
  set I := Set.Icc a₀ (a₀ + r) with hI
  have hIm : MeasurableSet I := measurableSet_Icc
  set Ga := I.indicator Fa with hGa
  set Gb := I.indicator Fb with hGb
  have hGam : Measurable Ga := hFam.indicator hIm
  have hGbm : Measurable Gb := hFbm.indicator hIm
  have hGa2 : MemLp Ga 2 := (memLp_indicator_iff_restrict hIm.nullMeasurableSet).mpr hFa2
  have hGb2 : MemLp Gb 2 := (memLp_indicator_iff_restrict hIm.nullMeasurableSet).mpr hFb2
  have hGa1 : Integrable Ga := (integrable_indicator_iff hIm).mpr (hFa2.integrable one_le_two)
  have hGb1 : Integrable Gb := (integrable_indicator_iff hIm).mpr (hFb2.integrable one_le_two)
  have hGas : ∀ y, Ga y ≠ 0 → y ∈ I := fun y hy => by
    by_contra h; exact hy (Set.indicator_of_notMem h _)
  have hGbs : ∀ y, Gb y ≠ 0 → y ∈ I := fun y hy => by
    by_contra h; exact hy (Set.indicator_of_notMem h _)
  have hsq (F : ℝ → ℂ) : ∫ x, ‖I.indicator F x‖ ^ 2 = ∫ x in I, ‖F x‖ ^ 2 := by
    rw [← integral_indicator hIm]
    congr 1; funext x
    by_cases hx : x ∈ I
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- slot positions
  set! ar : ℝ := ((a : ℕ) : ℝ) with har
  set! br : ℝ := ((b : ℕ) : ℝ) with hbr
  have har3 : |ar| ≤ 3 := by
    rw [har, abs_of_nonneg (Nat.cast_nonneg _)]
    have := a.isLt; exact_mod_cast (by omega : (a : ℕ) ≤ 3)
  have hab1 : 1 ≤ |br - ar| := by
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (1 : ℝ) ≤ br - ar := by
        rw [har, hbr]; have : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast h
        linarith
      rw [abs_of_pos (by linarith)]; exact this
    · have : (1 : ℝ) ≤ ar - br := by
        rw [har, hbr]; have : ((b : ℕ) : ℝ) + 1 ≤ (a : ℕ) := by exact_mod_cast h
        linarith
      rw [abs_sub_comm, abs_of_pos (by linarith)]; exact this
  have hcoord (j : Fin 4) (z : ℝ × ℝ) :
      realProgressionCoordinate j z = z.1 + ((j : ℕ) : ℝ) * z.2 := rfl
  -- restrict the inputs to the cell
  have hrestr : ∀ z : ℝ × ℝ, w z * Q z.2 * Fa (realProgressionCoordinate a z) *
      Fb (realProgressionCoordinate b z) =
      w z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) := by
    intro z
    by_cases hz : w z = 0
    · simp [hz]
    have hmem (j : Fin 4) : realProgressionCoordinate j z ∈ I := by
      have h := hw.support z hz j
      have hm := mul_nonneg κ.margin_pos.le hr.le
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [hGa, hGb, ← hcoord a, ← hcoord b, Set.indicator_of_mem (hmem a),
      Set.indicator_of_mem (hmem b)]
  simp_rw [hrestr]
  -- the kernel expansion
  obtain ⟨hcs, hct, hexp⟩ := admissibleKernel_fourier_expansion hr hw
  set c := periodicFourierCoeff (cubePeriodization (kernelUnitRescale a₀ r w) 16) with hc
  set c₀ := a₀ + r / 2 with hc₀
  set! E : (Fin 2 → ℤ) → ℝ × ℝ → ℂ := fun v z =>
    (Real.fourierChar ((v 0 : ℝ) * ((z.1 - c₀) / r / 16) + (v 1 : ℝ) * (z.2 / r / 16)) : ℂ)
    with hE
  set! Ψ : (Fin 2 → ℤ) → ℝ × ℝ → ℂ := fun v z =>
    E v z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) with hΨ
  have hpt : ∀ z : ℝ × ℝ, HasSum (fun v => c v * Ψ v z)
      (w z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)) := by
    intro z
    by_cases h0 : Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) = 0
    · have hz : ∀ v, c v * Ψ v z = 0 := fun v => by
        simp only [hΨ]
        rw [show E v z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) =
          E v z * Q z.2 * (Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)) by ring, h0]
        simp
      have : w z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) = 0 := by
        rw [show w z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) =
          w z * Q z.2 * (Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)) by ring, h0, mul_zero]
      rw [this]
      simp_rw [hz]
      exact hasSum_zero
    have ha := hGas _ (left_ne_zero_of_mul h0)
    have hb := hGbs _ (right_ne_zero_of_mul h0)
    have ht : |z.2| ≤ r := by
      have hd : |(br - ar) * z.2| ≤ r := by
        have : (br - ar) * z.2 = (z.1 + br * z.2) - (z.1 + ar * z.2) := by ring
        rw [this, abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      rw [abs_mul] at hd
      calc |z.2| = 1 * |z.2| := (one_mul _).symm
        _ ≤ |br - ar| * |z.2| := mul_le_mul_of_nonneg_right hab1 (abs_nonneg _)
        _ ≤ r := hd
    have hx : |z.1 - c₀| ≤ 8 * r := by
      have h1 : |ar * z.2| ≤ 3 * r := by
        rw [abs_mul]; exact mul_le_mul har3 ht (abs_nonneg _) (by norm_num)
      have : z.1 - c₀ = (z.1 + ar * z.2 - c₀) - ar * z.2 := by ring
      rw [this]
      have h2 : |z.1 + ar * z.2 - c₀| ≤ r := by
        rw [abs_le, hc₀]; constructor <;> linarith [ha.1, ha.2]
      calc _ ≤ |z.1 + ar * z.2 - c₀| + |ar * z.2| := abs_sub _ _
        _ ≤ r + 3 * r := add_le_add h2 h1
        _ ≤ 8 * r := by linarith
    have h := (hexp z.1 z.2 hx (by linarith)).mul_right
      (Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2))
    convert h using 1
    · funext v; simp only [hΨ, hE]; ring
    · ring
  -- integrability and interchange of the expansion with the integral
  have habr : ar ≠ br := by
    intro h; rw [h, sub_self, abs_zero] at hab1; norm_num at hab1
  have hpair := integrable_progression_pair hGam hGbm hGa1 hGa2 hGb1 hGb2 habr
  have hchm : Continuous (fun t : ℝ => (Real.fourierChar t : ℂ)) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  have hEQm (v : Fin 2 → ℤ) : Measurable (fun z : ℝ × ℝ => E v z * Q z.2) :=
    (hchm.measurable.comp (by fun_prop)).mul (hQm.comp measurable_snd)
  have hEQ1 (v : Fin 2 → ℤ) (z : ℝ × ℝ) : ‖E v z * Q z.2‖ ≤ 1 := by
    simp only [hE, norm_mul, Circle.norm_coe, one_mul]; exact hQ1 _
  have hΨi (v : Fin 2 → ℤ) : Integrable (Ψ v) := by
    have := hpair.bdd_mul (c := 1) (hEQm v).aestronglyMeasurable
      (Filter.Eventually.of_forall (hEQ1 v))
    exact this.congr (Filter.Eventually.of_forall fun z => by simp only [hΨ]; ring)
  set! P := ∫ z : ℝ × ℝ, ‖Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)‖ with hP
  have hΨn (v : Fin 2 → ℤ) : ∫ z, ‖c v * Ψ v z‖ ≤ ‖c v‖ * P := by
    rw [hP, ← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hpair.norm.const_mul _)
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [hΨ]
    rw [show c v * (E v z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)) =
      c v * (E v z * Q z.2) * (Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2)) by ring,
      norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (hEQ1 v z))
      (norm_nonneg _)
  have hsumm : Summable (fun v => ∫ z, ‖c v * Ψ v z‖) :=
    Summable.of_nonneg_of_le (fun v => integral_nonneg fun _ => norm_nonneg _) hΨn
      (hcs.mul_right P)
  have hint : ∫ z : ℝ × ℝ, w z * Q z.2 * Ga (z.1 + ar * z.2) * Gb (z.1 + br * z.2) =
      ∑' v, c v * ∫ z, Ψ v z := by
    have h := integral_tsum_of_summable_integral_norm (fun v => (hΨi v).const_mul (c v)) hsumm
    simp_rw [integral_const_mul] at h
    rw [h]
    congr 1; funext z; exact (hpt z).tsum_eq.symm
  -- each term is a modulated separated term
  set! Sa := Real.sqrt (∫ x, ‖Ga x‖ ^ 2) with hSa
  set! Sb := Real.sqrt (∫ x, ‖Gb x‖ ^ 2) with hSb
  have hterm (v : Fin 2 → ℤ) : ‖∫ z, Ψ v z‖ ≤ r * M * Sa * Sb := by
    set! α : ℝ := (v 0 : ℝ) / (16 * r) with hα
    set! γ : ℝ := (v 1 : ℝ) / (16 * r) - α * ar with hγ
    set! A' : ℝ → ℂ := fun y => (Real.fourierChar (α * y) : ℂ) * Ga y with hA'
    have hA'm : Measurable A' :=
      (hchm.measurable.comp (measurable_const.mul measurable_id)).mul hGam
    have hA'n : ∀ y, ‖A' y‖ = ‖Ga y‖ := fun y => by simp [hA']
    have hA'1 : Integrable A' := hGa1.mono hA'm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (hA'n y).le)
    have hA'2 : MemLp A' 2 := hGa2.of_le hA'm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (hA'n y).le)
    have hA's : ∀ y, A' y ≠ 0 → y ∈ I := fun y hy => hGas y (by
      intro h; apply hy; simp [hA', h])
    have hΨe : ∀ z : ℝ × ℝ, Ψ v z = (Real.fourierChar (-(α * c₀)) : ℂ) *
        (A' (z.1 + ar * z.2) * Gb (z.1 + br * z.2) *
          ((Real.fourierChar (γ * z.2) : ℂ) * Q z.2)) := by
      intro z
      simp only [hΨ, hE, hA']
      have hph : (Real.fourierChar ((v 0 : ℝ) * ((z.1 - c₀) / r / 16) +
          (v 1 : ℝ) * (z.2 / r / 16)) : ℂ) =
          (Real.fourierChar (-(α * c₀)) : ℂ) * (Real.fourierChar (α * (z.1 + ar * z.2)) : ℂ) *
            (Real.fourierChar (γ * z.2) : ℂ) := by
        rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
          ← AddChar.map_add_eq_mul]
        congr 2
        rw [hγ, hα]; field_simp; ring
      rw [hph]; ring
    simp_rw [hΨe]
    rw [integral_const_mul, norm_mul, Circle.norm_coe, one_mul]
    have h := separated_term_bound hA'm hGbm hA'1 hA'2 hGb1 hGb2 hr hA's hGbs hab1 hQm hQ1
      hζi hζ1 hM γ
    have hn : ∫ x, ‖A' x‖ ^ 2 = ∫ x, ‖Ga x‖ ^ 2 := by simp_rw [hA'n]
    rw [hn] at h
    exact h
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ ∑' v, ‖c v‖ := tsum_nonneg fun _ => norm_nonneg _
  have hK0 : 0 ≤ r * M * Sa * Sb := by positivity
  have hsum2 : Summable (fun v => ‖c v * ∫ z, Ψ v z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun v => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hterm v) (norm_nonneg _))
      (hcs.mul_right _)
  have hbound : ‖∑' v, c v * ∫ z, Ψ v z‖ ≤ kernelFourierConst κ * (r * M * Sa * Sb) := by
    calc ‖∑' v, c v * ∫ z, Ψ v z‖ ≤ ∑' v, ‖c v * ∫ z, Ψ v z‖ := norm_tsum_le_tsum_norm hsum2
      _ ≤ ∑' v, ‖c v‖ * (r * M * Sa * Sb) :=
          hsum2.tsum_le_tsum (fun v => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hterm v) (norm_nonneg _))
            (hcs.mul_right _)
      _ = (∑' v, ‖c v‖) * (r * M * Sa * Sb) := tsum_mul_right
      _ ≤ _ := mul_le_mul_of_nonneg_right hct hK0
  rw [hint, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hSa' : Real.sqrt (r⁻¹ * ∫ x in I, ‖Fa x‖ ^ 2) = Real.sqrt r⁻¹ * Sa := by
    rw [Real.sqrt_mul (inv_nonneg.mpr hr.le), hSa, hGa, hsq]
  have hSb' : Real.sqrt (r⁻¹ * ∫ x in I, ‖Fb x‖ ^ 2) = Real.sqrt r⁻¹ * Sb := by
    rw [Real.sqrt_mul (inv_nonneg.mpr hr.le), hSb, hGb, hsq]
  rw [hSa', hSb']
  have hrr : Real.sqrt r⁻¹ * Real.sqrt r⁻¹ = r⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hr.le)
  calc r⁻¹ ^ 2 * ‖∑' v, c v * ∫ z, Ψ v z‖ ≤
      r⁻¹ ^ 2 * (kernelFourierConst κ * (r * M * Sa * Sb)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = kernelFourierConst κ * M * (Real.sqrt r⁻¹ * Sa) * (Real.sqrt r⁻¹ * Sb) := by
        have : kernelFourierConst κ * M * (Real.sqrt r⁻¹ * Sa) * (Real.sqrt r⁻¹ * Sb) =
            kernelFourierConst κ * M * (Real.sqrt r⁻¹ * Real.sqrt r⁻¹) * Sa * Sb := by ring
        rw [this, hrr]
        field_simp

/-! ### The separated phase (lem:separation, line 1411) -/

theorem inner_single_realMatrixOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (realMatrixOperator A (EuclideanSpace.single j 1)) =
      A i j := by
  rw [EuclideanSpace.inner_single_left]
  simp [realMatrixOperator, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- A rational matrix acting as an orthogonal projection is symmetric. -/
theorem isSymm_of_realMatrixOperator_starProjection {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ}
    {U : Submodule ℝ (EuclideanSpace ℝ (Fin n))} [U.HasOrthogonalProjection]
    (h : realMatrixOperator (Q.map (fun q => (q : ℝ))) = U.starProjection) : Q.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have e1 := inner_single_realMatrixOperator (Q.map (fun q => (q : ℝ))) i j
  have e2 := inner_single_realMatrixOperator (Q.map (fun q => (q : ℝ))) j i
  rw [h] at e1 e2
  rw [← Submodule.inner_starProjection_left_eq_right, real_inner_comm] at e1
  have := e2.symm.trans e1
  simp only [Matrix.map_apply] at this
  exact_mod_cast this

theorem inner_eq_sum_euclidean {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, x k * y k := by
  rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro k _
  rw [real_inner_eq_re_inner, RCLike.inner_apply]; simp [mul_comm]

theorem one_sub_map_cast {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) :
    (1 - Q).map (fun q => (q : ℝ)) = 1 - Q.map (fun q => (q : ℝ)) := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

/-- The isotropy of the fast subspace as a matrix identity. -/
theorem isotropy_matrix_of_starProjection {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ}
    {M : Matrix (Fin n) (Fin n) ℝ} {U : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    [U.HasOrthogonalProjection]
    (hP : realMatrixOperator ((1 - Q).map (fun q => (q : ℝ))) = U.starProjection)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, inner ℝ y (realMatrixOperator M x) = 0) :
    (1 - Q.map (fun q => (q : ℝ))).transpose * M * (1 - Q.map (fun q => (q : ℝ))) = 0 := by
  have hPm := one_sub_map_cast Q
  set P := 1 - Q.map (fun q => (q : ℝ)) with hPdef
  rw [hPm] at hP
  have hcol (j : Fin n) : realMatrixOperator P (EuclideanSpace.single j 1) ∈ U := by
    rw [hP]; exact Submodule.starProjection_apply_mem U _
  have hcolv (j k : Fin n) : (realMatrixOperator P (EuclideanSpace.single j 1)) k = P k j := by
    simp [realMatrixOperator, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  have h0 := hiso _ (hcol j) _ (hcol i)
  rw [inner_eq_sum_euclidean] at h0
  simp only [realMatrixOperator_apply, hcolv] at h0
  simp only [Matrix.zero_apply]
  rw [← h0]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  have hcol' : P.mulVec (EuclideanSpace.single j (1 : ℝ)).ofLp = fun l => P l j := by
    funext l; simp [Matrix.mulVec, dotProduct]
  rw [hcol']
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _
  ring

/-- A one-variable chart regarded as a chart in one real variable. -/
noncomputable def oneVariableChart {d : ℕ} (A : QuadraticChartData d) :
    MultivariableQuadraticChartData 1 d where
  horizontal := fun i _ => A.horizontal i
  quadratic := fun _ _ => A.quadratic
  symmetric := by ext i j; fin_cases i; fin_cases j; rfl
  linear := fun _ => A.linear
  matrix := A.matrix
  amplitude := A.amplitude
  smooth := A.smooth
  compact := A.compact

theorem oneVariableChart_atom {d : ℕ} (A : QuadraticChartData d) (z : Fin 1 → ℝ) :
    multivariableQuadraticChartAtom (oneVariableChart A) z = quadraticChartAtom A (z 0) := by
  have hv : (oneVariableChart A).horizontal.mulVec z = chartHorizontalPosition A (z 0) := by
    funext i; simp [oneVariableChart, Matrix.mulVec, dotProduct, chartHorizontalPosition]
  unfold multivariableQuadraticChartAtom quadraticChartAtom
  rw [hv]
  congr 1
  congr 2; simp [oneVariableChart]; ring

theorem oneVariableChart_complexity {d c₀ : ℕ} {H : ℝ} {A : QuadraticChartData d}
    (hA : QuadraticChartComplexity c₀ H A) :
    MultivariableQuadraticChartComplexity c₀ H (oneVariableChart A) where
  lower := hA.lower
  dimension := hA.dimension
  height := hA.height
  support := hA.support
  derivative := hA.derivative

/-- The Fourier transform on `ℝ¹` of a function of the single coordinate. -/
theorem fourier_euclidean_one (g : ℝ → ℂ) (ξ : EuclideanSpace ℝ (Fin 1)) :
    𝓕 (fun z : EuclideanSpace ℝ (Fin 1) => g (z.ofLp 0)) ξ =
      ∫ u, (Real.fourierChar (-(u * ξ.ofLp 0)) : ℂ) * g u := by
  rw [Real.fourier_eq]
  have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h := hmp.integral_comp' (fun u : ℝ => (Real.fourierChar (-(u * ξ.ofLp 0)) : ℂ) * g u)
  rw [← h]
  congr 1; funext z
  have hin : inner ℝ z ξ = z.ofLp 0 * ξ.ofLp 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_one]; simp [mul_comm]
  simp only [Circle.smul_def, smul_eq_mul, hin]
  rfl

theorem quadForm_entry {d : ℕ} (V : Matrix (Fin d) (Fin 1) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (V.transpose * M * V) 0 0 = ∑ i, ∑ j, V i 0 * M i j * V j 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- In one real variable the effective quadratic of lem:weyl is a single quadratic form. -/
theorem effectiveReturnQuadratic_one {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (Λ : Matrix (Fin 1) (Fin 1) ℝ) (V : Matrix (Fin d) (Fin 1) ℝ)
    (Qr : Matrix (Fin d) (Fin d) ℝ) :
    effectiveReturnQuadratic C Λ V ((1 - Qr) * V) (Qr * V) 0 0 =
      Λ 0 0 + ∑ i, ∑ j, V i 0 *
        (((1 / 2 : ℝ) • realSymmetricPart C + (1 - Qr).transpose * realSkewPart C * Qr) i j) *
          V j 0 := by
  have h1 : realSymmetricPart (((1 - Qr) * V).transpose * realSkewPart C * (Qr * V)) 0 0 =
      (V.transpose * ((1 - Qr).transpose * realSkewPart C * Qr) * V) 0 0 := by
    have e : ((1 - Qr) * V).transpose * realSkewPart C * (Qr * V) =
        V.transpose * ((1 - Qr).transpose * realSkewPart C * Qr) * V := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [e]
    simp only [realSymmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul]
    ring
  unfold effectiveReturnQuadratic
  rw [Matrix.add_apply, Matrix.add_apply, h1, Matrix.smul_apply, smul_eq_mul, quadForm_entry,
    quadForm_entry]
  simp only [Finset.mul_sum]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem abs_rat_le_of_height {q : ℚ} {B : ℝ} (h : (rationalHeight q : ℝ) ≤ B) :
    |(q : ℝ)| ≤ B := (abs_rat_le_rationalHeight q).trans h

/-- Height of the separated phase matrix: quasipolynomial in the heights of `C` and `Q`. -/
theorem separatedPhaseMatrix_height {d : ℕ} {H B : ℝ} (hH : 1 ≤ H) (hB : 1 ≤ B)
    (C Q : Matrix (Fin d) (Fin d) ℚ) (hC : ∀ i j, (rationalHeight (C i j) : ℝ) ≤ H)
    (hQ : ∀ i j, (rationalHeight (Q i j) : ℝ) ≤ B) (i j : Fin d) :
    (rationalHeight (separatedPhaseMatrix C Q i j) : ℝ) ≤
      4 * H ^ (d ^ 2) * (B ^ (d ^ 2)) ^ 2 * (H + (d : ℝ) ^ 2 * ((1 + B) * H * B) + 1) := by
  obtain ⟨P, Z, hP, hPH, hZ⟩ := chart_matrix_clear_denominators (by linarith) C (fun i j => hC i j)
  obtain ⟨q, W, hq, hqB, hW⟩ := chart_matrix_clear_denominators (by linarith) Q (fun i j => hQ i j)
  have hZq : ∀ k l, (Z k l : ℚ) = (P : ℚ) * C k l := fun k l => by
    have := hZ k l; exact_mod_cast this
  have hWq : ∀ k l, (W k l : ℚ) = (q : ℚ) * Q k l := fun k l => by
    have := hW k l; exact_mod_cast this
  have hint : ∃ z : ℤ, ((4 * P * q ^ 2 : ℕ) : ℚ) * separatedPhaseMatrix C Q i j = z := by
    refine ⟨(q : ℤ) ^ 2 * (Z i j + Z j i) + ∑ l, ∑ k,
      2 * ((if k = i then (q : ℤ) else 0) - W k i) * (Z k l - Z l k) * W l j, ?_⟩
    simp only [separatedPhaseMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    push_cast
    simp only [hZq, hWq]
    rw [mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      split_ifs <;> ring
  have hbound : |((separatedPhaseMatrix C Q i j : ℚ) : ℝ)| ≤
      H / 2 + (d : ℝ) ^ 2 * ((1 + B) * H * B) := by
    have hCa : ∀ k l, |(C k l : ℝ)| ≤ H := fun k l => abs_rat_le_of_height (hC k l)
    have hQa : ∀ k l, |(Q k l : ℝ)| ≤ B := fun k l => abs_rat_le_of_height (hQ k l)
    have hcast := congrFun (congrFun (separatedPhaseMatrix_cast C Q) i) j
    simp only [Matrix.map_apply] at hcast
    rw [hcast]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
      realSymmetricPart, realSkewPart, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply,
      smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := abs_add_le (C i j : ℝ) (C j i)
      nlinarith only [hCa i j, hCa j i, this]
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l, |(∑ k, ((if k = i then (1 : ℝ) else 0) - (Q k i : ℝ)) *
            (1 / 2 * ((C k l : ℝ) - C l k))) * (Q l j : ℝ)| ≤
          ∑ _l : Fin d, ∑ _k : Fin d, (1 + B) * H * B := by
            apply Finset.sum_le_sum; intro l _
            rw [abs_mul]
            have hk : ∀ k : Fin d, |((if k = i then (1 : ℝ) else 0) - (Q k i : ℝ)) *
                (1 / 2 * ((C k l : ℝ) - C l k))| ≤ (1 + B) * H := by
              intro k
              rw [abs_mul]
              have h1 : |(if k = i then (1 : ℝ) else 0) - (Q k i : ℝ)| ≤ 1 + B := by
                refine (abs_sub _ _).trans (add_le_add ?_ (hQa k i))
                split_ifs <;> simp
              have h2 : |1 / 2 * ((C k l : ℝ) - C l k)| ≤ H := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
                have := abs_sub (C k l : ℝ) (C l k)
                linarith [hCa k l, hCa l k]
              exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
            calc _ ≤ (∑ _k : Fin d, (1 + B) * H) * B :=
                  mul_le_mul ((Finset.abs_sum_le_sum_abs _ _).trans
                    (Finset.sum_le_sum fun k _ => hk k)) (hQa l j) (abs_nonneg _)
                    (Finset.sum_nonneg fun _ _ => by positivity)
              _ = _ := by rw [Finset.sum_mul]
        _ = (d : ℝ) ^ 2 * ((1 + B) * H * B) := by simp [Finset.card_univ]; ring
  have hD : 0 < 4 * P * q ^ 2 := by positivity
  have h := rationalHeight_le_of_mul_int (separatedPhaseMatrix C Q i j) hD hint
  refine h.trans ?_
  push_cast
  have hP' : (P : ℝ) ≤ H ^ (d ^ 2) := hPH
  have hq' : (q : ℝ) ≤ B ^ (d ^ 2) := hqB
  gcongr
  linarith

/-- Blueprint lem:separation, eq:separated-phase (line 1411): if the Fourier supremum
`A_r` of a time chart is at least `δ`, then on the scale-`r` window
`Q(t) = e(λ_* t² + β t) Σ a_ℓ e(σ_ℓ·θ t)` exactly and absolutely, with
`λ_* = λ + θᵀ M θ` for a rational matrix `M` of bounded height, `|λ_*| r² ≤ D`, and
rational frequencies `σ_ℓ` of height `≤ D(1+|ℓ|)` and the shell bounds of lem:chartfourier;
everything is quasipolynomial in `H` and `δ⁻¹`. -/
theorem separatedPhase (c₀ : ℕ) (hc : 1 ≤ c₀) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ DJ : ℕ → ℕ, ∀ {d : ℕ} (H δ r : ℝ) (A : QuadraticChartData d),
      QuadraticChartComplexity c₀ H A → 0 < r →
      ∀ ζ : ℝ → ℂ, Measurable ζ → (∀ u, ‖ζ u‖ ≤ H) → (∀ u v, ‖ζ v - ζ u‖ ≤ H * |v - u|) →
      (∀ u, ζ u ≠ 0 → |u| ≤ R) → 0 < δ →
      (∀ s < δ, ∃ ξ : ℝ, s < ‖∫ u, (Real.fourierChar (-(u * ξ)) : ℂ) *
        (ζ u * quadraticChartAtom A (r * u))‖) →
      let X := 1 + Real.log H + Real.log (max 1 δ⁻¹)
      ∃ M : Matrix (Fin d) (Fin d) ℚ,
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤ Real.exp (D * X ^ D)) ∧
        |A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j| * r ^ 2 ≤
          Real.exp (D * X ^ D) ∧
        ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin (d + d) → ℤ) → Fin d → ℚ),
          (Fintype.card ι : ℝ) ≤ Real.exp (D * X ^ D) ∧
          (∀ p i, (rationalHeight (σ p i) : ℝ) ≤
            Real.exp (D * X ^ D) * (1 + frequencyLength p.2)) ∧
          ∃ a : ι × (Fin (d + d) → ℤ) → ℂ,
            (∀ t : ℝ, |t| ≤ R * r →
              HasSum (fun p => a p *
                  (Real.fourierChar ((∑ i, (σ p i : ℝ) * A.horizontal i) * t) : ℂ))
                ((Real.fourierChar (-((A.quadratic +
                    ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j) * t ^ 2 +
                    A.linear * t)) : ℂ) * quadraticChartAtom A t)) ∧
            Summable (fun p => ‖a p‖) ∧ (∑' p, ‖a p‖) ≤ Real.exp (D * X ^ D) ∧
            ∀ J : ℕ,
              (∀ p, ‖a p‖ * (1 + frequencyLength p.2) ^ (J * (d + 1) ^ 2) ≤
                Real.exp (DJ J * X ^ DJ J)) ∧
              ∀ T : ℝ, 1 ≤ T →
                (∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖) *
                    T ^ (J * (d + 1) ^ 2) ≤ Real.exp (DJ J * X ^ DJ J) := by
  obtain ⟨Dw, hDw, hweyl⟩ := weylSplitting c₀ hc R hR
  obtain ⟨Ds, hDs, DJs, hsplit⟩ := splitFourierExpansion c₀ hc 1 R hR
  set Dm : ℕ := 12 * (1 + Dw) + Ds * (1 + Dw) ^ Ds + Dw * Ds + Dw + 3 with hDm
  have hDm1 : Dw * Ds ≤ Dm := by
    rw [hDm]; generalize Ds * (1 + Dw) ^ Ds = x; generalize Dw * Ds = y; omega
  have hDm2 : Dw + 2 ≤ Dm := by
    rw [hDm]; generalize Ds * (1 + Dw) ^ Ds = x; generalize Dw * Ds = y; omega
  have hDm3 : Dw ≤ Dm := by omega
  refine ⟨Dm, by omega, fun J => DJs J * (1 + Dw) ^ (DJs J) + Dw * DJs J + 1, ?_⟩
  intro d H δ r A hA hr ζ hζm hζ hζL hζs hδ hsup X
  -- the chart `Q(r·)` in one real variable
  set! A' := oneVariableChart (dilateQuadraticChart r A) with hA'
  have hA'c : MultivariableQuadraticChartComplexity c₀ H A' :=
    oneVariableChart_complexity (dilateQuadraticChart_complexity hA r)
  set! θw : (Fin 1 → ℝ) → ℂ := fun z => ζ (z 0) with hθw
  have hθm : Measurable θw := hζm.comp (measurable_pi_apply 0)
  have hθb : ∀ z, ‖θw z‖ ≤ H := fun z => hζ _
  have hθL : ∀ x y, ‖θw y - θw x‖ ≤ H * ‖y - x‖ := fun x y => by
    have hH0 : 0 ≤ H := (quadraticChartComplexity_parameter_pos hA).le
    refine (hζL (x 0) (y 0)).trans (mul_le_mul_of_nonneg_left ?_ hH0)
    have := norm_le_pi_norm (y - x) 0
    rwa [Pi.sub_apply, Real.norm_eq_abs] at this
  have hθs : ∀ z, θw z ≠ 0 → ∀ i, |z i| ≤ R := fun z hz i => by
    have : i = 0 := Subsingleton.elim _ _
    subst this; exact hζs _ hz
  have hF : ∀ s < δ, ∃ ξ : EuclideanSpace ℝ (Fin 1), s < ‖𝓕 (fun z : EuclideanSpace ℝ (Fin 1) =>
      θw z.ofLp * multivariableQuadraticChartAtom A' z.ofLp) ξ‖ := by
    intro s hs
    obtain ⟨ξ, hξ⟩ := hsup s hs
    refine ⟨EuclideanSpace.single 0 ξ, ?_⟩
    have he : (fun z : EuclideanSpace ℝ (Fin 1) =>
        θw z.ofLp * multivariableQuadraticChartAtom A' z.ofLp) =
        fun z => (fun u => ζ u * quadraticChartAtom A (r * u)) (z.ofLp 0) := by
      funext z
      simp only [hθw, hA', oneVariableChart_atom, dilateQuadraticChart_atom]
    rw [he, fourier_euclidean_one (fun u => ζ u * quadraticChartAtom A (r * u))]
    simpa using hξ
  obtain ⟨U, Q, hQU, hPU, hiso, hQh, hPh, hVs, hΛ⟩ :=
    hweyl (k := 1) le_rfl (by norm_num) H A' hA'c θw hθm hθb hθL hθs δ hδ hF
  set B := Real.exp ((Dw : ℝ) * (1 + Real.log H + Real.log (max 1 δ⁻¹)) ^ Dw) with hBdef
  have hH1 : 1 ≤ H := by linarith only [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hA.lower
  have hlogδ : 0 ≤ Real.log (max 1 δ⁻¹) := Real.log_nonneg (le_max_left _ _)
  have hX3 : 3 ≤ X := by simp only [X]; linarith only [hlogH, hlogδ]
  have hX1 : 1 ≤ X := by linarith only [hlogH, hlogδ]
  have hXD : 1 ≤ (Dw : ℝ) * X ^ Dw := by
    have : (1 : ℝ) ≤ X ^ Dw := one_le_pow₀ hX1
    have : (1 : ℝ) ≤ Dw := by exact_mod_cast hDw
    nlinarith
  have hB2 : 2 ≤ B := by
    have : Real.exp 1 ≤ B := Real.exp_le_exp.mpr hXD
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hQs : Q.IsSymm := isSymm_of_realMatrixOperator_starProjection hQU
  have hiso' := isotropy_matrix_of_starProjection hPU hiso
  obtain ⟨ι, hι, σ, hcard, hσ, hrest⟩ := hsplit (d := d) H B hA.lower hA.dimension hB2
    A.matrix Q (fun i j => hA.height i j) hQs hQh hiso'
  obtain ⟨a, hexp, hsumm, htot, hJ⟩ := hrest A' rfl hA'c hVs
  -- the phase identity in the variable `t`
  set! M := separatedPhaseMatrix A.matrix Q with hMdef
  set! lam := A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j with hlam
  set Λe := effectiveReturnQuadratic (A.matrix.map (fun q => (q : ℝ))) A'.quadratic
    A'.horizontal ((1 - Q.map (fun q => (q : ℝ))) * A'.horizontal)
    (Q.map (fun q => (q : ℝ)) * A'.horizontal) with hΛe
  have hΛ00 : Λe 0 0 = r ^ 2 * lam := by
    rw [hΛe, effectiveReturnQuadratic_one, ← separatedPhaseMatrix_cast]
    simp only [hA', oneVariableChart, dilateQuadraticChart, Matrix.map_apply, hlam, hMdef]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hHX : 1 + Real.log H ≤ X := by simp only [X]; linarith only [hlogδ]
  have hbudget := exp_log_budget_le (Ds := Ds) (Dm := Dm) hH1 hX1 hDw hHX hDm1 (by
    rw [hDm]; push_cast
    have : (0 : ℝ) ≤ Dw * Ds := by positivity
    linarith)
  change Real.exp (Ds * (1 + Real.log H + Real.log B) ^ Ds) ≤ _ at hbudget
  have hmain : ∀ {y : ℝ}, y ≤ Real.exp (Ds * (1 + Real.log H + Real.log B) ^ Ds) →
      y ≤ Real.exp (Dm * X ^ Dm) := fun h => h.trans hbudget
  refine ⟨M, ?_, ?_, ι, hι, σ, hmain hcard, fun p i => (hσ p i).trans
    (mul_le_mul_of_nonneg_right (hmain le_rfl) (by
      have := frequencyLength_nonneg p.2; linarith)), a, ?_, hsumm, hmain htot, ?_⟩
  · intro i j
    have h := separatedPhaseMatrix_height (H := H) (B := B) hH1 (by linarith) A.matrix Q
      (fun i j => hA.height i j) hQh i j
    have hdX : (d : ℝ) ≤ X := by
      have := hA.dimension; simp only [X]; linarith
    have hb := phase_height_budget (Dw := Dw) hDw hH1 (by simp only [X]; linarith) hX3 hdX
    refine h.trans (hb.trans (exp_poly_le hX1 hDm2 (by
      rw [hDm]; push_cast
      have : (0 : ℝ) ≤ Ds * (1 + Dw) ^ Ds + Dw * Ds := by positivity
      linarith)))
  · have h := realMatrix_abs_entry_le_norm Λe 0 0
    rw [hΛ00, abs_mul, abs_of_nonneg (by positivity)] at h
    rw [mul_comm]
    have hΛ' := hΛ
    rw [one_sub_map_cast] at hΛ'
    refine (h.trans hΛ').trans (exp_poly_le hX1 hDm3 (by
      rw [hDm]; push_cast
      have : (0 : ℝ) ≤ Ds * (1 + Dw) ^ Ds + Dw * Ds := by positivity
      linarith))
  · intro t ht
    set! z : Fin 1 → ℝ := fun _ => t / r with hz
    have hzR : ∀ i, |z i| ≤ R := fun i => by
      simp only [hz, abs_div, abs_of_pos hr]
      rw [div_le_iff₀ hr]; linarith
    have h := hexp z hzR
    have e1 : ∀ p, dotProduct (fun i => (σ p i : ℝ)) (A'.horizontal.mulVec z) =
        (∑ i, (σ p i : ℝ) * A.horizontal i) * t := fun p => by
      simp only [dotProduct, Matrix.mulVec, hA', oneVariableChart, dilateQuadraticChart, hz,
        Fin.sum_univ_one, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      field_simp
    have e2 : dotProduct z (Λe.mulVec z) + dotProduct A'.linear z = lam * t ^ 2 + A.linear * t := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, hz]
      rw [hΛ00]
      simp only [hA', oneVariableChart, dilateQuadraticChart]
      field_simp
    have e3 : multivariableQuadraticChartAtom A' z = quadraticChartAtom A t := by
      rw [hA', oneVariableChart_atom, dilateQuadraticChart_atom]
      congr 1; simp only [hz]; field_simp
    simp_rw [e1] at h
    rw [e2, e3] at h
    exact h
  · intro J
    have hbudgetJ := exp_log_budget_le (Ds := DJs J)
      (Dm := DJs J * (1 + Dw) ^ DJs J + Dw * DJs J + 1) hH1 hX1 hDw hHX (by omega) (by
        push_cast
        have : (0 : ℝ) ≤ Dw * DJs J := by positivity
        linarith)
    change Real.exp (DJs J * (1 + Real.log H + Real.log B) ^ DJs J) ≤ _ at hbudgetJ
    obtain ⟨hp, hs⟩ := hJ J
    exact ⟨fun p => (hp p).trans hbudgetJ,
      fun T hT => (hs T hT).trans hbudgetJ⟩

/-! ### Uniform separated approximation of the kernel (lem:separation, line 1411) -/

/-- A smooth function on `ℝ²` supported in `[-4,4]²` with coordinate-line derivative bounds
has an absolutely convergent Fourier expansion on `[-8,8]²` with explicit coefficient decay. -/
theorem unitSquare_fourier_expansion {F : (Fin 2 → ℝ) → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : ∀ u, F u ≠ 0 → ∀ l, |u l| ≤ 4) {A : ℕ → ℝ}
    (hA : ∀ (m : ℕ) (i : Fin 2) (x : Fin 1 → ℝ) (t : ℝ),
      ‖iteratedDeriv m (fun s => F (i.insertNth s x)) t‖ ≤ A m) :
    let c := periodicFourierCoeff (cubePeriodization F 16)
    Summable (fun v => ‖c v‖) ∧
      (∀ m, 2 < m → ∀ v, v ≠ 0 → ‖c v‖ ≤
        (4 ^ 2 * (16 ^ m * A m)) * (Real.sqrt (2 : ℕ) / (2 * Real.pi * frequencyLength v)) ^ m) ∧
      (∀ v, ‖c v‖ ≤ 4 ^ 2 * (16 ^ 0 * A 0)) ∧
      ∀ u : Fin 2 → ℝ, (∀ l, |u l| ≤ 8) →
        HasSum (fun v => c v * (Real.fourierChar ((v 0 : ℝ) * (u 0 / 16) +
          (v 1 : ℝ) * (u 1 / 16)) : ℂ)) (F u) := by
  intro c
  set f := cubePeriodization F 16 with hf
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
    cubePeriodization_smooth hF (by norm_num) (by norm_num) hsupp
  have hline (m : ℕ) (i : Fin 2) (x : Fin 1 → ℝ) (t : ℝ) :
      ‖iteratedDeriv m (fun s => f (i.insertNth s x)) t‖ ≤ 4 ^ 2 * (16 ^ m * A m) :=
    cubePeriodization_line_le hF (by norm_num) (by norm_num) hsupp m (hA m) i x t
  have hB (y : Fin 2 → ℝ) : ‖f y‖ ≤ 4 ^ 2 * (16 ^ 0 * A 0) := by
    have h := hline 0 0 (Fin.tail y) (y 0)
    rw [iteratedDeriv_zero] at h
    have hy : (Fin.insertNth 0 (y 0) (Fin.tail y) : Fin 2 → ℝ) = y := by
      funext l; fin_cases l <;> rfl
    rwa [hy] at h
  have hexp (m : ℕ) (hm : 1 + 1 < m) := periodic_fourier_expansion (d := 1) hm f hfs.continuous
    (cubePeriodization_periodic F 16)
    (fun i x => (hfs.comp (contDiff_insertNth_line i x)).of_le (by exact_mod_cast le_top))
    (hline m) hB
  have h2 : Real.sqrt ((1 : ℕ) + 1 : ℝ) = Real.sqrt ((2 : ℕ) : ℝ) := by norm_num
  refine ⟨(hexp 3 (by norm_num)).2.1, fun m hm v hv => ?_, (hexp 3 (by norm_num)).2.2.2, ?_⟩
  · have := (hexp m hm).2.2.1 v hv
    rw [h2] at this; exact this
  · intro u hu
    have heq := cubePeriodization_eq F (R := 4) (L := 16) (by norm_num) (by norm_num)
      (by norm_num) hsupp u (fun l => by linarith [hu l])
    have h := (hexp 3 (by norm_num)).1 (fun l => u l / 16)
    have hfu : f (fun l => u l / 16) = F u := by rw [hf, heq]
    rw [hfu] at h
    have hc : periodicFourierCoeff f = c := rfl
    rw [hc] at h
    convert h using 2 with v
    simp [Fin.sum_univ_two]

/-- The admissible kernel times the chirp `e(Λ u₁²)`, at unit scale. -/
noncomputable def chirpedKernelRescale (a₀ r Λ : ℝ) (w : ℝ × ℝ → ℂ) (u : Fin 2 → ℝ) : ℂ :=
  kernelUnitRescale a₀ r w u * (Real.fourierChar (Λ * u 1 ^ 2) : ℂ)

/-- Cumulative derivative constant of the kernel class up to order `m`. -/
noncomputable def kernelDerivSum (κ : LocalKernelClass) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), kernelDerivBound κ i

theorem kernelDerivBound_le_sum (κ : LocalKernelClass) {i m : ℕ} (hi : i ≤ m) :
    kernelDerivBound κ i ≤ kernelDerivSum κ m :=
  Finset.single_le_sum (fun j _ => kernelDerivBound_nonneg κ j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- The coordinate-line derivative constant of the chirped kernel. -/
noncomputable def chirpLineBound (κ : LocalKernelClass) (Λ : ℝ) (m : ℕ) : ℝ :=
  kernelDerivSum κ m * (1 + (m + 1) * (2 * Real.pi) * (max (|Λ| * 25) 1 * 2)) ^ m

theorem chirpLineBound_nonneg (κ : LocalKernelClass) (Λ : ℝ) (m : ℕ) :
    0 ≤ chirpLineBound κ Λ m := by
  unfold chirpLineBound kernelDerivSum
  have := fun j => kernelDerivBound_nonneg κ j
  have : 0 ≤ ∑ i ∈ Finset.range (m + 1), kernelDerivBound κ i := Finset.sum_nonneg fun j _ => this j
  positivity

theorem chirpedKernelRescale_support {κ : LocalKernelClass} {a₀ r Λ : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {u : Fin 2 → ℝ}
    (hu : chirpedKernelRescale a₀ r Λ w u ≠ 0) (l : Fin 2) : |u l| ≤ 4 :=
  kernelUnitRescale_support hr hw (left_ne_zero_of_mul hu) l

theorem chirpedKernelRescale_smooth {κ : LocalKernelClass} {a₀ r : ℝ} {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (Λ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chirpedKernelRescale a₀ r Λ w) := by
  unfold chirpedKernelRescale kernelUnitRescale
  exact (hw.smooth.comp (by fun_prop)).mul (chart_fourierChar_smooth.comp (by fun_prop))

theorem chirpedKernelRescale_line_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (Λ : ℝ) (m : ℕ) (i : Fin 2)
    (x : Fin 1 → ℝ) (t : ℝ) :
    ‖iteratedDeriv m (fun s => chirpedKernelRescale a₀ r Λ w (i.insertNth s x)) t‖ ≤
      chirpLineBound κ Λ m := by
  have hK0 : 0 ≤ kernelDerivSum κ m :=
    Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
  have hR1 : 1 ≤ (1 + (m + 1) * (2 * Real.pi) * (max (|Λ| * 25) 1 * 2)) := by
    have : 0 ≤ (m + 1 : ℝ) * (2 * Real.pi) * (max (|Λ| * 25) 1 * 2) := by positivity
    linarith
  have hks : ContDiff ℝ (⊤ : ℕ∞) (kernelUnitRescale a₀ r w) := by
    unfold kernelUnitRescale; exact hw.smooth.comp (by fun_prop)
  fin_cases i
  · -- the slow coordinate: the chirp is a unimodular constant
    simp only [Fin.zero_eta]
    have hhs : ContDiff ℝ (⊤ : ℕ∞)
        (fun s => kernelUnitRescale a₀ r w (Fin.insertNth 0 s x : Fin 2 → ℝ)) :=
      hks.comp (contDiff_insertNth_line 0 x)
    set cc : ℂ := (Real.fourierChar (Λ * x 0 ^ 2) : ℂ) with hcc
    have he : (fun s => chirpedKernelRescale a₀ r Λ w ((0 : Fin 2).insertNth s x)) =
        fun s => cc * kernelUnitRescale a₀ r w ((0 : Fin 2).insertNth s x) := by
      funext s
      have h1 : (Fin.insertNth 0 s x : Fin 2 → ℝ) 1 = x 0 := rfl
      simp only [chirpedKernelRescale, h1, hcc]; ring
    rw [he, iteratedDeriv_const_mul cc (hhs.of_le (by exact_mod_cast le_top)).contDiffAt,
      norm_mul, hcc, Circle.norm_coe, one_mul]
    refine (kernelUnitRescale_line_le hr hw m 0 x t).trans
      ((kernelDerivBound_le_sum κ le_rfl).trans ?_)
    exact le_mul_of_one_le_right hK0 (one_le_pow₀ hR1)
  · simp only [Fin.mk_one]
    set h : ℝ → ℂ := fun s => kernelUnitRescale a₀ r w (Fin.insertNth 1 s x : Fin 2 → ℝ)
      with hh
    have hhs : ContDiff ℝ (⊤ : ℕ∞) h := hks.comp (contDiff_insertNth_line 1 x)
    have he : (fun s => chirpedKernelRescale a₀ r Λ w ((1 : Fin 2).insertNth s x)) =
        fun s => h s * (Real.fourierChar (Λ * s ^ 2) : ℂ) := by
      funext s
      have h1 : (Fin.insertNth 1 s x : Fin 2 → ℝ) 1 = s := rfl
      simp only [chirpedKernelRescale, h1, hh]
    rw [he]
    have hφs : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Λ * s ^ 2) := by fun_prop
    by_cases ht : |t| ≤ 5
    · have gh : GeomBound h t (kernelDerivSum κ m) 1 m := fun i hi => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, one_pow, mul_one]
        exact (kernelUnitRescale_line_le hr hw i 1 x t).trans (kernelDerivBound_le_sum κ hi)
      have gs : GeomBound (fun s : ℝ => s) t 5 1 m := GeomBound.id_real t ht (by norm_num) m
      have gss : GeomBound (fun s : ℝ => s * s) t (5 * 5) (1 + 1) m :=
        GeomBound.mul contDiff_id contDiff_id (by norm_num) gs gs
      have gc : GeomBound (fun _ : ℝ => Λ) t ‖Λ‖ 0 m := GeomBound.const Λ t le_rfl m
      have gφ : GeomBound (fun s : ℝ => Λ * (s * s)) t (‖Λ‖ * (5 * 5)) (0 + (1 + 1)) m :=
        GeomBound.mul contDiff_const (contDiff_id.mul contDiff_id) le_rfl gc gss
      have gφ' : GeomBound (fun s : ℝ => Λ * s ^ 2) t (|Λ| * 25) 2 m := by
        have e : (fun s : ℝ => Λ * s ^ 2) = fun s => Λ * (s * s) := by funext s; ring
        rw [e]
        have e2 : ‖Λ‖ * (5 * 5) = |Λ| * 25 := by rw [Real.norm_eq_abs]; norm_num
        have e3 : (0 : ℝ) + (1 + 1) = 2 := by norm_num
        rw [e2, e3] at gφ
        exact gφ
      have ge := GeomBound.fourierChar hφs (by norm_num : (0 : ℝ) ≤ 2) gφ'
      have gp := GeomBound.mul hhs (chart_fourierChar_smooth.comp hφs) (by norm_num) gh ge
      have hb := gp m le_rfl
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
      refine hb.trans (le_of_eq ?_)
      simp only [chirpLineBound, mul_one]
    · have hz : (fun s => h s * (Real.fourierChar (Λ * s ^ 2) : ℂ)) =ᶠ[nhds t]
          fun _ => (0 : ℂ) := by
        have hopen : IsOpen {s : ℝ | 4 < |s|} := isOpen_lt continuous_const continuous_abs
        filter_upwards [hopen.mem_nhds (show (4 : ℝ) < |t| by push Not at ht; linarith)]
          with s hs
        have : h s = 0 := by
          by_contra hne
          have := kernelUnitRescale_support hr hw hne 1
          have h1 : (Fin.insertNth 1 s x : Fin 2 → ℝ) 1 = s := rfl
          rw [h1] at this
          exact absurd hs (not_lt.mpr this)
        simp [this]
      rw [hz.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simp [chirpLineBound_nonneg]

theorem norm_tsum_sub_sum_le {β : Type*} {f : β → ℂ} (hf : Summable (fun x => ‖f x‖))
    (s : Finset β) {g : β → ℝ} (hg : Summable g) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ x, x ∉ s → ‖f x‖ ≤ g x) :
    ‖(∑' x, f x) - ∑ x ∈ s, f x‖ ≤ ∑' x, g x := by
  have hfs : Summable f := hf.of_norm
  rw [← hfs.sum_add_tsum_compl (s := s), add_sub_cancel_left]
  have hsub : Summable (fun x : ↥((s : Set β)ᶜ) => ‖f x‖) := hf.subtype _
  calc ‖∑' x : ↥((s : Set β)ᶜ), f x‖ ≤ ∑' x : ↥((s : Set β)ᶜ), ‖f x‖ :=
        norm_tsum_le_tsum_norm hsub
    _ ≤ ∑' x : ↥((s : Set β)ᶜ), g x :=
        hsub.tsum_le_tsum (fun x => hfg x x.2) (hg.subtype _)
    _ ≤ ∑' x, g x := Summable.tsum_subtype_le g _ hg0 hg

theorem not_mem_frequencyBox {n N : ℕ} {v : Fin n → ℤ} (hv : v ∉ frequencyBox n N) :
    v ≠ 0 ∧ (N : ℝ) ≤ 1 + frequencyLength v := by
  have h : ¬ frequencyLength v ≤ N := fun h => hv (mem_frequencyBox_of_length_le h)
  push Not at h
  refine ⟨fun h0 => ?_, by linarith⟩
  subst h0
  have : frequencyLength (0 : Fin n → ℤ) = 0 := by simp [frequencyLength]
  rw [this] at h
  exact absurd h (not_lt.mpr (Nat.cast_nonneg N))

/-- The constant of the chirped kernel's Fourier tail at order three. -/
noncomputable def chirpTailConst (κ : LocalKernelClass) (Λ : ℝ) : ℝ :=
  7 ^ 2 * (4 ^ 2 * (16 ^ 3 * chirpLineBound κ Λ 3)) * Real.sqrt (2 : ℕ) ^ 3 * 2

/-- lem:separation, line 1411 (core): with a time-chart expansion
`e(-Λ(t/r)²) Q(t) = Σ a_p e(γ_p t)` on the window and the chirped kernel expansion,
the kernel `w(x,t) Q(t)` on `I × I` is approximated by a finite double sum of
pure linear phases in `(x,t)`, with explicit truncation errors. -/
theorem kernel_product_approx {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (Λ : ℝ) {n : ℕ} {ι : Type*}
    [Fintype ι] (Q : ℝ → ℂ) (γ : ι × (Fin n → ℤ) → ℝ) (a : ι × (Fin n → ℤ) → ℂ)
    (ha : Summable (fun p => ‖a p‖))
    (hQ : ∀ t : ℝ, |t| ≤ r → HasSum (fun p => a p * (Real.fourierChar (γ p * t) : ℂ))
      ((Real.fourierChar (-(Λ * (t / r) ^ 2)) : ℂ) * Q t))
    {E : ℝ} (hshell : ∀ T : ℝ, 1 ≤ T →
      (∑ f : ι, ∑ v ∈ frequencyShell n T, ‖a (f, v)‖) * T ≤ E)
    {sa sb : ℝ} (hab : 1 ≤ |sb - sa|) (hsa : |sa| ≤ 3) (K₁ K₂ : ℕ) (ya yb : ℝ)
    (hya : ya ∈ Set.Icc a₀ (a₀ + r)) (hyb : yb ∈ Set.Icc a₀ (a₀ + r)) :
    let cW := periodicFourierCoeff (cubePeriodization (chirpedKernelRescale a₀ r Λ w) 16)
    let t := (yb - ya) / (sb - sa)
    let x := ya - sa * t
    ‖w (x, t) * Q t - ∑ p ∈ (Finset.univ : Finset ι) ×ˢ frequencyBox n (2 ^ K₁),
        ∑ v ∈ frequencyBox 2 (2 ^ K₂), a p * cW v *
          (Real.fourierChar ((v 0 : ℝ) * ((x - (a₀ + r / 2)) / r / 16) +
            (v 1 : ℝ) * (t / r / 16) + γ p * t) : ℂ)‖ ≤
      localKernelSupBound κ * (2 * E / 2 ^ K₁) +
        (∑' p, ‖a p‖) * (chirpTailConst κ Λ / 2 ^ K₂) := by
  intro cW t x
  set c₀ := a₀ + r / 2 with hc₀
  have hba0 : 0 < |sb - sa| := by linarith
  have hba : sb - sa ≠ 0 := abs_pos.mp hba0
  have ht : |t| ≤ r := by
    simp only [t, abs_div]
    rw [div_le_iff₀ hba0]
    have : |yb - ya| ≤ r := by rw [abs_le]; constructor <;> linarith [hya.1, hya.2, hyb.1, hyb.2]
    nlinarith
  have hx : |x - c₀| ≤ 4 * r := by
    have h1 : |sa * t| ≤ 3 * r := by
      rw [abs_mul]; exact mul_le_mul hsa ht (abs_nonneg _) (by norm_num)
    have h2 : |ya - c₀| ≤ r := by
      rw [abs_le, hc₀]; constructor <;> linarith [hya.1, hya.2]
    calc |x - c₀| = |(ya - c₀) - sa * t| := by simp only [x]; ring_nf
      _ ≤ |ya - c₀| + |sa * t| := abs_sub _ _
      _ ≤ r + 3 * r := add_le_add h2 h1
      _ = 4 * r := by ring
  -- the chirped kernel expansion
  set! A : ℕ → ℝ := chirpLineBound κ Λ with hA
  obtain ⟨hWs, hWd, hW0, hWexp⟩ := unitSquare_fourier_expansion
    (chirpedKernelRescale_smooth hw Λ) (fun u hu l => chirpedKernelRescale_support hr hw hu l)
    (A := A) (fun m i y s => chirpedKernelRescale_line_le hr hw Λ m i y s)
  set! u : Fin 2 → ℝ := ![(x - c₀) / r, t / r] with hu
  have hu8 : ∀ l, |u l| ≤ 8 := by
    intro l; fin_cases l
    · simp only [hu, Fin.zero_eta, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]; linarith
    · simp only [hu, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]; linarith
  have hFu : chirpedKernelRescale a₀ r Λ w u =
      w (x, t) * (Real.fourierChar (Λ * (t / r) ^ 2) : ℂ) := by
    simp only [chirpedKernelRescale, kernelUnitRescale, hu, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e1 : c₀ + r * ((x - c₀) / r) = x := by field_simp; ring
    have e2 : r * (t / r) = t := by field_simp
    rw [← hc₀, e1, e2]
  have hWsum := hWexp u hu8
  rw [hFu] at hWsum
  -- the time-chart expansion
  have hP := hQ t ht
  set eP : ι × (Fin n → ℤ) → ℂ := fun p => a p * (Real.fourierChar (γ p * t) : ℂ) with heP
  set eW : (Fin 2 → ℤ) → ℂ := fun v => cW v * (Real.fourierChar ((v 0 : ℝ) * (u 0 / 16) +
    (v 1 : ℝ) * (u 1 / 16)) : ℂ) with heW
  have hnP : ∀ p, ‖eP p‖ = ‖a p‖ := fun p => by simp [heP]
  have hnW : ∀ v, ‖eW v‖ = ‖cW v‖ := fun v => by simp [heW]
  have hPs : Summable (fun p => ‖eP p‖) := by simp_rw [hnP]; exact ha
  have hWs' : Summable (fun v => ‖eW v‖) := by simp_rw [hnW]; exact hWs
  set! P := ∑' p, eP p with hPdef
  set! W := ∑' v, eW v with hWdef
  have hchi : (Real.fourierChar (Λ * (t / r) ^ 2) : ℂ) *
      (Real.fourierChar (-(Λ * (t / r) ^ 2)) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    simp
  have hQt : Q t = (Real.fourierChar (Λ * (t / r) ^ 2) : ℂ) * P := by
    rw [hPdef, hP.tsum_eq, ← mul_assoc, hchi, one_mul]
  have hWt : W = w (x, t) * (Real.fourierChar (Λ * (t / r) ^ 2) : ℂ) := hWsum.tsum_eq
  have hwQ : w (x, t) * Q t = W * P := by rw [hQt, hWt]; ring
  -- the approximant is a product of truncations
  set S := (Finset.univ : Finset ι) ×ˢ frequencyBox n (2 ^ K₁) with hS
  set V := frequencyBox 2 (2 ^ K₂) with hV
  have happ : ∑ p ∈ S, ∑ v ∈ V, a p * cW v *
      (Real.fourierChar ((v 0 : ℝ) * ((x - c₀) / r / 16) + (v 1 : ℝ) * (t / r / 16) +
        γ p * t) : ℂ) = (∑ v ∈ V, eW v) * ∑ p ∈ S, eP p := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro v _
    simp only [heW, heP, hu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
    have : (x - c₀) / r / 16 = (x - c₀) / r / 16 := rfl
    ring
  rw [hwQ, happ]
  -- the two tails
  have htailP : ‖P - ∑ p ∈ S, eP p‖ ≤ 2 * E / 2 ^ K₁ := by
    obtain ⟨hgs, hgt⟩ := pooled_shell_tail_bound a hshell K₁
    refine (norm_tsum_sub_sum_le hPs S hgs (fun _ => norm_nonneg _) fun p hp => ?_).trans hgt
    have hp2 : p.2 ∉ frequencyBox n (2 ^ K₁) := by
      intro h; exact hp (Finset.mem_product.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨h1, h2⟩ := not_mem_frequencyBox hp2
    rw [hnP]
    have h2' : (2 : ℝ) ^ K₁ ≤ 1 + frequencyLength p.2 := by exact_mod_cast h2
    simp [h1, h2']
  have htailW : ‖W - ∑ v ∈ V, eW v‖ ≤ chirpTailConst κ Λ / 2 ^ K₂ := by
    have hA3 : 0 ≤ 4 ^ 2 * (16 ^ 3 * A 3) := by
      have := chirpLineBound_nonneg κ Λ 3; positivity
    have htb := frequency_tail_bound (d := 2) (m := 3) hA3 (by norm_num) cW
      (fun v hv => hWd 3 (by norm_num) v hv) K₂
    have hgs : Summable (fun v : Fin 2 → ℤ =>
        if v ≠ 0 ∧ (2 : ℝ) ^ K₂ ≤ 1 + frequencyLength v then ‖cW v‖ else 0) :=
      Summable.of_nonneg_of_le (fun v => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
        (fun v => by split_ifs <;> [exact le_rfl; exact norm_nonneg _]) hWs
    refine (norm_tsum_sub_sum_le hWs' V hgs
      (fun v => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
      fun v hv => ?_).trans (htb.trans (le_of_eq ?_))
    · obtain ⟨h1, h2⟩ := not_mem_frequencyBox hv
      rw [hnW]
      have h2' : (2 : ℝ) ^ K₂ ≤ 1 + frequencyLength v := by exact_mod_cast h2
      simp [h1, h2']
    · have hneg : ((2 : ℕ) : ℝ) - (3 : ℕ) = -1 := by norm_num
      rw [hneg, Real.rpow_neg_one, Real.rpow_neg_one, chirpTailConst, hA]
      field_simp
      norm_num
  have hW0 : ‖W‖ ≤ localKernelSupBound κ := by
    rw [hWt, norm_mul, Circle.norm_coe, mul_one]; exact admissibleLocalKernel_norm_le hw _
  have hPS : ‖∑ p ∈ S, eP p‖ ≤ ∑' p, ‖a p‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [hnP]
    exact ha.sum_le_tsum S (fun p _ => norm_nonneg _)
  have hsplit : W * P - (∑ v ∈ V, eW v) * ∑ p ∈ S, eP p =
      W * (P - ∑ p ∈ S, eP p) + (W - ∑ v ∈ V, eW v) * ∑ p ∈ S, eP p := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul hW0 htailP (norm_nonneg _) (localKernelSupBound_nonneg κ)
  · rw [norm_mul, mul_comm]
    exact mul_le_mul hPS htailW (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)

theorem chirpLineBound_le (κ : LocalKernelClass) (Λ : ℝ) (m : ℕ) :
    chirpLineBound κ Λ m ≤ kernelDerivSum κ m * ((1300 * (m + 1)) * (1 + |Λ|)) ^ m := by
  unfold chirpLineBound
  have hK0 : 0 ≤ kernelDerivSum κ m := Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
  apply mul_le_mul_of_nonneg_left _ hK0
  apply pow_le_pow_left₀ (by positivity)
  have hmax : max (|Λ| * 25) 1 * 2 ≤ 50 * (1 + |Λ|) := by
    have := abs_nonneg Λ
    rcases le_total (|Λ| * 25) 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
  have hm : (1 : ℝ) ≤ m + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hL : (1 : ℝ) ≤ 1 + |Λ| := by have := abs_nonneg Λ; linarith
  calc 1 + (m + 1) * (2 * Real.pi) * (max (|Λ| * 25) 1 * 2) ≤
      1 + (m + 1) * (2 * 4) * (50 * (1 + |Λ|)) := by gcongr
    _ ≤ (1300 * (m + 1)) * (1 + |Λ|) := by nlinarith

/-- The fixed constant of the chirped kernel tail (depends only on the kernel class). -/
noncomputable def chirpTailClassConst (κ : LocalKernelClass) : ℝ :=
  2 * (7 ^ 2 * (4 ^ 2 * (16 ^ 3 * (kernelDerivSum κ 3 * (1300 * 4) ^ 3))) * 3)

/-- The fixed constant of the chirped kernel bounds (depends only on the kernel class). -/
noncomputable def chirpClassConst (κ : LocalKernelClass) : ℝ :=
  chirpTailClassConst κ + 4 ^ 2 * kernelDerivSum κ 0 + 1

theorem chirpTailClassConst_nonneg (κ : LocalKernelClass) : 0 ≤ chirpTailClassConst κ := by
  have h3 : 0 ≤ kernelDerivSum κ 3 := Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
  unfold chirpTailClassConst; positivity

theorem chirpClassConst_pos (κ : LocalKernelClass) : 1 ≤ chirpClassConst κ := by
  unfold chirpClassConst
  have h0 : 0 ≤ kernelDerivSum κ 0 := Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
  have := chirpTailClassConst_nonneg κ
  have : 0 ≤ 4 ^ 2 * kernelDerivSum κ 0 := by positivity
  linarith

theorem sqrt_two_cube_le : Real.sqrt ((2 : ℕ) : ℝ) ^ 3 ≤ 3 := by
  have h : Real.sqrt ((2 : ℕ) : ℝ) ≤ 1.42 := by
    calc Real.sqrt ((2 : ℕ) : ℝ) ≤ Real.sqrt (1.42 ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num)
      _ = 1.42 := Real.sqrt_sq (by norm_num)
  calc Real.sqrt ((2 : ℕ) : ℝ) ^ 3 ≤ 1.42 ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 3
    _ ≤ 3 := by norm_num

theorem chirpTailConst_le (κ : LocalKernelClass) (Λ : ℝ) :
    chirpTailConst κ Λ ≤ chirpTailClassConst κ * (1 + |Λ|) ^ 3 := by
  have h3 := chirpLineBound_le κ Λ 3
  have h3' : chirpLineBound κ Λ 3 ≤ kernelDerivSum κ 3 * (1300 * 4) ^ 3 * (1 + |Λ|) ^ 3 := by
    refine h3.trans (le_of_eq ?_); push_cast; ring
  have hc0 : 0 ≤ chirpLineBound κ Λ 3 := chirpLineBound_nonneg κ Λ 3
  unfold chirpTailConst chirpTailClassConst
  calc 7 ^ 2 * (4 ^ 2 * (16 ^ 3 * chirpLineBound κ Λ 3)) * Real.sqrt ((2 : ℕ) : ℝ) ^ 3 * 2 ≤
      7 ^ 2 * (4 ^ 2 * (16 ^ 3 * (kernelDerivSum κ 3 * (1300 * 4) ^ 3 * (1 + |Λ|) ^ 3))) *
        3 * 2 := by
        have hX : 7 ^ 2 * (4 ^ 2 * (16 ^ 3 * chirpLineBound κ Λ 3)) ≤
            7 ^ 2 * (4 ^ 2 * (16 ^ 3 * (kernelDerivSum κ 3 * (1300 * 4) ^ 3 * (1 + |Λ|) ^ 3))) := by
          gcongr
        have hK3 : 0 ≤ kernelDerivSum κ 3 :=
          Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
        have hY : 0 ≤ 7 ^ 2 * (4 ^ 2 * (16 ^ 3 *
            (kernelDerivSum κ 3 * (1300 * 4) ^ 3 * (1 + |Λ|) ^ 3))) := by
          apply mul_nonneg (by norm_num); apply mul_nonneg (by norm_num)
          apply mul_nonneg (by norm_num)
          exact mul_nonneg (mul_nonneg hK3 (by norm_num)) (by positivity)
        have := mul_le_mul hX sqrt_two_cube_le (by positivity) hY
        linarith
    _ = _ := by ring

/-- Total Fourier mass of the chirped kernel. -/
theorem chirpedKernel_coeff_mass {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) (Λ : ℝ) :
    let cW := periodicFourierCoeff (cubePeriodization (chirpedKernelRescale a₀ r Λ w) 16)
    Summable (fun v => ‖cW v‖) ∧ (∑' v, ‖cW v‖) ≤ chirpClassConst κ * (1 + |Λ|) ^ 3 := by
  intro cW
  obtain ⟨hWs, hWd, hW0, -⟩ := unitSquare_fourier_expansion
    (chirpedKernelRescale_smooth hw Λ) (fun u hu l => chirpedKernelRescale_support hr hw hu l)
    (A := chirpLineBound κ Λ) (fun m i y s => chirpedKernelRescale_line_le hr hw Λ m i y s)
  have henv := fourier_coeff_envelope_bounds (n := 2) cW hWs
    (A := fun m => 4 ^ 2 * (16 ^ m * chirpLineBound κ Λ m))
    (fun m => by have := chirpLineBound_nonneg κ Λ m; positivity) hW0 hWd
  refine ⟨hWs, henv.2.2.trans ?_⟩
  have h3 := chirpTailConst_le κ Λ
  have hL : (1 : ℝ) ≤ 1 + |Λ| := by have := abs_nonneg Λ; linarith
  have hb0 : chirpLineBound κ Λ 0 = kernelDerivSum κ 0 := by simp [chirpLineBound]
  have hp : (1 : ℝ) ≤ (1 + |Λ|) ^ 3 := one_le_pow₀ hL
  have h0 : 0 ≤ kernelDerivSum κ 0 := Finset.sum_nonneg fun j _ => kernelDerivBound_nonneg κ j
  have hT0 := chirpTailClassConst_nonneg κ
  have e : 4 ^ 2 * (16 ^ 0 * chirpLineBound κ Λ 0) +
      2 * (7 ^ 2 * (4 ^ 2 * (16 ^ (0 + 2 + 1) * chirpLineBound κ Λ (0 + 2 + 1))) *
        Real.sqrt ((2 : ℕ) : ℝ) ^ (2 + 1)) = 4 ^ 2 * kernelDerivSum κ 0 + chirpTailConst κ Λ := by
    rw [hb0, chirpTailConst]; norm_num; ring
  rw [e]
  unfold chirpClassConst
  nlinarith only [h3, hp, h0]

theorem exists_two_pow_between {Y : ℝ} (hY : 1 ≤ Y) : ∃ K : ℕ, Y ≤ 2 ^ K ∧ (2 : ℝ) ^ K ≤ 2 * Y := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, Y ≤ 2 ^ K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt Y (by norm_num : (1 : ℝ) < 2)
    exact ⟨K, hK.le⟩
  classical
  let K₀ := Nat.find (⟨K, hK⟩ : ∃ K : ℕ, Y ≤ 2 ^ K)
  have hK₀ : Y ≤ 2 ^ K₀ := Nat.find_spec (⟨K, hK⟩ : ∃ K : ℕ, Y ≤ 2 ^ K)
  refine ⟨K₀, hK₀, ?_⟩
  rcases Nat.eq_zero_or_pos K₀ with h | h
  · rw [h]; simp; linarith
  · have hlt : ¬ Y ≤ 2 ^ (K₀ - 1) :=
      Nat.find_min (⟨K, hK⟩ : ∃ K : ℕ, Y ≤ 2 ^ K) (show K₀ - 1 < K₀ by omega)
    push Not at hlt
    have : (2 : ℝ) ^ K₀ = 2 * 2 ^ (K₀ - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; linarith

theorem trunc_error_le {s E ε : ℝ} {K : ℕ} (hε : 0 < ε)
    (hY : 4 * s * E / ε + 1 ≤ 2 ^ K) : s * (2 * E / 2 ^ K) ≤ ε / 2 := by
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  rw [mul_div_assoc', div_le_iff₀ hp]
  have h1 : 4 * s * E / ε * ε = 4 * s * E := div_mul_cancel₀ _ hε.ne'
  have h2 : ε / 2 * (4 * s * E / ε + 1) ≤ ε / 2 * 2 ^ K :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  nlinarith only [hε, hY, h1]

theorem trunc_error_le' {s T T' ε : ℝ} {K : ℕ} (hs : 0 ≤ s) (hT : T ≤ T') (hε : 0 < ε)
    (hY : 2 * s * T' / ε + 1 ≤ 2 ^ K) : s * (T / 2 ^ K) ≤ ε / 2 := by
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  rw [mul_div_assoc', div_le_iff₀ hp]
  have h1 : 2 * s * T' / ε * ε = 2 * s * T' := div_mul_cancel₀ _ hε.ne'
  have h2 : ε / 2 * (2 * s * T' / ε + 1) ≤ ε / 2 * 2 ^ K :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have h3 : s * T ≤ s * T' := mul_le_mul_of_nonneg_left hT hs
  nlinarith only [hs, hT, hε, hY, h1]

theorem qp_power_bound {W X : ℝ} {k cW e : ℕ} (hW1 : 1 ≤ W)
    (hlogW : Real.log W ≤ cW * X ^ e) (hX1 : 1 ≤ X) (hk : (k : ℝ) ≤ 11 * X) :
    W ^ k ≤ Real.exp (((11 * cW + e + 1 : ℕ) : ℝ) * X ^ (11 * cW + e + 1)) := by
  rw [← Real.exp_log (pow_pos (by linarith : (0 : ℝ) < W) k), Real.log_pow]
  have hl0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  have h1 : (k : ℝ) * Real.log W ≤ (11 * X) * (cW * X ^ e) :=
    mul_le_mul hk hlogW hl0 (by positivity)
  refine (Real.exp_le_exp.mpr h1).trans ?_
  have h2 : Real.exp ((11 * X) * (cW * X ^ e)) = Real.exp ((11 * cW : ℝ) * X ^ (e + 1)) := by
    congr 1; ring
  rw [h2]
  exact exp_poly_le hX1 (by omega) (by push_cast; linarith)

theorem approx_budget_K₁ {s0 EJ ε E1 Cκ : ℝ} {K : ℕ} (hs0 : 0 ≤ s0) (hEJ1 : 1 ≤ EJ)
    (hε : 0 < ε) (hε' : 1 ≤ ε⁻¹) (hE11 : 1 ≤ E1) (hC : 5 * (4 * s0 + 1) ≤ Cκ)
    (hK : (2 : ℝ) ^ K ≤ 2 * (4 * s0 * EJ / ε + 1)) :
    2 * (2 : ℝ) ^ K + 1 ≤ Cκ * E1 * EJ * ε⁻¹ := by
  have hEε : 1 ≤ EJ * ε⁻¹ := one_le_mul_of_one_le_of_one_le hEJ1 hε'
  have e1 : 4 * s0 * EJ / ε = 4 * s0 * (EJ * ε⁻¹) := by rw [div_eq_mul_inv]; ring
  rw [e1] at hK
  have h1 : 2 * (2 : ℝ) ^ K + 1 ≤ 5 * (4 * s0 + 1) * (EJ * ε⁻¹) := by nlinarith only [hs0, hK, hEε]
  have h2 : 5 * (4 * s0 + 1) ≤ Cκ * E1 := by nlinarith only [hs0, hE11, hC]
  calc 2 * (2 : ℝ) ^ K + 1 ≤ 5 * (4 * s0 + 1) * (EJ * ε⁻¹) := h1
    _ ≤ Cκ * E1 * (EJ * ε⁻¹) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Cκ * E1 * EJ * ε⁻¹ := by ring

theorem approx_budget_K₂ {A Ct L ε E1 EJ Cκ : ℝ} {K : ℕ} (hA : A ≤ E1)
    (hCt : 0 ≤ Ct) (hL1 : 1 ≤ L) (hL : L ≤ 2 * E1) (hε : 0 < ε) (hε' : 1 ≤ ε⁻¹)
    (hE11 : 1 ≤ E1) (hEJ1 : 1 ≤ EJ) (hC : 5 * (16 * Ct + 1) ≤ Cκ)
    (hK : (2 : ℝ) ^ K ≤ 2 * (2 * A * (Ct * L ^ 3) / ε + 1)) :
    2 * (2 : ℝ) ^ K + 1 ≤ (Cκ * E1 * EJ * ε⁻¹) ^ 4 := by
  have hL3 : L ^ 3 ≤ (2 * E1) ^ 3 := pow_le_pow_left₀ (by linarith) hL 3
  have e1 : 2 * A * (Ct * L ^ 3) / ε = 2 * A * (Ct * L ^ 3) * ε⁻¹ := div_eq_mul_inv _ _
  have h1 : 2 * A * (Ct * L ^ 3) ≤ 16 * Ct * E1 ^ 4 := by
    have : A * L ^ 3 ≤ E1 * (2 * E1) ^ 3 := mul_le_mul hA hL3 (by positivity) (by linarith)
    nlinarith only [hCt, this]
  have hE4 : 1 ≤ E1 ^ 4 := one_le_pow₀ hE11
  have h2 : 2 * (2 : ℝ) ^ K + 1 ≤ 5 * (16 * Ct + 1) * (E1 ^ 4 * ε⁻¹) := by
    rw [e1] at hK
    have : 2 * A * (Ct * L ^ 3) * ε⁻¹ ≤ 16 * Ct * E1 ^ 4 * ε⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have : 1 ≤ E1 ^ 4 * ε⁻¹ := one_le_mul_of_one_le_of_one_le hE4 hε'
    nlinarith only [hCt, hε', hK, h1, this]
  refine h2.trans ?_
  have hCκ1 : 1 ≤ Cκ := by linarith
  have hb : 5 * (16 * Ct + 1) * (E1 ^ 4 * ε⁻¹) ≤ Cκ ^ 4 * E1 ^ 4 * EJ ^ 4 * ε⁻¹ ^ 4 := by
    have h3 : 5 * (16 * Ct + 1) ≤ Cκ ^ 4 := hC.trans (le_self_pow₀ hCκ1 (by norm_num))
    have h4 : ε⁻¹ ≤ ε⁻¹ ^ 4 := le_self_pow₀ hε' (by norm_num)
    have h5 : 1 ≤ EJ ^ 4 := one_le_pow₀ hEJ1
    calc 5 * (16 * Ct + 1) * (E1 ^ 4 * ε⁻¹) ≤ Cκ ^ 4 * (E1 ^ 4 * ε⁻¹ ^ 4) := by
          gcongr
      _ ≤ Cκ ^ 4 * (E1 ^ 4 * ε⁻¹ ^ 4) * EJ ^ 4 :=
          le_mul_of_one_le_right (by positivity) h5
      _ = _ := by ring
  rw [mul_pow, mul_pow, mul_pow]; linarith

theorem approx_budget_mass {Cc L E1 EJ ε Cκ : ℝ} (hCc : 0 ≤ Cc) (hL1 : 1 ≤ L)
    (hL : L ≤ 2 * E1) (hε' : 1 ≤ ε⁻¹) (hE11 : 1 ≤ E1) (hEJ1 : 1 ≤ EJ) (hC : 8 * Cc ≤ Cκ)
    (hCκ1 : 1 ≤ Cκ) :
    E1 * (Cc * L ^ 3) ≤ (Cκ * E1 * EJ * ε⁻¹) ^ 4 := by
  have hL3 : L ^ 3 ≤ (2 * E1) ^ 3 := pow_le_pow_left₀ (by linarith) hL 3
  have h1 : E1 * (Cc * L ^ 3) ≤ 8 * Cc * E1 ^ 4 := by
    have := mul_le_mul_of_nonneg_left hL3 (mul_nonneg (by linarith : (0:ℝ) ≤ E1) hCc)
    nlinarith
  refine h1.trans ?_
  have h3 : 8 * Cc ≤ Cκ ^ 4 := hC.trans (le_self_pow₀ hCκ1 (by norm_num))
  have h5 : 1 ≤ EJ ^ 4 * ε⁻¹ ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hEJ1)
    (one_le_pow₀ hε')
  rw [mul_pow, mul_pow, mul_pow]
  calc 8 * Cc * E1 ^ 4 ≤ Cκ ^ 4 * E1 ^ 4 := by gcongr
    _ ≤ Cκ ^ 4 * E1 ^ 4 * (EJ ^ 4 * ε⁻¹ ^ 4) := le_mul_of_one_le_right (by positivity) h5
    _ = _ := by ring

theorem phase_split_sum {α' β' : Type*} (S : Finset α') (V : Finset β') (f : α' → β' → ℂ)
    (φ c α β : α' → β' → ℝ) (ya yb : ℝ)
    (h : ∀ p v, φ p v = c p v + α p v * ya + β p v * yb) :
    ∑ p ∈ S, ∑ v ∈ V, f p v * (Real.fourierChar (φ p v) : ℂ) =
      ∑ ν : ↥S × ↥V, f ν.1.1 ν.2.1 * (Real.fourierChar (c ν.1.1 ν.2.1) : ℂ) *
        (Real.fourierChar (α ν.1.1 ν.2.1 * ya) : ℂ) *
        (Real.fourierChar (β ν.1.1 ν.2.1 * yb) : ℂ) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_coe_sort V]
  apply Finset.sum_congr rfl; intro v _
  rw [h, mul_assoc, mul_assoc, ← Circle.coe_mul, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 3; ring

/-- Blueprint lem:separation, line 1411: if `A_r ≥ δ`, the two-variable kernel
`w(x,t) Q(t)` on `I × I` (with `t = (y_b - y_a)/(b - a)`, `x = y_a - a t`) has a uniform
`ε`-approximation by a finite sum `Σ c_ν e(α_ν y_a) e(β_ν y_b)` of products of bounded
atoms (pure linear phases), with number of terms and absolute coefficient norm
quasipolynomial in `H, δ⁻¹, ε⁻¹`. -/
theorem separatedKernelApprox (c₀ : ℕ) (hc : 1 ≤ c₀) (R : ℝ) (hR : 1 ≤ R)
    (κ : LocalKernelClass) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ {d : ℕ} (H δ ε r a₀ : ℝ) (A : QuadraticChartData d),
      QuadraticChartComplexity c₀ H A → 0 < r →
      ∀ w : ℝ × ℝ → ℂ, IsAdmissibleLocalKernel κ a₀ r w →
      ∀ ζ : ℝ → ℂ, Measurable ζ → (∀ u, ‖ζ u‖ ≤ H) → (∀ u v, ‖ζ v - ζ u‖ ≤ H * |v - u|) →
      (∀ u, ζ u ≠ 0 → |u| ≤ R) → 0 < δ → 0 < ε → ε ≤ 1 →
      (∀ s < δ, ∃ ξ : ℝ, s < ‖∫ u, (Real.fourierChar (-(u * ξ)) : ℂ) *
        (ζ u * quadraticChartAtom A (r * u))‖) →
      ∀ sa sb : ℝ, 1 ≤ |sb - sa| → |sa| ≤ 3 →
      let X := 1 + Real.log H + Real.log (max 1 δ⁻¹) + Real.log ε⁻¹
      ∃ (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ) (α β : ι' → ℝ),
        (Fintype.card ι' : ℝ) ≤ Real.exp (D * X ^ D) ∧
        (∑ ν, ‖c ν‖) ≤ Real.exp (D * X ^ D) ∧
        ∀ ya yb : ℝ, ya ∈ Set.Icc a₀ (a₀ + r) → yb ∈ Set.Icc a₀ (a₀ + r) →
          ‖w (ya - sa * ((yb - ya) / (sb - sa)), (yb - ya) / (sb - sa)) *
              quadraticChartAtom A ((yb - ya) / (sb - sa)) -
            ∑ ν, c ν * (Real.fourierChar (α ν * ya) : ℂ) *
              (Real.fourierChar (β ν * yb) : ℂ)‖ ≤ ε := by
  obtain ⟨Dp, hDp, DJp, hph⟩ := separatedPhase c₀ hc R (by linarith)
  set LJ := DJp 1 with hLJ
  set s0 := localKernelSupBound κ with hs0
  set Ct := chirpTailClassConst κ with hCt
  set Cc := chirpClassConst κ with hCc
  set Cκ := 5 * (4 * s0 + 1) + 5 * (16 * Ct + 1) + 8 * Cc + 2 with hCκ
  set e : ℕ := max Dp LJ with he
  set cW : ℕ := ⌈Real.log Cκ⌉₊ + Dp + LJ + 1 with hcW
  refine ⟨11 * cW + e + 1, by omega, ?_⟩
  intro d H δ ε r a₀ A hA hr w hw ζ hζm hζ hζL hζs hδ hε hε1 hsup sa sb hab hsa X
  obtain ⟨M, -, hlam, ι, hι, σ, hcard, -, a, hexp, hsumm, htot, hJ⟩ :=
    hph H δ r A hA hr ζ hζm hζ hζL hζs hδ hsup
  set Xp := 1 + Real.log H + Real.log (max 1 δ⁻¹) with hXp
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hA.lower
  have hlogδ : 0 ≤ Real.log (max 1 δ⁻¹) := Real.log_nonneg (le_max_left _ _)
  have hε' : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
  have hlogε : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg hε'
  have hXpX : Xp ≤ X := by simp only [X, Xp]; linarith
  have hXp3 : 3 ≤ Xp := by simp only [Xp]; linarith
  have hX1 : 1 ≤ X := by linarith
  have hpow (k : ℕ) : Xp ^ k ≤ X ^ k := pow_le_pow_left₀ (by linarith) hXpX k
  set! E1 := Real.exp (Dp * X ^ Dp) with hE1
  set! EJ := Real.exp (LJ * X ^ LJ) with hEJ
  have hE1' : ∀ y, y ≤ Real.exp (Dp * Xp ^ Dp) → y ≤ E1 := fun y hy =>
    hy.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hpow Dp) (Nat.cast_nonneg _)))
  have hEJ' : ∀ y, y ≤ Real.exp (LJ * Xp ^ LJ) → y ≤ EJ := fun y hy =>
    hy.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hpow LJ) (Nat.cast_nonneg _)))
  have hE11 : 1 ≤ E1 := Real.one_le_exp (by positivity)
  have hEJ1 : 1 ≤ EJ := Real.one_le_exp (by positivity)
  -- the quadratic phase and the time-chart expansion on the window
  set lam := A.quadratic + ∑ i, ∑ j, A.horizontal i * (M i j : ℝ) * A.horizontal j with hlamd
  set! Λ := lam * r ^ 2 with hΛ
  have hΛE : |Λ| ≤ E1 := by
    rw [hΛ, abs_mul, abs_of_nonneg (sq_nonneg r)]; exact hE1' _ hlam
  set! γ : ι × (Fin (d + d) → ℤ) → ℝ := fun p =>
    A.linear + ∑ i, (σ p i : ℝ) * A.horizontal i with hγ
  have hQ : ∀ t : ℝ, |t| ≤ r → HasSum (fun p => a p * (Real.fourierChar (γ p * t) : ℂ))
      ((Real.fourierChar (-(Λ * (t / r) ^ 2)) : ℂ) * quadraticChartAtom A t) := by
    intro t ht
    have h := (hexp t (by nlinarith only [hR, hr,
        ht])).mul_left (Real.fourierChar (A.linear * t) : ℂ)
    convert h using 1
    · funext p
      simp only [hγ]
      rw [add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
    · rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      rw [hΛ]; field_simp; ring
  have hshell : ∀ T : ℝ, 1 ≤ T →
      (∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖) * T ≤ EJ := by
    intro T hT
    have h := (hJ 1).2 T hT
    have hTT : T ≤ T ^ (1 * (d + 1) ^ 2) := le_self_pow₀ hT (by positivity)
    have h0 : 0 ≤ ∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    exact hEJ' _ ((mul_le_mul_of_nonneg_left hTT h0).trans h)
  -- truncation levels
  have hs00 : 0 ≤ s0 := localKernelSupBound_nonneg κ
  have hCt0 : 0 ≤ Ct := chirpTailClassConst_nonneg κ
  have hCc1 : 1 ≤ Cc := chirpClassConst_pos κ
  have hA0 : 0 ≤ ∑' p, ‖a p‖ := tsum_nonneg fun _ => norm_nonneg _
  have htotE : (∑' p, ‖a p‖) ≤ E1 := hE1' _ htot
  have hΛ1 : 1 + |Λ| ≤ 2 * E1 := by linarith
  set! Y₁ := 4 * s0 * EJ / ε + 1 with hY₁
  set! Y₂ := 2 * (∑' p, ‖a p‖) * (Ct * (1 + |Λ|) ^ 3) / ε + 1 with hY₂
  have hY₁1 : 1 ≤ Y₁ := by
    have : 0 ≤ 4 * s0 * EJ / ε := by positivity
    linarith
  have hY₂1 : 1 ≤ Y₂ := by
    have : 0 ≤ 2 * (∑' p, ‖a p‖) * (Ct * (1 + |Λ|) ^ 3) / ε := by positivity
    linarith only [this]
  obtain ⟨K₁, hK₁, hK₁'⟩ := exists_two_pow_between hY₁1
  obtain ⟨K₂, hK₂, hK₂'⟩ := exists_two_pow_between hY₂1
  set! S := (Finset.univ : Finset ι) ×ˢ frequencyBox (d + d) (2 ^ K₁) with hS
  set! V := frequencyBox 2 (2 ^ K₂) with hV
  set! cWc := periodicFourierCoeff (cubePeriodization (chirpedKernelRescale a₀ r Λ w) 16)
    with hcWc
  obtain ⟨hcWs, hcWt⟩ := chirpedKernel_coeff_mass hr hw Λ
  set! c₀ := a₀ + r / 2 with hc₀
  set! gg : ι × (Fin (d + d) → ℤ) → (Fin 2 → ℤ) → ℝ := fun p v =>
    ((v 1 : ℝ) - sa * v 0) / (16 * r) + γ p with hgg
  -- the quasipolynomial base
  set! W := Cκ * E1 * EJ * ε⁻¹ with hW
  have hCκ2 : 2 ≤ Cκ := by
    rw [hCκ]
    have : 0 ≤ 5 * (4 * s0 + 1) + 5 * (16 * Ct + 1) + 8 * Cc := by positivity
    linarith
  have hW1 : 1 ≤ W := by
    rw [hW]
    have h1 : 1 ≤ Cκ * E1 := one_le_mul_of_one_le_of_one_le (by linarith) hE11
    have h2 : 1 ≤ Cκ * E1 * EJ := one_le_mul_of_one_le_of_one_le h1 hEJ1
    exact one_le_mul_of_one_le_of_one_le h2 hε'
  have he1 : 1 ≤ e := le_trans hDp (le_max_left _ _)
  have hXe (k : ℕ) (hk : k ≤ e) : X ^ k ≤ X ^ e := pow_le_pow_right₀ hX1 hk
  have hlogW : Real.log W ≤ cW * X ^ e := by
    rw [hW, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), hE1, hEJ, Real.log_exp,
      Real.log_exp]
    have h1 : Real.log Cκ ≤ ⌈Real.log Cκ⌉₊ * X ^ e := by
      have hle := Nat.le_ceil (Real.log Cκ)
      have : (1 : ℝ) ≤ X ^ e := one_le_pow₀ hX1
      have h0 : (0 : ℝ) ≤ ⌈Real.log Cκ⌉₊ := Nat.cast_nonneg _
      nlinarith only [hle, this]
    have h2 : (Dp : ℝ) * X ^ Dp ≤ Dp * X ^ e :=
      mul_le_mul_of_nonneg_left (hXe Dp (le_max_left _ _)) (Nat.cast_nonneg _)
    have h3 : (LJ : ℝ) * X ^ LJ ≤ LJ * X ^ e :=
      mul_le_mul_of_nonneg_left (hXe LJ (le_max_right _ _)) (Nat.cast_nonneg _)
    have h4 : Real.log ε⁻¹ ≤ X ^ e := by
      have : Real.log ε⁻¹ ≤ X := by simp only [X]; linarith only [hlogH, hlogδ]
      exact this.trans (by simpa using hXe 1 he1)
    rw [hcW]; push_cast; linarith only [h1, h2, h3, h4]
  have hdX : (d : ℝ) ≤ X := by have := hA.dimension; simp only [X]; linarith
  have hιW : (Fintype.card ι : ℝ) ≤ W := (hE1' _ hcard).trans (by
    rw [hW]
    have h1 : E1 ≤ Cκ * E1 := le_mul_of_one_le_left (by linarith) (by linarith)
    have h2 : Cκ * E1 ≤ Cκ * E1 * EJ := le_mul_of_one_le_right (by positivity) hEJ1
    have h3 : Cκ * E1 * EJ ≤ Cκ * E1 * EJ * ε⁻¹ := le_mul_of_one_le_right (by positivity) hε'
    linarith)
  have hK₁W : (2 * (2 : ℝ) ^ K₁ + 1) ≤ W := by
    rw [hW]; exact approx_budget_K₁ hs00 hEJ1 hε hε' hE11 (by rw [hCκ]; linarith) hK₁'
  have hK₂W : (2 * (2 : ℝ) ^ K₂ + 1) ≤ W ^ 4 := by
    rw [hW]
    exact approx_budget_K₂ htotE hCt0 (by have := abs_nonneg Λ; linarith) hΛ1 hε hε'
      hE11 hEJ1 (by rw [hCκ]; linarith) hK₂'
  have hmassW : E1 * (Cc * (1 + |Λ|) ^ 3) ≤ W ^ 4 := by
    rw [hW]
    exact approx_budget_mass (by linarith) (by have := abs_nonneg Λ; linarith) hΛ1 hε' hE11
      hEJ1 (by rw [hCκ]; linarith) (by linarith)
  have hcardS : (S.card : ℝ) = Fintype.card ι * (2 * 2 ^ K₁ + 1) ^ (d + d) := by
    rw [hS, Finset.card_product, card_frequencyBox]; push_cast; simp
  have hcardV : (V.card : ℝ) = (2 * 2 ^ K₂ + 1) ^ 2 := by
    rw [hV, card_frequencyBox]; push_cast; ring
  clear_value W S V
  refine ⟨↥S × ↥V, inferInstance,
    fun ν => a ν.1.1 * cWc ν.2.1 *
      (Real.fourierChar (-((ν.2.1 0 : ℝ) * c₀ / (16 * r))) : ℂ),
    fun ν => (ν.2.1 0 : ℝ) / (16 * r) - gg ν.1.1 ν.2.1 / (sb - sa),
    fun ν => gg ν.1.1 ν.2.1 / (sb - sa), ?_, ?_, ?_⟩
  · -- the number of terms
    have hcardle : (Fintype.card (↥S × ↥V) : ℝ) ≤ W ^ (2 * d + 9) := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]
      push_cast
      rw [hcardS, hcardV]
      have h1 : ((2 : ℝ) * 2 ^ K₁ + 1) ^ (d + d) ≤ W ^ (d + d) :=
        pow_le_pow_left₀ (by positivity) hK₁W _
      have h2 : ((2 : ℝ) * 2 ^ K₂ + 1) ^ 2 ≤ (W ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hK₂W _
      calc (Fintype.card ι : ℝ) * (2 * 2 ^ K₁ + 1) ^ (d + d) * (2 * 2 ^ K₂ + 1) ^ 2 ≤
          W * W ^ (d + d) * (W ^ 4) ^ 2 := by gcongr
        _ = W ^ (2 * d + 9) := by ring
    exact hcardle.trans (qp_power_bound hW1 hlogW hX1 (by push_cast; linarith))
  · -- the coefficient mass
    have e : ∀ ν : ↥S × ↥V, ‖a ν.1.1 * cWc ν.2.1 *
        (Real.fourierChar (-((ν.2.1 0 : ℝ) * c₀ / (16 * r))) : ℂ)‖ =
        ‖a ν.1.1‖ * ‖cWc ν.2.1‖ := fun ν => by
      rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    rw [Finset.sum_congr rfl (fun ν _ => e ν), Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum, Finset.sum_coe_sort S (fun p => ‖a p‖),
      Finset.sum_coe_sort V (fun v => ‖cWc v‖)]
    have h1 : ∑ p ∈ S, ‖a p‖ ≤ ∑' p, ‖a p‖ := hsumm.sum_le_tsum S (fun _ _ => norm_nonneg _)
    have h2 : ∑ v ∈ V, ‖cWc v‖ ≤ ∑' v, ‖cWc v‖ := hcWs.sum_le_tsum V (fun _ _ => norm_nonneg _)
    have h3 : (∑ p ∈ S, ‖a p‖) * ∑ v ∈ V, ‖cWc v‖ ≤ E1 * (Cc * (1 + |Λ|) ^ 3) :=
      mul_le_mul (h1.trans htotE) (h2.trans hcWt) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (by linarith)
    exact (h3.trans hmassW).trans (qp_power_bound hW1 hlogW hX1 (by push_cast; linarith))
  · intro ya yb hya hyb
    have h := kernel_product_approx hr hw Λ (quadraticChartAtom A) γ a hsumm hQ hshell hab hsa
      K₁ K₂ ya yb hya hyb
    have hba : sb - sa ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hab; norm_num at hab
    dsimp only at h
    rw [← hS, ← hV] at h
    rw [phase_split_sum S V (fun p v => a p * cWc v)
      (fun p v => (v 0 : ℝ) * ((ya - sa * ((yb - ya) / (sb - sa)) - (a₀ + r / 2)) / r / 16) +
        (v 1 : ℝ) * ((yb - ya) / (sb - sa) / r / 16) + γ p * ((yb - ya) / (sb - sa)))
      (fun p v => -((v 0 : ℝ) * c₀ / (16 * r)))
      (fun p v => (v 0 : ℝ) / (16 * r) - gg p v / (sb - sa))
      (fun p v => gg p v / (sb - sa)) ya yb (fun p v => by
        simp only [hgg, hc₀]; field_simp; ring)] at h
    have hb1 := trunc_error_le hε hK₁
    have hb2 := trunc_error_le' hA0 (chirpTailConst_le κ Λ) hε
      (show 2 * (∑' p, ‖a p‖) * (Ct * (1 + |Λ|) ^ 3) / ε + 1 ≤ 2 ^ K₂ from hK₂)
    exact h.trans (by linarith)

/-! ### Packaging lem:separation: coefficient tails of the separated pair -/

/-- Shell bounds with decay `T^{-q}` give the pooled tail `2E/2^{Kq}` past `2^K`. -/
theorem pooled_shell_tail_bound_pow {ι : Type*} [Fintype ι] {n q : ℕ} (hq : 1 ≤ q)
    (a : ι × (Fin n → ℤ) → ℂ) {E : ℝ}
    (hshell : ∀ T : ℝ, 1 ≤ T →
      (∑ f : ι, ∑ v ∈ frequencyShell n T, ‖a (f, v)‖) * T ^ q ≤ E) (K : ℕ) :
    Summable (fun p : ι × (Fin n → ℤ) =>
        ‖if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0‖) ∧
      (∑' p : ι × (Fin n → ℤ),
        ‖if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0‖) ≤
        2 * E / ((2 : ℝ) ^ K) ^ q := by
  classical
  set c : ι × (Fin n → ℤ) → ℂ := fun p =>
    if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0
  let s : ℕ → Finset (ι × (Fin n → ℤ)) := fun k =>
    Finset.univ ×ˢ frequencyShell n ((2 : ℝ) ^ (K + k))
  have hcover : ∀ p, c p ≠ 0 → ∃ k, p ∈ s k := by
    intro p hp
    have hcond : p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 := by
      by_contra h; exact hp (by simp [c, h])
    obtain ⟨k, hk⟩ := exists_mem_late_frequencyShell hcond.1 K hcond.2
    exact ⟨k, Finset.mem_product.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hE0 : 0 ≤ E := by
    have h := hshell 1 le_rfl
    have : 0 ≤ (∑ f : ι, ∑ v ∈ frequencyShell n 1, ‖a (f, v)‖) * (1 : ℝ) ^ q := by positivity
    linarith
  have hK1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hmass (k : ℕ) : ∑ p ∈ s k, ‖c p‖ ≤ E / ((2 : ℝ) ^ K) ^ q * (1 / 2) ^ k := by
    have hT : (1 : ℝ) ≤ 2 ^ (K + k) := one_le_pow₀ (by norm_num)
    have h1 : ∑ p ∈ s k, ‖c p‖ ≤ ∑ f : ι, ∑ v ∈ frequencyShell n ((2 : ℝ) ^ (K + k)),
        ‖a (f, v)‖ := by
      rw [Finset.sum_product]
      apply Finset.sum_le_sum; intro f _
      apply Finset.sum_le_sum; intro v _
      simp only [c]
      split_ifs <;> simp
    have h2 := hshell _ hT
    have hpos : (0 : ℝ) < (2 ^ (K + k)) ^ q := by positivity
    have hq2 : ((2 : ℝ) ^ K) ^ q * 2 ^ k ≤ ((2 : ℝ) ^ (K + k)) ^ q := by
      rw [pow_add, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (2 : ℝ) ^ k = (2 ^ k) ^ 1 := (pow_one _).symm
        _ ≤ (2 ^ k) ^ q := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hq
    have h3 : ∑ p ∈ s k, ‖c p‖ ≤ E / ((2 : ℝ) ^ (K + k)) ^ q := by
      rw [le_div_iff₀ hpos]; exact (mul_le_mul_of_nonneg_right h1 hpos.le).trans h2
    refine h3.trans ?_
    calc E / ((2 : ℝ) ^ (K + k)) ^ q ≤ E / (((2 : ℝ) ^ K) ^ q * 2 ^ k) :=
          div_le_div_of_nonneg_left hE0 (by positivity) hq2
      _ = E / ((2 : ℝ) ^ K) ^ q * (1 / 2) ^ k := by rw [one_div_pow]; field_simp
  have hgeom : Summable (fun k : ℕ => E / ((2 : ℝ) ^ K) ^ q * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_two).mul_left _
  have hm0 (k : ℕ) : 0 ≤ ∑ p ∈ s k, ‖c p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsumm : Summable (fun k => ∑ p ∈ s k, ‖c p‖) :=
    Summable.of_nonneg_of_le hm0 hmass hgeom
  obtain ⟨hs, ht⟩ := tsum_norm_le_shell_masses c s hcover hsumm
  refine ⟨hs, ht.trans ?_⟩
  calc ∑' k, ∑ p ∈ s k, ‖c p‖ ≤ ∑' k : ℕ, E / ((2 : ℝ) ^ K) ^ q * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum hmass hsumm hgeom
    _ = 2 * E / ((2 : ℝ) ^ K) ^ q := by
        rw [tsum_mul_left, tsum_geometric_two]; ring

/-- Tail mass past an arbitrary level `T ≥ 1` from shell bounds of decay `T^{-q}`. -/
theorem shell_tail_at {ι : Type*} [Fintype ι] {n q : ℕ} (hq : 1 ≤ q)
    (a : ι × (Fin n → ℤ) → ℂ) (ha : Summable (fun p => ‖a p‖)) {E M : ℝ}
    (hshell : ∀ T : ℝ, 1 ≤ T →
      (∑ f : ι, ∑ v ∈ frequencyShell n T, ‖a (f, v)‖) * T ^ q ≤ E)
    (hM : (∑' p, ‖a p‖) ≤ M) {T : ℝ} (hT : 1 ≤ T) :
    Summable (fun p => if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) ∧
      (∑' p, if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) ≤
        (2 ^ q * M + 2 ^ (q + 1) * E) / T ^ q := by
  have hle : ∀ p, (if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) ≤ ‖a p‖ := fun p => by
    split_ifs <;> simp
  have hnn : ∀ p, 0 ≤ (if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) := fun p => by
    split_ifs <;> simp
  have hs : Summable (fun p => if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) :=
    Summable.of_nonneg_of_le hnn hle ha
  refine ⟨hs, ?_⟩
  have hTq : 0 < T ^ q := by positivity
  have hM0 : 0 ≤ M := (tsum_nonneg fun _ => norm_nonneg _).trans hM
  have hE0 : 0 ≤ E := by
    have h := hshell 1 le_rfl
    have : 0 ≤ (∑ f : ι, ∑ v ∈ frequencyShell n 1, ‖a (f, v)‖) * (1 : ℝ) ^ q := by positivity
    linarith
  by_cases hT2 : T < 2
  · have h1 : (∑' p, if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) ≤ M :=
      (hs.tsum_le_tsum hle ha).trans hM
    refine h1.trans ?_
    rw [le_div_iff₀ hTq]
    have : T ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) hT2.le q
    have : 0 ≤ 2 ^ (q + 1) * E := by positivity
    nlinarith
  · push Not at hT2
    obtain ⟨K, hK1, hK2⟩ := exists_two_pow_between (Y := T / 2) (by linarith)
    obtain ⟨hps, hpt⟩ := pooled_shell_tail_bound_pow hq a hshell K
    have hle' : ∀ p, (if T ≤ 1 + frequencyLength p.2 then ‖a p‖ else 0) ≤
        ‖if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0‖ := by
      intro p
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; apply h2
        refine ⟨fun h0 => ?_, by linarith⟩
        rw [h0] at h1
        have : frequencyLength (0 : Fin n → ℤ) = 0 := by simp [frequencyLength]
        rw [this] at h1; linarith
      · simp
      · simp
    refine (hs.tsum_le_tsum hle' hps).trans (hpt.trans ?_)
    have hK0 : (0 : ℝ) < 2 ^ K := by positivity
    have hKT : T ^ q ≤ 2 ^ q * ((2 : ℝ) ^ K) ^ q := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) q
    rw [div_le_div_iff₀ (by positivity) hTq]
    have : 0 ≤ 2 ^ q * M * ((2 : ℝ) ^ K) ^ q := by positivity
    calc 2 * E * T ^ q ≤ 2 * E * (2 ^ q * ((2 : ℝ) ^ K) ^ q) :=
          mul_le_mul_of_nonneg_left hKT (by positivity)
      _ = 2 ^ (q + 1) * E * ((2 : ℝ) ^ K) ^ q := by ring
      _ ≤ (2 ^ q * M + 2 ^ (q + 1) * E) * ((2 : ℝ) ^ K) ^ q := by nlinarith only [hTq, hM0, hKT]

/-- Mass and tail of a product of two coefficient families. -/
theorem product_family_tail {α β : Type*} (f : α → ℂ) (g : β → ℂ)
    (hf : Summable (fun x => ‖f x‖)) (hg : Summable (fun y => ‖g y‖))
    (sf : α → ℝ) (sg : β → ℝ) (T : ℝ)
    (htf : Summable (fun x => if T ≤ sf x then ‖f x‖ else 0))
    (htg : Summable (fun y => if T ≤ sg y then ‖g y‖ else 0)) :
    Summable (fun z : α × β => ‖f z.1 * g z.2‖) ∧
      (∑' z : α × β, ‖f z.1 * g z.2‖) = (∑' x, ‖f x‖) * ∑' y, ‖g y‖ ∧
      (∑' z : α × β, if T ≤ max (sf z.1) (sg z.2) then ‖f z.1 * g z.2‖ else 0) ≤
        (∑' x, if T ≤ sf x then ‖f x‖ else 0) * (∑' y, ‖g y‖) +
          (∑' x, ‖f x‖) * ∑' y, if T ≤ sg y then ‖g y‖ else 0 := by
  have hnf : ∀ x, 0 ≤ ‖f x‖ := fun _ => norm_nonneg _
  have hng : ∀ y, 0 ≤ ‖g y‖ := fun _ => norm_nonneg _
  have hprod : Summable (fun z : α × β => ‖f z.1‖ * ‖g z.2‖) :=
    Summable.mul_of_nonneg hf hg hnf hng
  have e1 : (fun z : α × β => ‖f z.1 * g z.2‖) = fun z => ‖f z.1‖ * ‖g z.2‖ := by
    funext z; rw [norm_mul]
  have hmul (u : α → ℝ) (v : β → ℝ) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ y, 0 ≤ v y)
      (hu : Summable u) (hv : Summable v) :
      Summable (fun z : α × β => u z.1 * v z.2) ∧
        (∑' z : α × β, u z.1 * v z.2) = (∑' x, u x) * ∑' y, v y := by
    have hu' : Summable (fun x => ‖u x‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg (hu0 _)]
    have hv' : Summable (fun y => ‖v y‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg (hv0 _)]
    exact ⟨Summable.mul_of_nonneg hu hv hu0 hv0,
      (tsum_mul_tsum_of_summable_norm hu' hv').symm⟩
  have htf0 : ∀ x, 0 ≤ (if T ≤ sf x then ‖f x‖ else 0) := fun x => by split_ifs <;> simp
  have htg0 : ∀ y, 0 ≤ (if T ≤ sg y then ‖g y‖ else 0) := fun y => by split_ifs <;> simp
  obtain ⟨hs0, ht0⟩ := hmul _ _ hnf hng hf hg
  obtain ⟨hs1, ht1⟩ := hmul _ _ htf0 hng htf hg
  obtain ⟨hs2, ht2⟩ := hmul _ _ hnf htg0 hf htg
  refine ⟨by rw [e1]; exact hprod, by rw [e1]; exact ht0, ?_⟩
  have hpt : ∀ z : α × β, (if T ≤ max (sf z.1) (sg z.2) then ‖f z.1 * g z.2‖ else 0) ≤
      (if T ≤ sf z.1 then ‖f z.1‖ else 0) * ‖g z.2‖ +
        ‖f z.1‖ * (if T ≤ sg z.2 then ‖g z.2‖ else 0) := by
    intro z
    rw [norm_mul]
    by_cases h1 : T ≤ sf z.1
    · simp only [h1, ite_true]
      split_ifs <;> nlinarith only [hnf z.1, hng z.2, mul_nonneg (hnf z.1) (hng z.2)]
    · by_cases h2 : T ≤ sg z.2
      · simp only [h1, h2, ite_true, ite_false]
        split_ifs <;> nlinarith [hnf z.1, hng z.2, mul_nonneg (hnf z.1) (hng z.2)]
      · have : ¬ T ≤ max (sf z.1) (sg z.2) := by
          rw [le_max_iff]; push Not; exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
        simp only [h1, h2, this, ite_false]; simp only [zero_mul, mul_zero, add_zero, le_refl]
  have hnn : ∀ z : α × β, 0 ≤ (if T ≤ max (sf z.1) (sg z.2) then ‖f z.1 * g z.2‖ else 0) :=
    fun z => by split_ifs <;> positivity
  have hsum := hs1.add hs2
  calc (∑' z : α × β, if T ≤ max (sf z.1) (sg z.2) then ‖f z.1 * g z.2‖ else 0) ≤
      ∑' z : α × β, ((if T ≤ sf z.1 then ‖f z.1‖ else 0) * ‖g z.2‖ +
        ‖f z.1‖ * (if T ≤ sg z.2 then ‖g z.2‖ else 0)) :=
        (Summable.of_nonneg_of_le hnn hpt hsum).tsum_le_tsum hpt hsum
    _ = _ := by rw [hs1.tsum_add hs2, ht1, ht2]

theorem summable_prod_fintype_nonneg {ι β : Type*} [Fintype ι] {u : ι × β → ℝ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : ∀ i, Summable (fun b => u (i, b))) :
    Summable u ∧ (∑' z, u z) = ∑ i, ∑' b, u (i, b) := by
  have hs : Summable u :=
    (summable_prod_of_nonneg hu0).mpr ⟨hu, (hasSum_fintype _).summable⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, tsum_fintype]

theorem atom_family_budget {H E c : ℝ} {d Db : ℕ} (hH : Real.exp 2 ≤ H)
    (hdH : (d : ℝ) ≤ Real.log H) (hE0 : 0 ≤ E)
    (hE : E ≤ Real.exp (Db * (1 + Real.log H) ^ Db)) (hc0 : 0 ≤ c)
    (hc : c ≤ (95 * H) ^ d) :
    (2 ^ 100 + 2 ^ 101) * (c * (6 ^ d) ^ 3 * E) ≤
      Real.exp ((114 + Db : ℕ) * (1 + Real.log H) ^ (Db + 2)) := by
  set X := 1 + Real.log H with hX
  have hH1 : 1 ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlogH : 2 ≤ Real.log H := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hH
  have hX1 : 1 ≤ X := by linarith
  have hHX : Real.log H ≤ X := by linarith
  -- logarithms of the three factors
  have h1 : (2 : ℝ) ^ 100 + 2 ^ 101 ≤ Real.exp 102 := by
    have : (2 : ℝ) ^ 100 + 2 ^ 101 = 3 * 2 ^ 100 := by ring
    rw [this]
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : (2 : ℝ) ^ 100 ≤ Real.exp 100 := by
      have := pow_le_pow_left₀ (by norm_num) he 100
      rwa [← Real.exp_nat_mul, show ((100 : ℕ) : ℝ) * 1 = 100 by norm_num] at this
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc 3 * (2 : ℝ) ^ 100 ≤ Real.exp 2 * Real.exp 100 :=
          mul_le_mul h3 h2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp 102 := by rw [← Real.exp_add]; norm_num
  have hcm : c * (6 ^ d) ^ 3 ≤ Real.exp (12 * X ^ 2) := by
    have hb : c * ((6 : ℝ) ^ d) ^ 3 ≤ (20520 * H) ^ d := by
      have e6 : ((6 : ℝ) ^ d) ^ 3 = 216 ^ d := by
        rw [← pow_mul, mul_comm d 3, pow_mul]; norm_num
      calc c * ((6 : ℝ) ^ d) ^ 3 = c * 216 ^ d := by rw [e6]
        _ ≤ (95 * H) ^ d * 216 ^ d := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (20520 * H) ^ d := by rw [← mul_pow]; ring_nf
    refine hb.trans ?_
    rw [← Real.exp_log (pow_pos (by positivity : (0 : ℝ) < 20520 * H) d), Real.log_pow]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num) (by linarith)]
    have hl : Real.log 20520 ≤ 11 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have : (20520 : ℝ) ≤ Real.exp 1 ^ 11 := by
        have := Real.exp_one_gt_d9
        calc (20520 : ℝ) ≤ 2.7 ^ 11 := by norm_num
          _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) (by linarith) 11
      rwa [← Real.exp_nat_mul, show ((11 : ℕ) : ℝ) * 1 = 11 by norm_num] at this
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith only [hdH, hl]
  have hXe : X ^ 2 ≤ X ^ (Db + 2) := pow_le_pow_right₀ hX1 (by omega)
  have hXD : X ^ Db ≤ X ^ (Db + 2) := pow_le_pow_right₀ hX1 (by omega)
  have hX1' : X ≤ X ^ (Db + 2) := le_self_pow₀ hX1 (by omega)
  have hXp : (1 : ℝ) ≤ X ^ (Db + 2) := one_le_pow₀ hX1
  calc (2 ^ 100 + 2 ^ 101) * (c * (6 ^ d) ^ 3 * E) ≤
      Real.exp 102 * (Real.exp (12 * X ^ 2) * Real.exp (Db * X ^ Db)) := by
        gcongr
    _ = Real.exp (102 + 12 * X ^ 2 + Db * X ^ Db) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((114 + Db : ℕ) * X ^ (Db + 2)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have : (Db : ℝ) * X ^ Db ≤ Db * X ^ (Db + 2) :=
          mul_le_mul_of_nonneg_left hXD (Nat.cast_nonneg _)
        nlinarith only [hdH, hXe, hXD]

/-- The normalized coefficient family of one separated atom: total mass and tails
(lem:separation, line 1407), quasipolynomial in `H`. -/
theorem sepAtomFamily_bounds (c₀ : ℕ) (hc : 1 ≤ c₀) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1' : ∀ x, |ψ x| ≤ 1) (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {Kψ : ℕ} (hKψ : 1 ≤ Kψ)
    (hψd : ∀ i x, |iteratedDeriv i ψ x| ≤ ((Kψ : ℝ) * (i + 1 : ℝ)) ^ (Kψ * (i + 1)))
    {Kρ : ℕ} (hKρ : 1 ≤ Kρ)
    (hρd : ∀ n x, |iteratedDeriv n gevreyPartition x| ≤
      ((Kρ : ℝ) * ((n : ℝ) + 1)) ^ (Kρ * (n + 1))) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), 1 ≤ d →
      QuadraticChartComplexity c₀ H A → ∀ i a b : ℤ, |i| ≤ 3 → |a| ≤ 3 → |b| ≤ 3 →
      let Ki := slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊
      let Kb := slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
      let f : (Ki × Kb) × (Fin (d + d + d) → ℤ) → ℂ := fun q =>
        sepCoeff A.amplitude ψ i a b q.1.1 q.1.2 q.2 * ((6 ^ d : ℝ) : ℂ) ^ 3
      Summable (fun q => ‖f q‖) ∧
        (∑' q, ‖f q‖) ≤ Real.exp (D * (1 + Real.log H) ^ D) ∧
        ∀ T : ℝ, 1 ≤ T →
          Summable (fun q => if T ≤ 1 + frequencyLength q.2 then ‖f q‖ else 0) ∧
          (∑' q, if T ≤ 1 + frequencyLength q.2 then ‖f q‖ else 0) ≤
            Real.exp (D * (1 + Real.log H) ^ D) / T ^ 100 := by
  obtain ⟨Db, hDb, hbud⟩ := sepCoeff_budget c₀ Kψ Kρ 100 6
  refine ⟨114 + Db, by omega, ?_⟩
  intro d H A hd hA i a b hi ha hb Ki Kb f
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hia : |((i - a : ℤ) : ℝ)| ≤ 6 := by
    push_cast; have := abs_sub (i : ℝ) a
    have h1 : |(i : ℝ)| ≤ 3 := by exact_mod_cast hi
    have h2 : |(a : ℝ)| ≤ 3 := by exact_mod_cast ha
    linarith
  have hba : |((b - a : ℤ) : ℝ)| ≤ 6 := by
    push_cast; have := abs_sub (b : ℝ) a
    have h1 : |(b : ℝ)| ≤ 3 := by exact_mod_cast hb
    have h2 : |(a : ℝ)| ≤ 3 := by exact_mod_cast ha
    linarith
  obtain ⟨hbs, hbt⟩ := hbud (d := d) (H := H) (i := i) (a := a) (b := b) hd hA.lower
    hA.dimension (by exact_mod_cast hia) (by exact_mod_cast hba)
  set E := Real.exp (Db * (1 + Real.log H) ^ Db) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set! m6 : ℝ := ((6 : ℝ) ^ d) ^ 3 with hm6
  have hm60 : 0 ≤ m6 := by positivity
  have hfn : ∀ q, ‖f q‖ = m6 * ‖sepCoeff A.amplitude ψ i a b q.1.1 q.1.2 q.2‖ := fun q => by
    simp only [f, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hm6]
    ring
  have hone (ki : Ki) (kb : Kb) := sepCoeff_shell_bounds hd hA hc hψ hψ1' hψ1 hψ0 hKψ hψd hKρ
    hρd i a b ki kb
  -- per-slow-value bounds
  have hsl (ki : Ki) (kb : Kb) : Summable (fun p => ‖sepCoeff A.amplitude ψ i a b ki kb p‖) :=
    (hone ki kb).1
  have htl (ki : Ki) (kb : Kb) : (∑' p, ‖sepCoeff A.amplitude ψ i a b ki kb p‖) ≤ E :=
    (hone ki kb).2.2.trans hbt
  have hshl (ki : Ki) (kb : Kb) (T : ℝ) (hT : 1 ≤ T) :
      (∑ v ∈ frequencyShell (d + d + d) T, ‖sepCoeff A.amplitude ψ i a b ki kb v‖) * T ^ 100 ≤
        E := ((hone ki kb).2.1 100 T hT).trans hbs
  -- the family over the finite slow values
  have hfam := summable_prod_fintype_nonneg (u := fun q => ‖f q‖) (fun _ => norm_nonneg _)
    (fun ikb => by
      simp_rw [hfn]; exact (hsl ikb.1 ikb.2).mul_left m6)
  obtain ⟨hfs, hft⟩ := hfam
  set! card : ℝ := (Fintype.card (↥Ki × ↥Kb) : ℝ) with hcard
  have hcard0 : 0 ≤ card := Nat.cast_nonneg _
  have htot : (∑' q, ‖f q‖) ≤ card * m6 * E := by
    rw [hft]
    calc ∑ ikb : ↥Ki × ↥Kb, ∑' p, ‖f (ikb, p)‖ ≤ ∑ _ikb : ↥Ki × ↥Kb, m6 * E := by
          apply Finset.sum_le_sum; intro ikb _
          simp_rw [hfn]
          rw [tsum_mul_left]
          exact mul_le_mul_of_nonneg_left (htl ikb.1 ikb.2) hm60
      _ = card * m6 * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hshell : ∀ T : ℝ, 1 ≤ T →
      (∑ ikb : ↥Ki × ↥Kb, ∑ v ∈ frequencyShell (d + d + d) T, ‖f (ikb, v)‖) * T ^ 100 ≤
        card * m6 * E := by
    intro T hT
    rw [Finset.sum_mul]
    calc ∑ ikb : ↥Ki × ↥Kb, (∑ v ∈ frequencyShell (d + d + d) T, ‖f (ikb, v)‖) * T ^ 100 ≤
        ∑ _ikb : ↥Ki × ↥Kb, m6 * E := by
          apply Finset.sum_le_sum; intro ikb _
          simp_rw [hfn]
          rw [← Finset.mul_sum, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hshl ikb.1 ikb.2 T hT) hm60
      _ = card * m6 * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- the number of slow values
  have hcardH : card ≤ (95 * H) ^ d := by
    have hK1 : (⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊ : ℝ) ≤ H + 8 := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ H + 1 + |((i - a : ℤ) : ℝ)| by positivity)
      linarith
    have hK2 : (⌈2 + |((b - a : ℤ) : ℝ)|⌉₊ : ℝ) ≤ 9 := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 + |((b - a : ℤ) : ℝ)| by positivity)
      linarith
    have hH7 : 7 ≤ H := by
      have he := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have : (7 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith only [he]
      linarith [hA.lower]
    rw [hcard, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, slowValueBox_card,
      slowValueBox_card]
    push_cast at hK1 hK2 ⊢
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hH7, hK1, hK2]
  have hbig := atom_family_budget (c := card) (E := E) hA.lower hA.dimension hE0 hE.le hcard0 hcardH
  have hX1 : 1 ≤ 1 + Real.log H := by
    have := Real.log_nonneg hH1; linarith
  have hfin : Real.exp (((114 + Db : ℕ) : ℝ) * (1 + Real.log H) ^ (Db + 2)) ≤
      Real.exp (((114 + Db : ℕ) : ℝ) * (1 + Real.log H) ^ (114 + Db)) :=
    exp_poly_le hX1 (by omega) le_rfl
  have hm0 : 0 ≤ card * m6 * E := by positivity
  refine ⟨hfs, ?_, fun T hT => ?_⟩
  · refine htot.trans (le_trans ?_ (hbig.trans hfin))
    have : (1 : ℝ) ≤ 2 ^ 100 + 2 ^ 101 := by norm_num
    nlinarith only [hm0]
  · obtain ⟨hs, ht⟩ := shell_tail_at (n := d + d + d) (q := 100) (by norm_num) f hfs hshell htot hT
    refine ⟨hs, ht.trans ?_⟩
    have hT0 : 0 < T ^ 100 := by positivity
    apply div_le_div_of_nonneg_right _ hT0.le
    refine le_trans (le_of_eq (by ring)) (hbig.trans hfin)

theorem sepQ_le {i a b : ℤ} (hi : |i| ≤ 3) (ha : |a| ≤ 3) (hb : |b| ≤ 3) : sepQ i a b ≤ 55 := by
  have hi' : |(i : ℝ)| ≤ 3 := by exact_mod_cast hi
  have ha' : |(a : ℝ)| ≤ 3 := by exact_mod_cast ha
  have hb' : |(b : ℝ)| ≤ 3 := by exact_mod_cast hb
  unfold sepQ
  push_cast
  have h1 := abs_sub (i : ℝ) b
  have h2 := abs_sub (a : ℝ) i
  have h3 := abs_sub (b : ℝ) a
  have h4 : |((i : ℝ) - a) * (i - b)| ≤ 36 := by
    rw [abs_mul]
    have e1 : |(i : ℝ) - a| ≤ 6 := by have := abs_sub (i : ℝ) a; linarith
    have e2 : |(i : ℝ) - b| ≤ 6 := by linarith
    calc |(i : ℝ) - a| * |(i : ℝ) - b| ≤ 6 * 6 := mul_le_mul e1 e2 (abs_nonneg _) (by norm_num)
      _ = 36 := by norm_num
  linarith

theorem sum_abs_le_card_mul_length {n : ℕ} (p : Fin n → ℤ) :
    ∑ l, |(p l : ℝ)| ≤ n * frequencyLength p := by
  calc ∑ l, |(p l : ℝ)| ≤ ∑ _l : Fin n, frequencyLength p :=
        Finset.sum_le_sum fun l _ => abs_frequency_coordinate_le p l
    _ = n * frequencyLength p := by simp

/-- The slow-value boxes of one separated atom have at most `(95 H)^d` elements. -/
theorem slowBox_pair_card_le {d : ℕ} {H : ℝ} (hH7 : 7 ≤ H) (i a b : ℤ) (hi : |i| ≤ 3)
    (ha : |a| ≤ 3) (hb : |b| ≤ 3) :
    (Fintype.card (↥(slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊) ×
      ↥(slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊)) : ℝ) ≤ (95 * H) ^ d := by
  have hia : |((i - a : ℤ) : ℝ)| ≤ 6 := by
    have : |i - a| ≤ 6 := (abs_sub _ _).trans (by linarith)
    exact_mod_cast this
  have hba : |((b - a : ℤ) : ℝ)| ≤ 6 := by
    have : |b - a| ≤ 6 := (abs_sub _ _).trans (by linarith)
    exact_mod_cast this
  have hK1 : (⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊ : ℝ) ≤ H + 8 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ H + 1 + |((i - a : ℤ) : ℝ)| by positivity)
    linarith
  have hK2 : (⌈2 + |((b - a : ℤ) : ℝ)|⌉₊ : ℝ) ≤ 9 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 + |((b - a : ℤ) : ℝ)| by positivity)
    linarith
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, slowValueBox_card,
    slowValueBox_card]
  push_cast at hK1 hK2 ⊢
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-- The slow-value count of one separated atom is quasi-polynomial. -/
theorem slowBox_pair_card_exp_le {d : ℕ} {H : ℝ} (hH7 : 7 ≤ H) (hd : (d : ℝ) ≤ Real.log H)
    (i a b : ℤ) (hi : |i| ≤ 3) (ha : |a| ≤ 3) (hb : |b| ≤ 3) :
    (Fintype.card (↥(slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊) ×
      ↥(slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊)) : ℝ) ≤
      Real.exp (5 * (1 + Real.log H) ^ 2) := by
  refine (slowBox_pair_card_le hH7 i a b hi ha hb).trans ?_
  have hH0 : 0 < H := by linarith
  have hl : Real.log (95 * H) ≤ 5 * (1 + Real.log H) := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    have h95 : Real.log 95 ≤ 5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [h5]
      calc (95 : ℝ) ≤ 2.7 ^ 5 := by norm_num
        _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h27 5
    have := Real.log_nonneg (show (1 : ℝ) ≤ H by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (95 * H) := Real.log_nonneg (by linarith)
  have hlH : 0 ≤ Real.log H := Real.log_nonneg (show (1 : ℝ) ≤ H by linarith)
  calc (95 * H) ^ d = Real.exp (d * Real.log (95 * H)) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ ≤ Real.exp ((1 + Real.log H) * (5 * (1 + Real.log H))) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul (by linarith) hl hlog0 (by linarith)
    _ = Real.exp (5 * (1 + Real.log H) ^ 2) := by congr 1; ring



end TrilinearHT.Auto
end
