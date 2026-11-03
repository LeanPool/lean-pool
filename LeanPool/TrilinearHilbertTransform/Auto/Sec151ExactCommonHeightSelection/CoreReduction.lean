/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec151ExactCommonHeightSelection.Setup

/-!
# Trilinear Hilbert transform: core_reduction
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

open scoped Classical in
private def CoreReductionHrvStatement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (qG : bf.Grp → ℕ)
    (S : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp)
    (cc : ℕ)
    (kk : ℝ)
    (Vl : Fin (4 : ℕ) → ℝ)
    (C : Finset (ℤ × ℤ))
    (ρ₂ : ℝ),
  let G0 : ℝ :=
    Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * kk)) ^ (2 : ℕ))
  let a : Fin (4 : ℕ) → ℤ × ℤ → ℝ :=
    fun l I => if D.u = some l then 0 else ∑ G ∈ gs I, (‖columnL2Restriction
      (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G
      I.1)‖ ^ 2 + ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ 2) /
      dyadicGridLength A.G I.1
  ∀ (_ : a = fun (l : Fin (4 : ℕ)) (I : ℤ × ℤ) => if D.u = some l then (0 : ℝ) else ∑ G ∈ gs
      I, (‖(columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable
      A.G I.1 I.2) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin
      fp.Mc))) (D.roll l G I.1)‖ ^ (2 : ℕ) + ‖(columnL2Restriction (dyadicGridCell A.G
      I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2) : ↥(ColumnL2 (bf.Lab ⊕ Fin
      fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ (2 :
      ℕ)) / dyadicGridLength A.G I.1)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ S, (0 : ℝ) ≤ a l I),
  let Bv : Fin (4 : ℕ) → ℝ :=
    fun (l : Fin (4 : ℕ)) => if D.u = some l then (0 : ℝ) else (↑D.S.K : ℝ) * ((20 : ℝ)
      * G0 + (32 : ℝ)) + (↑D.S.K : ℝ) * Vl l
  ∀ (C₂ : Finset (ℤ × ℤ))
    (_ : ∀ (v : Fin (4 : ℕ)) (x : ℝ), ∑ I ∈ {I ∈ S | ¬∃ c ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G c.1 c.2} with x ∈ dyadicGridCell A.G I.1 I.2, a v I ≤ (∑ v :
      Fin (4 : ℕ), Bv v) / ρ₂),
  let T₂ : ℝ :=
    D.T2 cc kk Vl ρ₂
  let S₁ : Finset (ℤ × ℤ) :=
    {I ∈ S | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2}
  let S₂ : Finset (ℤ × ℤ) :=
    {I ∈ S₁ | ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S₂ ⊆ S₁)
    (_ : S₁ ⊆ S),
  ∀ I ∈ S₂, ∀ G ∈ gs I, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → ‖(columnL2Restriction
    (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2) : ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (D.roll l G I.1)‖ ≤ √T₂
    * √(dyadicGridLength A.G I.1) ∧ ‖(columnL2Restriction (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) →
    ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) ((D.withQ0 (qG G)).pV l G I.1)‖ ≤ √T₂ *
    √(dyadicGridLength A.G I.1)




private theorem core_reduction_hrv : CoreReductionHrvStatement := by
  classical
  intro κ' c₀ A bf fp D qG S gs cc kk Vl C ρ₂ G0 a ha_def ha Bv C₂ hcap₂ T₂ S₁ S₂ hS₂₁ hS₁ I hI G
    hG l hl
  have hr := dyadicGridLength_pos A.G I.1
  have hIS := hS₁ (hS₂₁ hI)
  have hIC₂ := (Finset.mem_filter.mp hI).2
  have hIx := dyadicGridCell_left_mem A.G I.1 I.2
  have haI : a l I ≤ T₂ := by
    refine le_trans ?_ (hcap₂ l (dyadicGridLeft A.G I.1 I.2))
    exact Finset.single_le_sum (f := a l) (fun J hJ => ha l J
      (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1)
      (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS, hIC₂⟩, hIx⟩)
  set x := ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G I.1)‖
  set y := ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖
  have hxy : (x ^ 2 + y ^ 2) / dyadicGridLength A.G I.1 ≤ T₂ := by
    refine le_trans ?_ haI
    simp only [ha_def, hl, ↓reduceIte]
    exact Finset.single_le_sum (f := fun G => (‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G I.1)‖ ^ 2 +
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ 2) /
      dyadicGridLength A.G I.1) (fun G _ => div_nonneg (by positivity) hr.le) hG
  have hb : ∀ z : ℝ, 0 ≤ z → z ^ 2 ≤ T₂ * dyadicGridLength A.G I.1 →
      z ≤ Real.sqrt T₂ * Real.sqrt (dyadicGridLength A.G I.1) := fun z hz hz2 => by
    have hT0 : 0 ≤ T₂ := le_trans (div_nonneg (by positivity) hr.le) hxy
    rw [← Real.sqrt_mul hT0, ← Real.sqrt_sq hz]
    exact Real.sqrt_le_sqrt hz2
  rw [div_le_iff₀ hr] at hxy
  exact ⟨hb x (norm_nonneg _) (by nlinarith only [sq_nonneg y, hxy]),
    hb y (norm_nonneg _) (by nlinarith only [sq_nonneg x, hxy])⟩
-- the retained sizes


open Classical in
/-- Blueprint line 2461, the reduction of the core terms on the side states. Take the cut family
`C` of the side estimate (two-side bound `B₂`, side cap `T_c`, three-side power bound `B₃(B_c)` on
retained cells with cores of normalized size `B_c`) and a second cut `C₂` of root fraction at most
`ρ₂` for the integrated budgets of the rolling sides (`eq:variation`) and the linear sides
(`eq:linear-energy`). On the cells retained by both, the cores, errors and sides have the `P^C`
retained sizes `coreBd`, `errBd` and `√T_c` (the lift is pointwise bounded), and the weighted
active minimum of the whole leaf outputs is at most `B₂`, `82` times the error patterns (bounded by
`eq:physical-error`, the active multiplicity `M` and Cauchy-Schwarz), `82 B₃` and the weighted
active minimum of the patterns with at least three cores. A basic `U` role remains a side. -/
theorem core_reduction (qG : bf.Grp → ℕ) (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (k Bn : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    (huse : ∀ I ∈ S, ∀ G ∈ gs I, fp.ActualUse G I) (hBn : ∀ I ∈ S, (D.toLeafQ qG).bk I < Bn)
    (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : Fin 4 → ℝ}
    (hlin : ∀ l, D.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide
        (D.S.withQ0 (qG G))
        D.hA D.SP (A.R.1 + ((D.S.K * β : ℕ) : ℤ))
          (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
          (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤
        Vl l * dyadicGridLength A.G A.R.1)
    (hrep : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l, D.u ≠ some l → (D.withQ0 (qG G)).RepAt L l G I)
    {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖(D.toLeafQ qG).out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    -- the outputs of the side estimate on its cut family `C`
    (C : Finset (ℤ × ℤ)) {η : ℝ} (hη : 0 ≤ η) {B₂ Tc : ℝ}
    (htwo : ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I
            (fun l => if σ l = 0 then (D.toLeafQ qG).out l G I else (D.toLeafQ qG).sv l G I)‖ ≤ B₂)
    (hcap : ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, (D.toLeafQ qG).s2 G I ≤ Tc)
    {B₃ : ℝ → ℝ}
    (hthree : ∀ (core err : ℤ × ℤ → bf.Grp → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
        (S' : Finset (ℤ × ℤ)), S' ⊆ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∀ {Bc : ℝ}, 0 ≤ Bc →
        (∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
          ‖core I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength A.G I.1)) →
        ∑ I ∈ S', dyadicGridLength A.G I.1 * min η (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
            ‖∑ G ∈ gs I, fp.Λc I
              (patternPiece (core I G) (fun l => (D.toLeafQ qG).sv l G I) (err I G) σ)‖) ≤ B₃ Bc)
    -- the physical errors (`eq:physical-error`) and the active multiplicity
    {Ee M : ℝ} (hEe : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.withQ0 (qG G)).errAt L l G I‖ ^ 2 ≤ Ee)
    (hM : ∑ I ∈ S, dyadicGridLength A.G I.1 * (gs I).card ≤ M)
    {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) :
    ∃ C₂ : Finset (ℤ × ℤ), C₂ ⊆ S ∧ dyadicRootLength A.G C₂ ≤ ρ₂ * dyadicGridLength A.G A.R.1 ∧
      (∀ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        ∀ G ∈ gs I, ∀ l,
        ‖(D.withQ0 (qG G)).coreAt l G I‖ ≤ coreBd B₀ (D.T2 cc kk Vl ρ₂) * Real.sqrt
            (dyadicGridLength A.G I.1) ∧
        ‖(D.withQ0 (qG G)).errAt L l G I‖ ≤ errBd B₀ (D.T2 cc kk Vl ρ₂) * Real.sqrt
            (dyadicGridLength A.G I.1) ∧
        ‖(D.toLeafQ qG).sv l G I‖ ≤ Real.sqrt Tc * Real.sqrt (dyadicGridLength A.G I.1)) ∧
      ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ G ∈ gs I, fp.Λc I (fun l => (D.toLeafQ qG).out l G I)‖ ≤
      B₂ + 82 * (81 * (localFormUniformConstant κ' * (coreBd B₀ (D.T2 cc kk Vl ρ₂) +
          errBd B₀ (D.T2 cc kk Vl ρ₂) + Real.sqrt Tc) ^ 3) * (Real.sqrt (4 * M) * Real.sqrt Ee)) +
        82 * B₃ (coreBd B₀ (D.T2 cc kk Vl ρ₂)) +
        ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
            dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
            (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
          dyadicGridLength A.G I.1 * min η ‖∑ τ ∈ Finset.univ.filter
            (fun τ : Fin 4 → Fin 3 => (∀ l, τ l ≠ 2) ∧ 3 ≤ patternCount τ 0),
            ∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
              (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ :=
                  by
  set! G0 := Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2)
  -- the second cut for the rolling and linear sides
  set! a : Fin 4 → ℤ × ℤ → ℝ := fun l I => if D.u = some l then 0 else
    ∑ G ∈ gs I, (‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G I.1)‖ ^ 2 +
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ 2) /
      dyadicGridLength A.G I.1 with ha_def
  have ha : ∀ l, ∀ I ∈ S, 0 ≤ a l I := fun l I _ => by
    simp only [ha_def]
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun G _ => div_nonneg (by positivity)
        (dyadicGridLength_pos A.G I.1).le
  set! Bv : Fin 4 → ℝ := fun l => if D.u = some l then 0 else
    (D.S.K * (20 * G0 + 32) + D.S.K * Vl l) with hBv_def
  have hB : ∀ l, ∑ I ∈ S, dyadicGridLength A.G I.1 * a l I ≤ Bv l * dyadicGridLength A.G A.R.1 :=
    fun l => by
      by_cases hl : D.u = some l
      · simp [ha_def, hBv_def, hl]
      · simp only [ha_def, hBv_def, hl, ↓reduceIte]
        have h1 := D.roll_cell_energy qG hanc hne l S hS gs gset hgs k hcertS B hroot' hτ' hτ1 hHed
          hτN cc hc hk hDm hDb hLs
        have h2 := D.V_cell_energy qG l S hS gs gset hgs Bn hBn (hlin l hl)
        calc ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I,
              (‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
                (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G I.1)‖ ^ 2 +
              ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
                (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ 2) /
              dyadicGridLength A.G I.1
            = ∑ I ∈ S, ∑ G ∈ gs I, ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
                (dyadicGridCell_measurable A.G I.1 I.2) (D.roll l G I.1)‖ ^ 2 +
              ∑ I ∈ S, ∑ G ∈ gs I, ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
                (dyadicGridCell_measurable A.G I.1 I.2) ((D.withQ0 (qG G)).pV l G I.1)‖ ^ 2 := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun I _ => ?_
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun G _ => ?_
              field_simp [(dyadicGridLength_pos A.G I.1).ne']
          _ ≤ _ := by
              have : D.S.K * (20 * G0 + 32) * dyadicGridLength A.G A.R.1 +
                  D.S.K * (Vl l * dyadicGridLength A.G A.R.1) =
                  (D.S.K * (20 * G0 + 32) + D.S.K * Vl l) * dyadicGridLength A.G A.R.1 := by ring
              linarith
  obtain ⟨C₂, hC₂S, hlen₂, hcap₂⟩ := caps_cut A.G S A.R (fun I hI => A.sub I (hS hI)) a ha Bv hB
    hρ₂ hρ₂1
  have hT2 : (∑ v, Bv v) / ρ₂ = D.T2 cc kk Vl ρ₂ := rfl
  set T₂ := D.T2 cc kk Vl ρ₂
  set S₁ := S.filter (fun I => ¬ ∃ e ∈ C,
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)
  set! S₂ := S₁.filter (fun I => ¬ ∃ e ∈ C₂,
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)
  have hS₂₁ : S₂ ⊆ S₁ := Finset.filter_subset _ _
  have hS₁ : S₁ ⊆ S := Finset.filter_subset _ _
  -- the sides on retained cells (the side cap)
  have hsv : ∀ I ∈ S₁, ∀ G ∈ gs I, ∀ l,
      ‖(D.toLeafQ qG).sv l G I‖ ≤ Real.sqrt Tc * Real.sqrt (dyadicGridLength A.G I.1) := by
    intro I hI G hG l
    have hr := dyadicGridLength_pos A.G I.1
    have hIx := dyadicGridCell_left_mem A.G I.1 I.2
    have h1 : (D.toLeafQ qG).ns l G I ^ 2 ≤ Tc := by
      refine le_trans ?_ (hcap (dyadicGridLeft A.G I.1 I.2))
      refine le_trans ?_ (Finset.single_le_sum (f := fun I => ∑ G ∈ gs I, (D.toLeafQ qG).s2 G I)
        (fun J _ => Finset.sum_nonneg fun G _ => (D.toLeafQ qG).s2_nonneg G J)
        (Finset.mem_filter.mpr ⟨hI, hIx⟩))
      refine le_trans ?_ (Finset.single_le_sum (f := fun G => (D.toLeafQ qG).s2 G I)
        (fun G _ => (D.toLeafQ qG).s2_nonneg G I) hG)
      exact Finset.single_le_sum (f := fun l => (D.toLeafQ qG).ns l G I ^ 2) (fun l _ => sq_nonneg
          _)
        (Finset.mem_univ l)
    have h2 : (D.toLeafQ qG).ns l G I ≤ Real.sqrt Tc := by
      rw [← Real.sqrt_sq ((D.toLeafQ qG).ns_nonneg l G I)]
      exact Real.sqrt_le_sqrt h1
    have h3 : ‖(D.toLeafQ qG).sv l G I‖ = (D.toLeafQ qG).ns l G I * Real.sqrt (dyadicGridLength A.G
        I.1) := by
      unfold SideLeafM.ns
      rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr hr).ne']
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  -- the rolling and linear sides on retained cells (the second cut)
  have hrv : ∀ I ∈ S₂, ∀ G ∈ gs I, ∀ l, D.u ≠ some l →
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (D.roll l G I.1)‖ ≤ Real.sqrt T₂ * Real.sqrt (dyadicGridLength A.G I.1) ∧
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        ((D.withQ0 (qG G)).pV l G I.1)‖ ≤ Real.sqrt T₂ * Real.sqrt (dyadicGridLength A.G I.1) := by
    expose_names
    exact @core_reduction_hrv κ' c₀ A bf fp D qG S gs cc kk Vl C ρ₂ ha_def ha C₂ hcap₂ hS₂₁ hS₁
  have hsizes : ∀ I ∈ S₂, ∀ G ∈ gs I, ∀ l,
      ‖(D.withQ0 (qG G)).coreAt l G I‖ ≤ coreBd B₀ T₂ * Real.sqrt (dyadicGridLength A.G I.1) ∧
      ‖(D.withQ0 (qG G)).errAt L l G I‖ ≤ errBd B₀ T₂ * Real.sqrt (dyadicGridLength A.G I.1) ∧
      ‖(D.toLeafQ qG).sv l G I‖ ≤ Real.sqrt Tc * Real.sqrt (dyadicGridLength A.G I.1) := by
    intro I hI G hG l
    have hIS := hS₁ (hS₂₁ hI)
    refine ⟨?_, ?_, hsv I (hS₂₁ hI) G hG l⟩ <;>
    · by_cases hl : D.u = some l
      · have hT := Real.sqrt_nonneg T₂
        have h5 := Real.sqrt_nonneg 5
        simp only [coreAt, errAt, SideInput.withQ0_u, hl, ↓reduceIte, norm_zero, coreBd, errBd]
        positivity
      · have h := D.sizes_atQ qG L (hS hIS) G (huse I hIS G hG) l (hrep I hIS G hG l hl) hB₀
          (hout I hIS G hG l) (hrv I hI G hG l hl).1 (hrv I hI G hG l hl).2
        first | exact h.1 | exact h.2
  refine ⟨C₂, hC₂S, hlen₂, hsizes, ?_⟩
  -- the cell inequality
  set! E : ℤ × ℤ → ℝ := fun I => ∑ τ ∈ Finset.univ.filter (fun τ : Fin 4 → Fin 3 => ∃ l, τ l = 2),
    ‖∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
      (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ with hE_def
  set! Tt : ℤ × ℤ → ℝ := fun I => ∑ τ ∈ Finset.univ.filter (fun τ : Fin 4 → Fin 3 =>
    (∀ l, τ l ≠ 2) ∧ 3 ≤ patternCount τ 1),
    ‖∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
      (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ with hT_def
  set! Rr : ℤ × ℤ → ℝ := fun I => ‖∑ σ ∈ Finset.univ.filter
    (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
      (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
      (Finset.univ.filter fun l => σ l = 1).card = 2),
    ∑ G ∈ gs I, fp.Λc I
      (fun l => if σ l = 0 then (D.toLeafQ qG).out l G I else (D.toLeafQ qG).sv l G I)‖ with hR_def
  set! Cc : ℤ × ℤ → ℝ := fun I => ‖∑ τ ∈ Finset.univ.filter
    (fun τ : Fin 4 → Fin 3 => (∀ l, τ l ≠ 2) ∧ 3 ≤ patternCount τ 0),
    ∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
      (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ with hC_def
  have hcell : ∀ I ∈ S₂, dyadicGridLength A.G I.1 *
      min η ‖∑ G ∈ gs I, fp.Λc I (fun l => (D.toLeafQ qG).out l G I)‖ ≤
      dyadicGridLength A.G I.1 * min η (Rr I) + 82 * (dyadicGridLength A.G I.1 * E I) +
        82 * (dyadicGridLength A.G I.1 * min η (Tt I)) +
        dyadicGridLength A.G I.1 * min η (Cc I) := by
    intro I hI
    have hIS := hS₁ (hS₂₁ hI)
    have hr := dyadicGridLength_pos A.G I.1
    have h1 := D.cell_reduction qG L (hS hIS) (gs I) (fun G hG l hl => hrep I hIS G hG l hl)
    have h2 := min_four_le (a := Rr I) (e := E I) (t := Tt I) (c := Cc I) hη (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (norm_nonneg _)
    have h3 := (min_le_min_left η h1).trans h2
    have := mul_le_mul_of_nonneg_left h3 hr.le
    nlinarith only [hr, h3]
  calc _ ≤ ∑ I ∈ S₂, (dyadicGridLength A.G I.1 * min η (Rr I) +
        82 * (dyadicGridLength A.G I.1 * E I) +
        82 * (dyadicGridLength A.G I.1 * min η (Tt I)) +
        dyadicGridLength A.G I.1 * min η (Cc I)) := Finset.sum_le_sum hcell
    _ = ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min η (Rr I) +
        82 * ∑ I ∈ S₂, dyadicGridLength A.G I.1 * E I +
        82 * ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min η (Tt I) +
        ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min η (Cc I) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have hR : ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min η (Rr I) ≤ B₂ := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS₂₁ fun I _ _ =>
            mul_nonneg (dyadicGridLength_pos A.G I.1).le (le_min hη (norm_nonneg _))) htwo
        have hEr := error_patterns_le S₂ (fun I => dyadicGridLength A.G I.1)
          (fun I _ => dyadicGridLength_pos A.G I.1) gs fp.Λc
          (localFormUniformConstant_nonneg κ')
          (by unfold coreBd errBd; positivity : 0 ≤ coreBd B₀ T₂ + errBd B₀ T₂ + Real.sqrt Tc)
          (fun I _ x => fp.norm_Λc_leM I x) (fun I G l => (D.withQ0 (qG G)).coreAt l G I)
          (fun I G l => (D.toLeafQ qG).sv l G I) (fun I G l => (D.withQ0 (qG G)).errAt L l G I)
          (fun I hI G hG l => by
            obtain ⟨h1, h2, h3⟩ := hsizes I hI G hG l
            have hsq := Real.sqrt_nonneg (dyadicGridLength A.G I.1)
            have hc0 : 0 ≤ coreBd B₀ T₂ := by unfold coreBd; positivity
            have he0 : 0 ≤ errBd B₀ T₂ := by unfold errBd; positivity
            have ht0 := Real.sqrt_nonneg Tc
            refine ⟨h1.trans ?_, h3.trans ?_, h2.trans ?_⟩ <;>
            exact mul_le_mul_of_nonneg_right (by linarith) hsq)
          (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hS₂₁.trans hS₁) fun I _ _ =>
            mul_nonneg (dyadicGridLength_pos A.G I.1).le (Nat.cast_nonneg _)) hM)
          (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hS₂₁.trans hS₁) fun I _ _ =>
            Finset.sum_nonneg fun G _ => Finset.sum_nonneg fun l _ => sq_nonneg _) hEe)
        have hTh := hthree (fun I G l => (D.withQ0 (qG G)).coreAt l G I) (fun I G l => (D.withQ0
            (qG G)).errAt L l G I) S₂ hS₂₁
          (by unfold coreBd; positivity : (0 : ℝ) ≤ coreBd B₀ T₂)
          (fun I hI G hG l => (hsizes I hI G hG l).1)
        linarith

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint line 2461 with the side estimate (lines 2446-2456): on one localization leaf of the
guarded search, after the cut family of the side estimate (root fraction `2ρ`) and the second cut
for the rolling and linear sides (root fraction `ρ₂`), the cores, errors and sides have the
retained sizes `coreBd`, `errBd`, `√T_c`, the side cap of the side estimate holds along the
retained paths, and the weighted active minimum of the whole leaf
outputs is at most the two-side bound of the side estimate, `82` times the error patterns
(`eq:physical-error`, the active multiplicity and Cauchy-Schwarz), `82` times the three-side power
bound with cores of size `coreBd`, and the weighted active minimum of the patterns with at least
three cores (`core_reduction`, `side_estimate_leaf`). -/
theorem core_reduction_leaf (qG : bf.Grp → ℕ) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3)
    (hanc : A.AncClosed)
    (hne : A.cells.Nonempty)
    -- the leaf of the guarded search, its cells, groups and counts
    {fuel : ℕ} {up₀ : Fin 4} {s : ℕ} (hLf : D.Lf = leafAt fuel fp.Lc up₀ s)
    (hmH : 2 * fuel + 2 ≤ fp.mH)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : D.S.K ≤ 2 ^ N) (S : Finset (ℤ × ℤ))
    (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, (D.toLeafQ qG).bk I < Bn)
    (hLp : ∀ l, ((D.toLeafQ qG).pe l).length ≤ Lp)
    (hJm : ∀ c d i i',
      ((D.toLeafQ qG).desc c d ((D.toLeafQ qG).tOf c i) ((D.toLeafQ qG).tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    (huse : ∀ I ∈ S, ∀ G ∈ gs I, fp.ActualUse G I)
    {Np : ℝ} (hNp : ∀ c d, (((D.toLeafQ qG).pe d).length * ((D.toLeafQ qG).pe c).length : ℝ) ≤ Np)
    -- the finite base data
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → D.u ≠ some c → D.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    {CF : ℝ} (hCF : 0 < CF)
    (hnormF : ∀ l (jb : Fin 2), ∀ U ∈ A.cells, ‖columnL2Restriction (dyadicGridCell A.G U.1 U.2)
      (dyadicGridCell_measurable A.G U.1 U.2) (bf.P l jb).Z‖ ^ 2 ≤ CF * dyadicGridLength A.G U.1)
    {η₀ E : ℝ} (hsub : A.SubRootProps η₀ E)
    -- the catalogs and the instantiated helper catalog
    {τr : ℕ → ℝ}
    (hpass : ∀ I ∈ S, ∀ l, D.u ≠ some l → ∀ w : fp.TestName I Unit, fp.MainRk w →
      (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc
        bf.vtag (A.w I) (τr (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).r) fp.mH (D.cat l))
    {τH : ℝ} (hτH : 0 ≤ τH) {Bh : Type} (gE : ℤ × ℤ → Bh → bf.Grp)
    (hgE : ∀ I ∈ S, ∀ G ∈ gs I, ∃ i, gE I i = G)
    (hhpass : ∀ I ∈ S, ∀ a, ∀ w : fp.HelperName I Bh,
      (fp.helperOf a I (fun i => (D.toLeafQ qG).sv a (gE I i) I) w).Pass A.G (bf.origCols a) I
        A.csrc A.Hsrc bf.vtag (A.w I) τH fp.mH (D.cat a))
    {τ₃ Sz : ℝ} (hτ0 : ∀ R, 0 ≤ τr R) (n : ℕ → ℝ) (hn : Monotone n)
    (hn0 : 2 * A.colBudget ≤ n 0)
    (hτr : ∀ R, 1 ≤ R → R ≤ fp.Lc + 4 → τr R * (A.colBudget * Real.sqrt (n (R - 1))) ≤ τ₃)
    (hτH' : τH * (A.colBudget * Real.sqrt (n (fp.Lc + 4))) ≤ τ₃) (hSz : 2 * Real.sqrt CF ≤ Sz)
    (d₀ : bf.Vtx) {NH : ℝ}
    (hNl : ∀ I ∈ S, ∀ l, ∀ r ≤ fp.Lc + 4, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols l) (D.cat l) I r M d₀).card : ℝ) ≤ n r)
    (hNH : ∀ I ∈ S, ∀ a, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols a) (D.cat a) I (fp.Lc + 5) M d₀).card : ℝ) ≤ NH)
    {τ₂ : ℝ} (hτ₂ : 0 < τ₂) (hτ₂1 : τ₂ ≤ 1)
    (hτ₂' : τ₂ * (A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt NH)) ≤ τ₃)
    (hHed₂ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed)
    -- the joint group budgets of the ball levels
    (G₀ : bf.Grp) (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hJc : (Jm : ℝ) ≤ cc * (Real.log kk + 1))
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1))
    -- the linear-side bound
    {Vl : Fin 4 → ℝ}
    (hlin : ∀ l, D.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide
        (D.S.withQ0 (qG G))
        D.hA D.SP (A.R.1 + ((D.S.K * β : ℕ) : ℤ))
          (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
          (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤
        Vl l * dyadicGridLength A.G A.R.1)
    -- the stack energies of the near bands
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, D.u ≠ some a → fp.stackEA (SideLeafM.nOs Lp Jm) (D.cat a) (D.mbs a)
        (D.toLeafQ qG).Dpre N (capV A cc kk) (sideB0 A cc kk (Vl a)) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, D.u ≠ some b →
      (SideLeafM.nOs Lp Jm).card * (N * capV A cc kk + sideB0 A cc kk (Vl b)) ≤
        Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (SideLeafM.nOs Lp Jm).card * (2 * (4 * E * dyadicGridLength A.G A.R.1)) ≤
      ΓU * dyadicGridLength A.G A.R.1)
    -- the frozen lifts and their coefficients, the physical errors and the active multiplicity
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    (hrep : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l, D.u ≠ some l → (D.withQ0 (qG G)).RepAt L l G I)
    {Ee M : ℝ} (hEe : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.withQ0 (qG G)).errAt L l G I‖ ^ 2 ≤ Ee)
    (hM : ∑ I ∈ S, dyadicGridLength A.G I.1 * (gs I).card ≤ M)
    {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C C₂ : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      C₂ ⊆ S ∧ dyadicRootLength A.G C₂ ≤ ρ₂ * dyadicGridLength A.G A.R.1 ∧
      (∀ I ∈ ((S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)),
        ∀ G ∈ gs I, ∀ l,
        ‖(D.withQ0 (qG G)).coreAt l G I‖ ≤ coreBd (max (2 * Real.sqrt CF) A.S) (D.T2 cc kk Vl ρ₂) *
            Real.sqrt
            (dyadicGridLength A.G I.1) ∧
        ‖(D.withQ0 (qG G)).errAt L l G I‖ ≤ errBd (max (2 * Real.sqrt CF) A.S) (D.T2 cc kk Vl ρ₂) *
            Real.sqrt
            (dyadicGridLength A.G I.1) ∧
        ‖(D.toLeafQ qG).sv l G I‖ ≤ Real.sqrt (D.Tside qG Lp Jm CF E cc kk Vl ρ) * Real.sqrt
            (dyadicGridLength A.G I.1)) ∧
      (∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, (D.toLeafQ qG).s2 G I ≤
        D.Tside qG Lp Jm CF E cc kk Vl ρ) ∧
      ∑ I ∈ ((S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)),
        dyadicGridLength A.G I.1 * min η ‖∑ G ∈ gs I, fp.Λc I (fun l => (D.toLeafQ qG).out l G I)‖ ≤
      (6 * 256 * Np * (τ + fp.farC fuel τ₃ Sz) * D.Tside qG Lp Jm CF E cc kk Vl ρ *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          (D.toLeafQ qG).nearBnd hq2 hq3 Nd N Lp Jm Mp (2 * Real.sqrt CF) (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl
            ρ ^
            (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
          dyadicGridLength A.G A.R.1)) +
      82 * (81 * (localFormUniformConstant κ' * (coreBd (max (2 * Real.sqrt CF) A.S) (D.T2 cc kk
          Vl ρ₂) + errBd (max (2 * Real.sqrt CF) A.S) (D.T2 cc kk Vl ρ₂) +
        Real.sqrt (D.Tside qG Lp Jm CF E cc kk Vl ρ)) ^ 3) * (Real.sqrt (4 * M) * Real.sqrt Ee)) +
      82 * (η ^ (1 - p) * (81 * localFormUniformConstant κ' *
          max (coreBd (max (2 * Real.sqrt CF) A.S) (D.T2 cc kk Vl ρ₂)) (Real.sqrt (D.Tside qG Lp Jm
              CF E cc kk Vl ρ))) ^ p *
        (D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
            D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * dyadicGridLength A.G A.R.1)) +
      ∑ I ∈ ((S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)),
        dyadicGridLength A.G I.1 * min η ‖∑ τ ∈ Finset.univ.filter
          (fun τ : Fin 4 → Fin 3 => (∀ l, τ l ≠ 2) ∧ 3 ≤ patternCount τ 0),
          ∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
            (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ := by
  have hS0 : 0 ≤ A.S := le_trans ENNReal.toReal_nonneg (A.U_le 0 A.R)
  have hbasic : ∀ J ∈ A.cells, ∀ l, ‖bf.basicIn fp.Mc l J‖ ≤
      2 * Real.sqrt CF * Real.sqrt (dyadicGridLength A.G J.1) := fun J hJ l =>
    bf.norm_basicIn_le fp.Mc l hJ hCF.le fun jb => hnormF l jb J hJ
  have hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l, ‖(D.toLeafQ qG).out l G I‖ ≤
      max (2 * Real.sqrt CF) A.S * Real.sqrt (dyadicGridLength A.G I.1) := by
    intro I hI G _ l
    refine ((D.toLeafQ qG).norm_out_le l G I).trans ?_
    change ‖(if D.u = some l then bf.Ucol fp.Mc l I else bf.basicIn fp.Mc l I)‖ ≤ _
    split_ifs
    · exact (bf.norm_Ucol_le fp.Mc l I).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
    · exact (hbasic I (hS hI) l).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨C, hC, hlen, htwo, hthree, hcap⟩ := D.side_estimate_leaf qG hq2 hq3 hanc hne hLf hmH hKNd
    hKN S hS hroot gs gset hgs Lp Jm Bn k hBn hLp hJm Act hact hMp hcertS huse hNp hτ hpair hCF
    hnormF hsub hpass hτH gE hgE hhpass hτ0 n hn hn0 hτr hτH' hSz d₀ hNl hNH hτ₂ hτ₂1 hτ₂' hHed₂
    G₀ B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hJc hLs hlin hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ
    hρ1
  obtain ⟨C₂, hC₂, hlen₂, hsizes, hmain⟩ := D.core_reduction qG L hanc hne S hS gs gset hgs k Bn
    hcertS huse hBn B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hLs hlin hrep
    (le_max_of_le_left (by positivity)) hout C hη htwo hcap
    (B₃ := fun Bc => η ^ (1 - p) * (81 * localFormUniformConstant κ' *
      max Bc (Real.sqrt (D.Tside qG Lp Jm CF E cc kk Vl ρ))) ^ p *
      (D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
        D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * dyadicGridLength A.G A.R.1))
    (fun core err S' hS' Bc hBc hcore => hthree core err S' hS' hBc hcore) hEe hM hρ₂ hρ₂1
  exact ⟨C, C₂, hC, hlen, hC₂, hlen₂, hsizes, hcap, hmain.trans (by linarith only)⟩

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The exact common-height selection on the side states (blueprint lines 2464-2466) -/

/-- A column function vanishing off a set restricts to zero on a disjoint set, also after taking
its physical part. -/
theorem restrict_physEmbed_eq_zero {V W : Type*} [Fintype V] [Fintype W] {s t : Set ℝ}
    (ht : MeasurableSet t) (hst : Disjoint s t) (x : ColumnL2 V)
    (hx : ∀ᵐ y ∂volume, y ∉ s → (x : ℝ → ColumnHilbert V) y = 0) :
    columnL2Restriction t ht (physEmbed V W x) = 0 := by
  classical
  refine Lp.ext ?_
  change (columnL2Indicator t ht (physEmbed V W x) : ℝ → ColumnHilbert W) =ᵐ[volume] _
  filter_upwards [columnL2Indicator_coeFn t ht (physEmbed V W x), physEmbed_coeFn (W := W) x, hx,
    Lp.coeFn_zero (ColumnHilbert W) 2 (volume : Measure ℝ)] with y h1 h2 h3 h4
  rw [h1, h4]
  by_cases hy : y ∈ t
  · rw [Set.indicator_of_mem hy, h2, h3 (Set.disjoint_right.mp hst hy)]
    simp
  · rw [Set.indicator_of_notMem hy]
    rfl

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The pre-cell `J = anc_{b - 2K}(I)` of the block of a cell (blueprint line 1975). -/
noncomputable def preAt (I : ℤ × ℤ) : ℤ × ℤ := ancAt A.G I (A.blkStart D.S.K I.1 - 2 * D.S.K)

theorem subset_preAt (I : ℤ × ℤ) :
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G (D.preAt I).1 (D.preAt I).2 := by
  have hb := blkStart_bounds D.hK I.1 (A := A)
  have hK0 : (0 : ℤ) ≤ D.S.K := Nat.cast_nonneg _
  exact subset_ancAt A.G I (by omega)

open Classical in
/-- The core components of the slot `l` and group `G` at the cell `I`: those of the retained
pre-cell of its block (none in the basic `U` slot or when the pre-cell is not retained). -/
noncomputable def compsAt (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) : Finset (Finset (D.Ms l G).Md) :=
  if D.u ≠ some l ∧ D.preAt I ∈ fp.retainedV G (A.blkStart D.S.K I.1) D.S.K then
    (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) else ∅

/-- The physical subtotal on the cell `I` of a core component on its pre-cell. -/
noncomputable def compSub (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) (K : Finset (D.Ms l G).Md) :
    ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
    (fp.physMain (D.Ms l G).Md (∑ m ∈ K, D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m •
      (D.Ms l G).cellMode (D.preAt I) m))

open Classical in
/-- Blueprint lines 2463-2464: on a cell the core is the sum of the subtotals of the core
components of its retained pre-cell (the other retained pre-cells of the block are disjoint from
the cell). -/
theorem coreAt_eq_comps (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    D.coreAt l G I = ∑ K ∈ D.compsAt l G I, D.compSub l G I K := by
  have hIJ := D.subset_preAt I
  unfold coreAt compsAt
  set b := A.blkStart D.S.K I.1 with hb
  set Jp := D.preAt I with hJp
  -- the retained pre-cells other than `Jp` contribute nothing on `I`
  have hoff : ∀ J ∈ fp.retainedV G b D.S.K, J ≠ Jp →
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md (∑ K ∈ (D.Ms l G).coreComps D.S D.hA D.SP b J,
          ∑ m ∈ K, D.c l G b J m • (D.Ms l G).cellMode J m)) = 0 := by
    intro J hJ hne
    have hJ1 := ((fp.mem_retainedV).mp hJ).2.1
    have hJp1 : Jp.1 = b - 2 * D.S.K := rfl
    have hdisJ : Disjoint (dyadicGridCell A.G J.1 J.2) (dyadicGridCell A.G Jp.1 Jp.2) := by
      have h2 : J.2 ≠ Jp.2 := fun h => hne (Prod.ext (by rw [hJ1, hJp1]) h)
      rw [hJ1, hJp1] at *
      exact dyadicGridCell_pairwiseDisjoint A.G _ h2
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, map_smul, restrict_physEmbed_eq_zero _ (hdisJ.mono_right hIJ) _
      ((D.Ms l G).cellMode_vanish J m), smul_zero]
  by_cases hl : D.u = some l
  · simp [hl]
  by_cases hJ : Jp ∈ fp.retainedV G b D.S.K
  · simp only [hl, hJ, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    unfold ModeSystem.blockCore
    rw [map_sum, map_sum, Finset.sum_eq_single_of_mem Jp hJ hoff, map_sum, map_sum]
    rfl
  · simp only [hl, hJ, ne_eq, not_false_eq_true, and_false, ↓reduceIte, Finset.sum_empty]
    unfold ModeSystem.blockCore
    rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun J hJ' => hoff J hJ' fun h => hJ (h ▸ hJ')

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- The goodness at a height of the entry of a component tuple in a slot: the goodness of the
component on the pre-cell of the block of `I` in a core slot, always good otherwise. -/
def slotGood (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4) (h : ℕ)
    (o : Option (Finset (D.Ms l G).Md)) : Prop :=
  match o with
  | some K => (D.Ms l G).compGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K
  | none => True

open Classical in
/-- Blueprint lines 2464-2466 ("each core mode has bad proportion at most `2δ_*`, so success
probability is at least `1 - 2 m₀ δ_*`"): every tuple of core components of a pattern on a cell
has an upper height at which all its slots are good. -/
theorem tuple_success (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) (hJ : 2 ≤ D.SP.Jst)
    (hδ : 0 < D.SP.δs) (hδ16 : D.SP.δs ≤ 1 / 16) :
    ∀ r ∈ Fintype.piFinset (compIdx σ (fun l => D.compsAt l G I)),
      ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).filter
        fun h => ∀ l, D.slotGood G I l h (r l)).Nonempty := by
  intro r hr
  set H := ModeComponents.upperHeights D.SP.Jst D.SP.δs
  have hHn := ActiveSetup.AttemptParams.LeafSplit.upperHeights_nonempty (J := D.SP.Jst) hδ16
  set bad : Fin 4 → Finset ℕ := fun l => H.filter fun h => ¬ D.slotGood G I l h (r l)
  have hbad : ∀ l, ((bad l ∩ H).card : ℝ) ≤ 2 * D.SP.δs * H.card := by
    intro l
    have hsub : bad l ∩ H ⊆ bad l := Finset.inter_subset_left
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
    have hrl := (Fintype.mem_piFinset.mp hr) l
    unfold compIdx at hrl
    split_ifs at hrl with hl
    · obtain ⟨K, hK, hrK⟩ := Finset.mem_map.mp hrl
      have hK' : K ∈ (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) := by
        unfold compsAt at hK
        beta_reduce at hK
        split_ifs at hK
        · exact hK
        · exact absurd hK (Finset.notMem_empty _)
      have e : bad l = H.filter fun h => ¬ (D.Ms l G).compGood D.S D.hA D.SP
          (A.blkStart D.S.K I.1) (D.preAt I) h K := by
        simp only [bad, ← hrK, slotGood, Function.Embedding.some_apply]
      rw [e]
      exact (D.Ms l G).coreComp_bad_card D.S D.hA D.SP hK' hJ hδ hδ16
    · have hrn : r l = none := Finset.mem_singleton.mp hrl
      have e : bad l = ∅ := by
        simp only [bad, hrn, slotGood, not_true_eq_false]
        exact Finset.filter_false_of_mem fun _ _ => id
      rw [e, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
      positivity
  have hpos := success_proportion_pos H hHn bad hbad (by norm_num; linarith)
  have hne : (H.filter fun h => ∀ l, h ∉ bad l).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.card_empty, Nat.cast_zero, zero_div] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h, hh⟩ := hne
  obtain ⟨hH, hall⟩ := Finset.mem_filter.mp hh
  refine ⟨h, Finset.mem_filter.mpr ⟨hH, fun l => ?_⟩⟩
  by_contra hng
  exact hall l (Finset.mem_filter.mpr ⟨hH, hng⟩)

open Classical in
/-- Blueprint lines 2463-2466, the exact common-height selection on one actual cell and group of
the side states: the form of a core/side/error pattern is the sum over the tuples of core
components of the forms of their subtotals (the finite multilinear expansion), and it is the
convergent sum over the trial counts `n`, the assignments `a` of the failed trials to their first
failing roles, the words `w` of failed upper heights and the final heights `h`, with the weights
`|H|^{-(n+1)}` of the uniformly sampled heights, of the sums over the tuples in the product
masks; the first-success rule has total weight one for every tuple. -/
theorem pattern_first_success (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    (I : ℤ × ℤ) (G : bf.Grp) (σ : Fin 4 → Fin 3) (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) :
    fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) σ) =
      ∑ r ∈ Fintype.piFinset (compIdx σ (fun l => D.compsAt l G I)),
        fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I)
          (fun l => D.errAt L l G I) r) ∧
    HasSum (fun n : ℕ => ∑ a : Fin n → Fin 4,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      ∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ) ^ (n + 1))⁻¹ •
        ∑ r ∈ (Fintype.piFinset (compIdx σ (fun l => D.compsAt l G I))).filter
          (fun r => ∀ l, roleMask (D.slotGood G I l) l a w h (r l)),
          fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I)
            (fun l => D.errAt L l G I) r))
      (fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) σ)) := by
  have hexp : fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
      (fun l => D.errAt L l G I) σ) =
      ∑ r ∈ Fintype.piFinset (compIdx σ (fun l => D.compsAt l G I)),
        fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I)
          (fun l => D.errAt L l G I) r) :=
    pattern_comp_expand (fp.Λc I) σ (fun l => D.compsAt l G I) (fun l K => D.compSub l G I K)
      _ _ _ fun l _ => D.coreAt_eq_comps l G I
  refine ⟨hexp, ?_⟩
  rw [hexp]
  exact first_success_masked _ _ (fun l h o => D.slotGood G I l h o) _
    (D.tuple_success G I σ hJ hδ hδ16)

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## Failure masks and representatives on the side states (blueprint lines 2466-2467) -/

namespace ModeComponents
variable {Mode P : Type*} [DecidableEq Mode] [DecidableEq P] (C : ModeComponents Mode P)

/-- `good_same_predecessor` with the stabilization only at the heights `h ≤ J`. -/
theorem good_same_predecessor_le (Δ : ℕ) (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    {J : ℕ} (hstab : ∀ h ≤ J, ∀ x x', goodP h (C.π x) → C.π x' = C.π x → x' ∈ C.F h x →
      x' ∈ C.E (h - Δ) x)
    {h : ℕ} (hhJ : h ≤ J) {m m' : Mode} (hm : C.Good Δ goodP h m) (hm' : C.Good Δ goodP h m')
    (hmm' : m' ∈ C.F h m) : C.E (h - Δ) m = C.E (h - Δ) m' :=
  C.good_same_predecessor Δ (fun h' p => goodP h' p ∧ h' ≤ J)
    (fun h' x x' hg hπ hF => hstab h' hg.2 x x' hg.1 hπ hF)
    (by
      obtain ⟨h1, h2, h3⟩ := hm
      refine ⟨h1, h2, h3.trans (le_of_eq ?_)⟩
      congr 2
      exact Finset.filter_congr fun p _ => ⟨fun hp => ⟨hp, hhJ⟩, fun hp => hp.1⟩)
    (by
      obtain ⟨h1, h2, h3⟩ := hm'
      refine ⟨h1, h2, h3.trans (le_of_eq ?_)⟩
      congr 2
      exact Finset.filter_congr fun p _ => ⟨fun hp => ⟨hp, hhJ⟩, fun hp => hp.1⟩)
    hmm'

/-- `core_good_iff` with the stabilization only at the heights `h ≤ J`. -/
theorem core_good_iff_le (Δ : ℕ) (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    {J : ℕ} (hstab : ∀ h ≤ J, ∀ x x', goodP h (C.π x) → C.π x' = C.π x → x' ∈ C.F h x →
      x' ∈ C.E (h - Δ) x)
    (hJ : 2 ≤ J) {δ : ℝ} (hδ : 0 < δ) (hδJ : ⌈4 * δ * J⌉₊ ≤ J) {m m' : Mode}
    (hm : C.Core Δ goodP J δ m) (hm' : C.Core Δ goodP J δ m') (hmm' : m' ∈ C.F 0 m) :
    ∀ h ∈ upperHeights J δ, C.Good Δ goodP h m ↔ C.Good Δ goodP h m' := by
  classical
  obtain ⟨h0, hh0, hg0, hg0'⟩ : ∃ h0 < ⌈4 * δ * J⌉₊, C.Good Δ goodP h0 m ∧
      C.Good Δ goodP h0 m' := by
    by_contra hno
    push Not at hno
    have hsub : Finset.range ⌈4 * δ * J⌉₊ ⊆ C.badHeights Δ goodP J m ∪
        C.badHeights Δ goodP J m' := by
      intro h hh
      have hhJ : h < J + 1 := by have := Finset.mem_range.mp hh; omega
      simp only [Finset.mem_union, badHeights, Finset.mem_filter, Finset.mem_range]
      by_cases hgm : C.Good Δ goodP h m
      · exact Or.inr ⟨hhJ, hno h (Finset.mem_range.mp hh) hgm⟩
      · exact Or.inl ⟨hhJ, hgm⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at hc
    have hc' : (⌈4 * δ * J⌉₊ : ℝ) ≤ δ * (J + 1) + δ * (J + 1) := by
      have : (⌈4 * δ * J⌉₊ : ℝ) ≤ ((C.badHeights Δ goodP J m).card : ℝ) +
          (C.badHeights Δ goodP J m').card := by exact_mod_cast hc
      have h1 : ((C.badHeights Δ goodP J m).card : ℝ) ≤ δ * (J + 1) := hm
      have h2 : ((C.badHeights Δ goodP J m').card : ℝ) ≤ δ * (J + 1) := hm'
      linarith
    have hceil := Nat.le_ceil (4 * δ * J)
    have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hpre := C.good_same_predecessor_le Δ goodP hstab (by omega) hg0 hg0'
    (C.F_mono 0 h0 m (Nat.zero_le _) hmm')
  intro h hh
  have hh0h : h0 ≤ h := by
    have := (Finset.mem_filter.mp hh).2; omega
  apply C.good_iff_of_components Δ goodP
  · have hmem : m' ∈ C.E (h - Δ) m := by
      apply C.E_mono (h0 - Δ) _ m (by omega)
      rw [hpre]; exact C.E_self _ m'
    exact C.E_eq_of_mem hmem
  · exact (C.F_comp h m m' (C.F_mono 0 h m (Nat.zero_le _) hmm')).symm

/-- `mem_pred_of_good_class` with the stabilization only at the heights `h ≤ J`. -/
theorem mem_pred_of_good_class_le (Δ : ℕ) (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    {J : ℕ} (hstab : ∀ h ≤ J, ∀ x x', goodP h (C.π x) → C.π x' = C.π x → x' ∈ C.F h x →
      x' ∈ C.E (h - Δ) x)
    {h : ℕ} (hhJ : h ≤ J) {m x₀ x a : Mode} (hm : C.Good Δ goodP h m)
    (hx₀ : C.Good Δ goodP h x₀) (hcls : C.F h x₀ = C.F h m) (hx : x ∈ C.E 0 x₀)
    (ha : a ∈ C.E (h - Δ) m) : x ∈ C.E (h - Δ) a := by
  have hx₀m : x₀ ∈ C.F h m := hcls ▸ C.mem_F_self h x₀
  have hpred := C.good_same_predecessor_le Δ goodP hstab hhJ hm hx₀ hx₀m
  rw [C.E_comp (h - Δ) m a ha, hpred]
  exact C.E_mono 0 (h - Δ) x₀ (Nat.zero_le _) hx

end ModeComponents

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

open Classical in
/-- `compGood_iff_of_same_class` with the stabilization only at the heights `h ≤ J_*`. -/
theorem compGood_iff_of_same_class_le {b : ℤ} {J : ℤ × ℤ}
    (hstab : ∀ h ≤ SP.Jst, ∀ x x', Ms.goodP S SP b h ((Ms.blockComps S hA b J).π x) →
      (Ms.blockComps S hA b J).π x' = (Ms.blockComps S hA b J).π x →
      x' ∈ (Ms.blockComps S hA b J).F h x → x' ∈ (Ms.blockComps S hA b J).E (h - SP.Δ) x)
    (hJ : 2 ≤ SP.Jst) (hδ : 0 < SP.δs) (hδJ : ⌈4 * SP.δs * SP.Jst⌉₊ ≤ SP.Jst)
    {K K' : Finset Ms.Md} (hK : K ∈ Ms.coreComps S hA SP b J) (hK' : K' ∈ Ms.coreComps S hA SP b J)
    (hcls : Ms.compClass S hA b J 0 K = Ms.compClass S hA b J 0 K') :
    ∀ h ∈ ModeComponents.upperHeights SP.Jst SP.δs,
      Ms.compGood S hA SP b J h K ↔ Ms.compGood S hA SP b J h K' := by
  intro h hh
  obtain ⟨x, hKx, hcore⟩ := Ms.coreComps_rep S hA SP hK
  obtain ⟨x', hKx', hcore'⟩ := Ms.coreComps_rep S hA SP hK'
  rw [hKx, hKx', Ms.compClass_eq S hA b J 0 x, Ms.compClass_eq S hA b J 0 x'] at hcls
  have hF : (Ms.blockComps S hA b J).F 0 x = (Ms.blockComps S hA b J).F 0 x' :=
    Finset.map_injective _ hcls
  have hx' : x' ∈ (Ms.blockComps S hA b J).F 0 x :=
    hF ▸ (Ms.blockComps S hA b J).E_le_F 0 x' ((Ms.blockComps S hA b J).E_self 0 x')
  rw [Ms.compGood_iff S hA SP hKx h, Ms.compGood_iff S hA SP hKx' h]
  exact (Ms.blockComps S hA b J).core_good_iff_le SP.Δ (Ms.goodP S SP b) hstab hJ hδ hδJ hcore
    hcore' hx' h hh

end ModeSystem

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lem:stabilize on the pre-cells of the side states (`blockComps_stab`): two alive
modes of one key good at a height `h ≤ J_*` lying in one CURRENT component at `h` are PRE-joined
at `h - Δ`. -/
def Stab : Prop :=
  ∀ (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ), ∀ h ≤ D.SP.Jst, ∀ x x',
    (D.Ms l G).goodP D.S D.SP (A.blkStart D.S.K I.1) h
        (((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).π x) →
      ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).π x' =
        ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).π x →
      x' ∈ ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F h x →
      x' ∈ ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
        (h - D.SP.Δ) x

open Classical in
/-- At the chosen schedule (`S.Valid`, side parameters `S.sideParams δ_*`) the stabilization holds
on the pre-cells of the side states (`blockComps_stab`): the alive modes number at most `D_*`,
the dimensions are at most `d_max` and `D_*` covers the heights of the mode differences. -/
theorem stab_of_valid {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 5 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdim : ∀ l G p, (D.Ms l G).dvOf p + (D.Ms l G).zc.dim ≤ D.S.dmax)
    (hBσ : ∀ l G, 2 * (D.S.Q0 * (3 * ((D.Ms l G).Bσ * (D.Ms l G).Bσ) ^ 2)) ^ 2 ≤
      (⌊D.S.Dstar⌋₊ : ℝ))
    (hcard : ∀ l G I, (((D.Ms l G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar) :
    D.Stab := by
  intro l G I h hh x x' hg hπ hF
  have hJ : (D.preAt I).1 = A.blkStart D.S.K I.1 - 2 * D.S.K := rfl
  have hJst : D.SP.Jst = D.S.Jstar := by rw [hSP]; rfl
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  rw [hΔ]
  have hg' : (D.Ms l G).goodP D.S (D.S.sideParams δs) (A.blkStart D.S.K I.1) h
      (((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).π x) := by
    rw [← hSP]; exact hg
  exact (D.Ms l G).blockComps_stab D.S hV hCA hCT hd2 hD hB hQ D.hA (hdim l G) (hBσ l G) hJ
    (hcard l G I) (hJst ▸ hh) x x' hg' hπ hF

open Classical in
/-- The final class at height `h` of a component index of a core slot (blueprint line 2467):
the union of the CURRENT components at `h` of its modes. -/
noncomputable def coreCls (G : bf.Grp) (I : ℤ × ℤ) (h : ℕ) (l : Fin 4)
    (o : Option (Finset (D.Ms l G).Md)) : Finset (D.Ms l G).Md :=
  match o with
  | some K => (D.Ms l G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K
  | none => ∅

open Classical in
/-- Blueprint lines 2466-2467 ("for a fixed assignment, the conditions in a role form a product
mask ... the upper-height coherence proved in Section `sec:modes` means these masks select unions
of entire core subtotals in minimal CURRENT components"): two core components of a slot in one
minimal CURRENT component have the same role mask for every assignment and every failure history
with heights in the upper heights, and the same final class at every height. -/
theorem roleMask_iff_of_same_unit (hstab : D.Stab) (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4)
    (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    {K K' : Finset (D.Ms l G).Md}
    (hK : K ∈ (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I))
    (hK' : K' ∈ (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I))
    (hcls : (D.Ms l G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0 K =
      (D.Ms l G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0 K')
    {n : ℕ} (a : Fin n → Fin 4) {w : Fin n → ℕ}
    (hw : ∀ i, w i ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs) {h : ℕ}
    (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs) :
    (roleMask (D.slotGood G I l) l a w h (some K) ↔
      roleMask (D.slotGood G I l) l a w h (some K')) ∧
    D.coreCls G I h l (some K) = D.coreCls G I h l (some K') := by
  have hg := fun t (ht : t ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs) =>
    (D.Ms l G).compGood_iff_of_same_class_le D.S D.hA D.SP (hstab l G I) hJ hδ hδJ hK hK' hcls t
      ht
  refine ⟨?_, ?_⟩
  · unfold roleMask slotGood
    simp only
    rw [hg h hh]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (hg (w i) (hw i)).not.mp (h2 i hi),
        fun i hi => (hg (w i) (hw i)).mp (h3 i hi)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (hg (w i) (hw i)).not.mpr (h2 i hi),
        fun i hi => (hg (w i) (hw i)).mpr (h3 i hi)⟩
  · obtain ⟨x, hKx, -⟩ := (D.Ms l G).coreComps_rep D.S D.hA D.SP hK
    obtain ⟨x', hKx', -⟩ := (D.Ms l G).coreComps_rep D.S D.hA D.SP hK'
    rw [hKx, hKx', (D.Ms l G).compClass_eq D.S D.hA _ _ 0 x,
      (D.Ms l G).compClass_eq D.S D.hA _ _ 0 x'] at hcls
    set C := (D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)
    have hF0 : C.F 0 x = C.F 0 x' := Finset.map_injective _ hcls
    have hx' : x' ∈ C.F h x :=
      C.F_mono 0 h x (Nat.zero_le h) (hF0 ▸ C.E_le_F 0 x' (C.E_self 0 x'))
    simp only [coreCls]
    rw [hKx, hKx', (D.Ms l G).compClass_eq D.S D.hA _ _ h x,
      (D.Ms l G).compClass_eq D.S D.hA _ _ h x', C.F_comp h x x' hx']

open Classical in
/-- Blueprint line 2467 for any representative of the predecessor (in particular the hereditary
representative of lines 2172-2183): every mode of a core component good at the final height `h`
lies in the PRE predecessor `E_{h-Δ}(a)` of any mode `a` of the predecessor `E_{h-Δ}(m)` of a good
mode `m` of its final class (the unique good predecessor of the final component). -/
theorem selected_in_pred_of_rep (hstab : D.Stab) (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4) {h : ℕ}
    (hh : h ≤ D.SP.Jst) {K : Finset (D.Ms l G).Md}
    (hK : (D.Ms l G).compGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K)
    {m a : (D.Ms l G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hm : ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
      ((D.Ms l G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m)
    (hcls : (((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F h m).map
      ⟨Subtype.val, Subtype.val_injective⟩ =
        (D.Ms l G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K)
    (ha : a ∈ ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
      (h - D.SP.Δ) m)
    (x : (D.Ms l G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hxK : x.1 ∈ K) :
    x ∈ ((D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E (h - D.SP.Δ) a := by
  set C := (D.Ms l G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)
  obtain ⟨x₀, rfl, hx₀⟩ := hK
  rw [(D.Ms l G).compClass_eq D.S D.hA _ _ h x₀] at hcls
  have hF : C.F h x₀ = C.F h m := (Finset.map_injective _ hcls).symm
  have hx : x ∈ C.E 0 x₀ := by
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hxK
    rw [← Subtype.val_injective hyx]; exact hy
  exact C.mem_pred_of_good_class_le D.SP.Δ _ (hstab l G I) hh hm hx₀ hF hx ha

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The core torus form on the side states (blueprint `eq:core-torus-form`, lines 2467-2471) -/

/-- A cell at least `j` depths below `s` has length at most `2^{-j}` times that of depth `s`. -/
theorem dyadicGridLength_le_pow (G : RealDyadicGrid) {s t : ℤ} {j : ℕ} (hst : s + j ≤ t) :
    dyadicGridLength G t ≤ dyadicGridLength G s * (2 : ℝ)⁻¹ ^ j :=
  ((dyadicGridLength_strictAnti G).antitone hst).trans
    (le_of_eq (dyadicGridLength_add_nat G s j))

/-- Points of one dyadic cell are at distance at most its length. -/
theorem abs_sub_le_of_mem_cell' (G : RealDyadicGrid) {I : ℤ × ℤ} {x y : ℝ}
    (hx : x ∈ dyadicGridCell G I.1 I.2) (hy : y ∈ dyadicGridCell G I.1 I.2) :
    |y - x| ≤ dyadicGridLength G I.1 := by
  simp only [dyadicGridCell, Set.mem_Ico] at hx hy
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

namespace ModeSchedule
variable (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}

/-- `eq:lags` at the chosen schedule: the pre-lag satisfies `D_*^{C_K} ≤ 2^K`. -/
theorem Valid.Dstar_pow_le (hV : S.Valid Cj CA CT CK δs W) (hW : 0 ≤ W) (hT : 1 ≤ S.T)
    (hD : 1 ≤ S.Dstar) : S.Dstar ^ CK ≤ (2 : ℝ) ^ S.K := by
  have hK := hV.K_ge
  have hlT : 0 ≤ Real.logb 2 S.T := Real.logb_nonneg (by norm_num) hT
  have h1 : Real.logb 2 S.Dstar * CK ≤ S.K := by linarith
  have hD0 : 0 < S.Dstar := by linarith
  calc S.Dstar ^ CK = (2 : ℝ) ^ (Real.logb 2 S.Dstar * CK) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hD0,
          Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (S.K : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (2 : ℝ) ^ S.K := Real.rpow_natCast _ _

end ModeSchedule

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0)

/-- The common torus frequency `ξ = ϑ / L_h` (`ϑ = θ / Q₀`) of a selected group at height `h`
(blueprint line 2467). -/
noncomputable def torusξ (h : ℕ) (i : Fin Ms.zc.dim) : ℝ :=
  Ms.zc.θ i / (S.Q0 * ModeSchedule.Lh h)

/-- The periodic factor `g_j` of `eq:core-torus-form`: the true periodic cutoff (re-centered at
`x*`) times the finite trigonometric polynomial of the selected modes with their integer shifts
(blueprint lines 2468-2470). -/
noncomputable def torusG {U : ℤ × ℤ} (h : ℕ) (xs : ℝ) (F : Finset (Ms.alive U))
    (α : Ms.alive U → ℂ) (n : Ms.alive U → Fin Ms.zc.dim → ℤ) (u : Fin Ms.zc.dim → ℝ) : ℂ :=
  cutoffP Ms.δc Ms.ρ (fun i => (S.Q0 * ModeSchedule.Lh h) * u i + Ms.zc.θ i * xs) *
    ∑ m ∈ F, α m * ((Real.fourierChar (Ms.phase m.1 xs) : ℂ) *
      (Real.fourierChar (∑ i, (n m i : ℝ) * u i) : ℂ))

/-- The periodic factor is periodic on the `ξ` torus (`L_h` is an integer). -/
theorem torusG_periodic {U : ℤ × ℤ} (h : ℕ) (xs : ℝ) (F : Finset (Ms.alive U))
    (α : Ms.alive U → ℂ) (n : Ms.alive U → Fin Ms.zc.dim → ℤ) (u : Fin Ms.zc.dim → ℝ)
    (j : Fin Ms.zc.dim → ℤ) :
    Ms.torusG S h xs F α n (u + fun i => (j i : ℝ)) = Ms.torusG S h xs F α n u := by
  unfold torusG
  congr 1
  · have e : (fun i => (S.Q0 * ModeSchedule.Lh h) * (u + fun i => (j i : ℝ)) i +
        Ms.zc.θ i * xs) = (fun i => (S.Q0 * ModeSchedule.Lh h) * u i + Ms.zc.θ i * xs) +
        fun i => (((S.Q0 * 6 ^ h : ℕ) * j i : ℤ) : ℝ) := by
      funext i
      simp only [Pi.add_apply, ModeSchedule.Lh]
      push_cast
      ring
    rw [e, cutoffP_periodic]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    have e : ∑ i, (n m i : ℝ) * (u + fun i => (j i : ℝ)) i =
        ∑ i, (n m i : ℝ) * u i + ((∑ i, n m i * j i : ℤ) : ℝ) := by
      push_cast
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    have hk : (Real.fourierChar (((∑ i, n m i * j i : ℤ) : ℝ)) : ℂ) = 1 := by
      rw [Real.fourierChar_apply]
      have : (↑(2 * Real.pi * (((∑ i, n m i * j i : ℤ) : ℝ))) : ℂ) * Complex.I =
          ((∑ i, n m i * j i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [e, AddChar.map_add_eq_mul, Circle.coe_mul, hk, mul_one]

open Classical in
/-- Blueprint `eq:core-torus-form` (lines 2467-2471) for a group of selected modes `F` in the PRE
component `E_h(a)` of a representative `a`, on an actual cell `I` of the block `b` (`I.1 ≥ b`)
inside the pre-cell `J` (`J.1 = b - 2K`), at any `x* ∈ I`: the wave sum is
`e(c p_ρ(y)) e(γ*(y - x*)) g(ξ (y - x*))` with `γ* = ω_a(x*)`, `ξ = ϑ / L_h` and the periodic
factor `g = torusG` (the true cutoff times a trigonometric polynomial with integer shifts of size
at most `|alive| E_h`), up to `D_*^{-150}` times the absolute coefficient sum: the PRE path gives
slope error `D_* Ξ / r_J` and the pre-lag `2^K ≥ D_*^{600}` makes it and the quadratic Taylor
error (curvature at most `Λ ≤ D_*` at the admission scale) negligible. -/
theorem cell_torus_form {b : ℤ} {J : ℤ × ℤ} (hJ : J.1 = b - 2 * S.K) {I : ℤ × ℤ}
    (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2) (hIb : b ≤ I.1) {h : ℕ}
    (a : Ms.alive (ancAt Gd J (b - 4 * S.K))) (F : Finset (Ms.alive (ancAt Gd J (b - 4 * S.K))))
    (hF : F ⊆ (Ms.blockComps S hA b J).E h a) (α : Ms.alive (ancAt Gd J (b - 4 * S.K)) → ℂ)
    {xs : ℝ} (hxs : xs ∈ dyadicGridCell Gd I.1 I.2) (hQ : 1 ≤ S.Q0) (hD : 2 ≤ S.Dstar)
    (hcard : ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar) (hΛ : Ms.Λ ≤ S.Dstar)
    (hK : S.Dstar ^ 600 ≤ (2 : ℝ) ^ S.K) :
    ∃ n : Ms.alive (ancAt Gd J (b - 4 * S.K)) → Fin Ms.zc.dim → ℤ,
      (∀ m ∈ F, ∀ i, |(n m i : ℝ)| ≤
        Fintype.card (Ms.alive (ancAt Gd J (b - 4 * S.K))) * S.Eh h) ∧
      ∀ y ∈ dyadicGridCell Gd I.1 I.2,
        ‖∑ m ∈ F, α m * Ms.wave m.1 y -
          (Real.fourierChar ((Ms.cl : ℝ) * centerPhase Ms.zc Ms.ρ y) : ℂ) *
            (Real.fourierChar (Ms.slope a.1 xs * (y - xs)) : ℂ) *
            Ms.torusG S h xs F α n (fun i => Ms.torusξ S h i * (y - xs))‖ ≤
          (S.Dstar ^ 150)⁻¹ * ∑ m ∈ F, ‖α m‖ := by
  have hK0 : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) < S.Dstar := by linarith
  have hU1 : (ancAt Gd J (b - 4 * S.K)).1 = b - 4 * S.K := rfl
  -- the curvature of the selected modes at the admission scale
  have hlam : ∀ m ∈ F, |Ms.lamOf m.1| ≤ Ms.Λ / dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ^
      2 := by
    intro m _
    have hmU := (Ms.mem_alive).mp m.2
    have hRU : dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ≤ dyadicGridLength Gd (Ms.cellOf
        m.1).1 :=
      dyadicGridLength_le_of_subset Gd hmU
    have hU0 := dyadicGridLength_pos Gd (ancAt Gd J (b - 4 * S.K)).1
    rw [le_div_iff₀ (pow_pos hU0 2)]
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0.le hRU 2) (abs_nonneg _))
      (Ms.lam_le m.1)
  obtain ⟨n, hn, hform⟩ := Ms.group_torus_form S hA (show J.1 ≤ b + S.K by omega) a F hF α hlam
  refine ⟨n, hn, fun y hy => ?_⟩
  have hxJ : xs ∈ Set.Icc (dyadicGridLeft Gd J.1 J.2)
      (dyadicGridLeft Gd J.1 J.2 + dyadicGridLength Gd J.1) := by
    have := hIJ hxs
    simp only [dyadicGridCell, Set.mem_Ico] at this
    exact ⟨this.1, this.2.le⟩
  have h1 := hform xs hxJ y
  -- the main term is the claimed torus form
  have hmain : Ms.gauge y * ((Real.fourierChar (Ms.slope a.1 xs * (y - xs)) : ℂ) *
      ∑ m ∈ F, α m * ((Real.fourierChar (Ms.phase m.1 xs) : ℂ) *
        (Real.fourierChar (-((-(∑ i, (n m i : ℝ) * (Ms.zc.θ i / S.Q0)) /
          ModeSchedule.Lh h) * (y - xs))) : ℂ))) =
      (Real.fourierChar ((Ms.cl : ℝ) * centerPhase Ms.zc Ms.ρ y) : ℂ) *
        (Real.fourierChar (Ms.slope a.1 xs * (y - xs)) : ℂ) *
        Ms.torusG S h xs F α n (fun i => Ms.torusξ S h i * (y - xs)) := by
    have hQL : (S.Q0 : ℝ) * ModeSchedule.Lh h ≠ 0 := by
      unfold ModeSchedule.Lh; positivity
    have hcut : ((centerCut Ms.zc Ms.δc Ms.ρ y : ℝ) : ℂ) = cutoffP Ms.δc Ms.ρ
        (fun i => (S.Q0 * ModeSchedule.Lh h) * (Ms.torusξ S h i * (y - xs)) + Ms.zc.θ i * xs) := by
      rw [centerCut_eq_cutoffP]
      congr 1
      funext i
      unfold torusξ
      rw [← mul_assoc, mul_div_cancel₀ _ hQL]
      ring
    unfold gauge torusG
    rw [hcut]
    have hsum : ∀ m ∈ F, (Real.fourierChar (-((-(∑ i, (n m i : ℝ) * (Ms.zc.θ i / S.Q0)) /
        ModeSchedule.Lh h) * (y - xs))) : ℂ) =
        (Real.fourierChar (∑ i, (n m i : ℝ) * (Ms.torusξ S h i * (y - xs))) : ℂ) := by
      intro m _
      congr 2
      unfold torusξ
      rw [neg_div, neg_mul, neg_neg, Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mul_div_assoc, div_div]
      ring
    rw [Finset.sum_congr rfl fun m hm => by rw [hsum m hm]]
    ring
  rw [← hmain]
  refine h1.trans ?_
  -- the errors
  have hr := dyadicGridLength_pos Gd I.1
  have hyx : |y - xs| ≤ dyadicGridLength Gd I.1 := abs_sub_le_of_mem_cell' Gd hxs hy
  have hIJl : dyadicGridLength Gd I.1 ≤ dyadicGridLength Gd J.1 * (2 : ℝ)⁻¹ ^ (2 * S.K) :=
    dyadicGridLength_le_pow Gd (by push_cast; omega)
  have hIUl : dyadicGridLength Gd I.1 ≤ dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 * (2 :
      ℝ)⁻¹ ^ (4 * S.K) :=
    dyadicGridLength_le_pow Gd (by rw [hU1]; push_cast; omega)
  have hJ0 := dyadicGridLength_pos Gd J.1
  have hU0 := dyadicGridLength_pos Gd (ancAt Gd J (b - 4 * S.K)).1
  have hΛ0 : 0 ≤ Ms.Λ := le_trans (by positivity) (Ms.lam_le a.1)
  set! q : ℝ := (2 : ℝ)⁻¹ ^ S.K with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ^ 2 = (2 : ℝ)⁻¹ ^ (2 * S.K) := by rw [hq, ← pow_mul, mul_comm]
  have hq4 : q ^ 4 = (2 : ℝ)⁻¹ ^ (4 * S.K) := by rw [hq, ← pow_mul, mul_comm]
  have hqD : q ≤ (S.Dstar ^ 600)⁻¹ := by
    rw [hq, inv_pow]
    exact inv_anti₀ (by positivity) hK
  have hcardF : (Fintype.card (Ms.alive (ancAt Gd J (b - 4 * S.K))) : ℝ) ≤ S.Dstar := by
    rw [Fintype.card_coe]; exact hcard
  have hΞ0 : 0 ≤ S.Ξ := by unfold ModeSchedule.Ξ; positivity
  -- the slope error
  have e1 : (Fintype.card (Ms.alive (ancAt Gd J (b - 4 * S.K))) : ℝ) *
      (S.Ξ / dyadicGridLength Gd J.1) * |y - xs| ≤ S.Dstar * S.Ξ * q ^ 2 := by
    have : (S.Ξ / dyadicGridLength Gd J.1) * |y - xs| ≤ S.Ξ * q ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hJ0, hq2]
      have hΞ : 0 ≤ S.Ξ := by unfold ModeSchedule.Ξ; positivity
      calc S.Ξ * |y - xs| ≤ S.Ξ * (dyadicGridLength Gd J.1 * (2 : ℝ)⁻¹ ^ (2 * S.K)) :=
            mul_le_mul_of_nonneg_left (hyx.trans hIJl) hΞ
        _ = _ := by ring
    have hΞq : 0 ≤ S.Ξ * q ^ 2 := by unfold ModeSchedule.Ξ; positivity
    calc _ = (Fintype.card (Ms.alive (ancAt Gd J (b - 4 * S.K))) : ℝ) *
          ((S.Ξ / dyadicGridLength Gd J.1) * |y - xs|) := by ring
      _ ≤ S.Dstar * (S.Ξ * q ^ 2) := mul_le_mul hcardF this
          (mul_nonneg (div_nonneg hΞ0 hJ0.le) (abs_nonneg _)) hD0.le
      _ = _ := by ring
  -- the quadratic Taylor error
  have e2 : Ms.Λ / dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ^ 2 * (y - xs) ^ 2 ≤ S.Dstar *
      q ^ 2 := by
    have hy2 : (y - xs) ^ 2 ≤ (dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 * q ^ 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hyx.trans (hIUl.trans (le_of_eq (by rw [hq4]))))
        2
    have hq81 : q ^ 8 ≤ q ^ 2 := pow_le_pow_of_le_one hq0
      (by rw [hq]; exact pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    calc Ms.Λ / dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ^ 2 * (y - xs) ^ 2 ≤
          Ms.Λ / dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ^ 2 * (dyadicGridLength Gd
              (ancAt Gd J (b - 4 * S.K)).1 * q ^ 4) ^ 2 :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = Ms.Λ * q ^ 8 := by field_simp
      _ ≤ S.Dstar * q ^ 2 := mul_le_mul hΛ hq81 (by positivity) hD0.le
  -- the total against `D_*^{-150}`
  have hΞ : S.Ξ = S.Dstar ^ 1000 := rfl
  have hD1 : 1 ≤ S.Dstar := by linarith
  have htot : 2 * Real.pi * (S.Dstar * S.Ξ * q ^ 2 + S.Dstar * q ^ 2) ≤ (S.Dstar ^ 150)⁻¹ := by
    have hq2D : q ^ 2 ≤ ((S.Dstar ^ 600)⁻¹) ^ 2 := pow_le_pow_left₀ hq0 hqD 2
    have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have h16 : (16 : ℝ) ≤ S.Dstar ^ 4 := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ S.Dstar ^ 4 := pow_le_pow_left₀ (by norm_num) hD 4
    have hDD : S.Dstar ≤ S.Dstar * S.Ξ := by
      rw [hΞ]; nlinarith only [one_le_pow₀ (n := 1000) hD1, hD]
    have hpow : S.Dstar ^ 4 * (S.Dstar * S.Ξ) * ((S.Dstar ^ 600)⁻¹) ^ 2 ≤ (S.Dstar ^ 150)⁻¹ := by
      rw [hΞ]
      have e : S.Dstar ^ 4 * (S.Dstar * S.Dstar ^ 1000) * ((S.Dstar ^ 600)⁻¹) ^ 2 =
          (S.Dstar ^ 195)⁻¹ := by
        field_simp
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 (by norm_num))
    have hX : 0 ≤ S.Dstar * S.Ξ := by rw [hΞ]; positivity
    calc 2 * Real.pi * (S.Dstar * S.Ξ * q ^ 2 + S.Dstar * q ^ 2)
        ≤ 8 * (2 * (S.Dstar * S.Ξ) * q ^ 2) := by
          have : S.Dstar * q ^ 2 ≤ S.Dstar * S.Ξ * q ^ 2 :=
            mul_le_mul_of_nonneg_right hDD (by positivity)
          have h0 : 0 ≤ S.Dstar * S.Ξ * q ^ 2 + S.Dstar * q ^ 2 := by positivity
          nlinarith only [Real.pi_pos, hpi, hDD, h0]
      _ = 16 * (S.Dstar * S.Ξ) * q ^ 2 := by ring
      _ ≤ S.Dstar ^ 4 * (S.Dstar * S.Ξ) * ((S.Dstar ^ 600)⁻¹) ^ 2 := by
          have := mul_le_mul h16 hq2D (by positivity) (by positivity)
          nlinarith only [hD, hDD, this]
      _ ≤ _ := hpow
  have hα : 0 ≤ ∑ m ∈ F, ‖α m‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc 2 * Real.pi * ((Fintype.card (Ms.alive (ancAt Gd J (b - 4 * S.K))) : ℝ) *
        (S.Ξ / dyadicGridLength Gd J.1) * |y - xs| +
        Ms.Λ / dyadicGridLength Gd (ancAt Gd J (b - 4 * S.K)).1 ^ 2 * (y - xs) ^ 2) * ∑ m ∈ F, ‖α m‖
      ≤ 2 * Real.pi * (S.Dstar * S.Ξ * q ^ 2 + S.Dstar * q ^ 2) * ∑ m ∈ F, ‖α m‖ := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right htot hα

end ModeSystem

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lines 2463-2470 (the core subtotals as physical functions): the physical function of
the subtotal on a cell of a core component is a.e. `1_I Σ_{m ∈ K} c_m wave_m`. -/
theorem augPhys_compSub (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) (K : Finset (D.Ms l G).Md) :
    augPhys (D.compSub l G I K) =ᵐ[volume] (dyadicGridCell A.G I.1 I.2).indicator
      (fun y => ∑ m ∈ K, D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m *
        (D.Ms l G).wave m y) := by
  set X : ColumnL2 (D.Ms l G).Md :=
    ∑ m ∈ K, D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m • (D.Ms l G).cellMode (D.preAt I) m
  set! z := columnL2Restriction (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2) (physEmbed (D.Ms l G).Md (bf.Lab ⊕ Fin fp.Mc) X)
  have h2 := columnL2Indicator_coeFn (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2) (physEmbed (D.Ms l G).Md (bf.Lab ⊕ Fin fp.Mc) X)
  have h3 := physEmbed_coeFn_none (W := bf.Lab ⊕ Fin fp.Mc) X
  have h4 := (D.Ms l G).cellMode_sum_none (D.preAt I) K
    (D.c l G (A.blkStart D.S.K I.1) (D.preAt I))
  have hIJ := D.subset_preAt I
  filter_upwards [h2, h3, h4] with y e2 e3 e4
  unfold augPhys compSub
  change (columnL2Indicator (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
    (physEmbed (D.Ms l G).Md (bf.Lab ⊕ Fin fp.Mc) X) :
      ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y none = _
  rw [e2]
  by_cases hy : y ∈ dyadicGridCell A.G I.1 I.2
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, e3]
    exact e4 (hIJ hy)
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    rfl

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The frequency box (blueprint `eq:frequency-box`, lines 2471-2476) -/

namespace ModeSchedule
variable (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}

variable {S} in
/-- The common cutoff `B_*` is at most `A₀` (blueprint line 1955: `A₀` is a power of
`C_* 6^{R_*} B_* D_*`). -/
theorem Valid.Bstar_le_A0 (hV : S.Valid Cj CA CT CK δs W) (hCA : 1 ≤ CA) (hd2 : 2 ≤ S.dmax)
    (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) : S.Bstar ≤ S.A0 := by
  have hC := hV.two_le_Cstar hd2 hD
  have h6 : (1 : ℝ) ≤ 6 ^ S.Rht := one_le_pow₀ (by norm_num)
  set X := S.Cstar * 6 ^ S.Rht * S.Bstar * S.Dstar
  have hBX : S.Bstar ≤ X := by
    have h1 : 1 ≤ S.Cstar * 6 ^ S.Rht := one_le_mul_of_one_le_of_one_le (by linarith) h6
    calc S.Bstar = 1 * S.Bstar * 1 := by ring
      _ ≤ S.Cstar * 6 ^ S.Rht * S.Bstar * S.Dstar := by
          gcongr
          linarith
  have hX1 : 1 ≤ X := le_trans (by linarith) hBX
  calc S.Bstar ≤ X := hBX
    _ = X ^ 1 := (pow_one X).symm
    _ ≤ X ^ CA := pow_le_pow_right₀ hX1 hCA
    _ ≤ S.A0 := hV.A0_ge

/-- `B_* L_h ≤ E_h` (blueprint line 2055: `E_h ≥ B_* L_h`) for `6 ≤ A₀` and `B_* ≤ A₀`. -/
theorem Bstar_Lh_le_Eh (hA6 : 6 ≤ S.A0) (hBA : S.Bstar ≤ S.A0) (h : ℕ) :
    S.Bstar * Lh h ≤ S.Eh h := by
  unfold Lh Eh
  rw [pow_succ']
  exact mul_le_mul hBA (pow_le_pow_left₀ (by norm_num) hA6 h) (by positivity)
    (le_trans (by norm_num) hA6)

end ModeSchedule

/-- The truncation tail of the periodic cutoff is at most twice the gauge tail over `2^K`. -/
theorem cutTail_le_gaugeTail (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (K : ℕ) :
    cutTail d δ K ≤ 2 * gaugeTail d δ / 2 ^ K := by
  unfold cutTail gaugeTail
  have hb := one_le_bumpConst
  set Y := (d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ)))
  have hY : 0 ≤ Y := by positivity
  have hpow : Y ^ (d + 1) ≤ (2 * Y) ^ (d + 1) :=
    pow_le_pow_left₀ hY (by linarith) (d + 1)
  have h7 : (0 : ℝ) ≤ 7 ^ d := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt d ^ (d + 1) := by positivity
  gcongr

/-- Blueprint lines 1944 and 2471 ("truncate the Fourier series to tails at most `D_*^{-300}`"):
with the Fourier cutoff `K_f` of the schedule (`2 gaugeTail / 2^{K_f} ≤ D_*^{-300}`), the
truncation tail of every true periodic cutoff of width `δ` in dimension `d` is at most
`D_*^{-300}`. -/
theorem cutTail_le_of_Kf (d : ℕ) {δ : ℝ} (hδ : 0 < δ) {Kf : ℕ} {D : ℝ} (hD : 0 < D)
    (hKf : 2 * gaugeTail d δ / 2 ^ Kf * D ^ 300 ≤ 1) : cutTail d δ Kf ≤ (D ^ 300)⁻¹ := by
  refine (cutTail_le_gaugeTail d hδ Kf).trans ?_
  have hD3 : 0 < D ^ 300 := by positivity
  calc 2 * gaugeTail d δ / 2 ^ Kf = (2 * gaugeTail d δ / 2 ^ Kf * D ^ 300) / D ^ 300 := by
        field_simp
    _ ≤ 1 / D ^ 300 := div_le_div_of_nonneg_right hKf hD3.le
    _ = (D ^ 300)⁻¹ := one_div _

open Classical in
/-- Blueprint `eq:frequency-box` for the truncated cutoffs: in the torus coordinates `ξ = ϑ / L_h`
the frequencies `Q₀ L_h v` of the truncated cutoffs (`|v|_∞ ≤ 2^{K_f + 1}`, `Q₀ 2^{K_f + 1} ≤ B_*`)
lie in the box `B'_h = D_*^5 E_h` (the cutoff indices `B_* L_h ≤ E_h`). -/
theorem freqBox_cutoff (S : ModeSchedule) (hA6 : 6 ≤ S.A0) (hBA : S.Bstar ≤ S.A0) {Kf : ℕ}
    (hQB : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Bstar) (hD : 1 ≤ S.Dstar) {d : ℕ} {v : Fin d → ℤ}
    (hv : v ∈ frequencyBox d (2 ^ (Kf + 1))) (h : ℕ) (i : Fin d) :
    |(S.Q0 : ℝ) * ModeSchedule.Lh h * (v i : ℝ)| ≤ S.Dstar ^ 5 * S.Eh h := by
  have hvi := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hv) i)
  have habs : |(v i : ℝ)| ≤ 2 ^ (Kf + 1) := by
    have h1 : ((-((2 ^ (Kf + 1) : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((v i : ℤ) : ℝ) := Int.cast_le.mpr hvi.1
    have h2 : ((v i : ℤ) : ℝ) ≤ (((2 ^ (Kf + 1) : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr hvi.2
    push_cast at h1 h2
    rw [abs_le]; exact ⟨h1, h2⟩
  have hL : 0 ≤ ModeSchedule.Lh h := by unfold ModeSchedule.Lh; positivity
  have hE : S.Bstar * ModeSchedule.Lh h ≤ S.Eh h := S.Bstar_Lh_le_Eh hA6 hBA h
  have hE0 : 0 ≤ S.Eh h := by
    unfold ModeSchedule.Eh; exact pow_nonneg (le_trans (by norm_num) hA6) _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ S.Q0 * ModeSchedule.Lh h)]
  calc (S.Q0 : ℝ) * ModeSchedule.Lh h * |(v i : ℝ)| ≤
        (S.Q0 : ℝ) * ModeSchedule.Lh h * 2 ^ (Kf + 1) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (S.Q0 * 2 ^ (Kf + 1)) * ModeSchedule.Lh h := by ring
    _ ≤ S.Bstar * ModeSchedule.Lh h := mul_le_mul_of_nonneg_right hQB hL
    _ ≤ S.Eh h := hE
    _ = 1 * S.Eh h := (one_mul _).symm
    _ ≤ S.Dstar ^ 5 * S.Eh h := mul_le_mul_of_nonneg_right (one_le_pow₀ hD) hE0

open Classical in
/-- Blueprint `eq:frequency-box` for the truncated common progression multiplier: its frequencies
`L_h v` (`|v|_∞ ≤ 2^{K_f + 1} ≤ B_*`) lie in the box `B'_h = D_*^5 E_h`. -/
theorem freqBox_mult (S : ModeSchedule) (hA6 : 6 ≤ S.A0) (hBA : S.Bstar ≤ S.A0) {Kf : ℕ}
    (hQ : 1 ≤ S.Q0) (hQB : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Bstar) (hD : 1 ≤ S.Dstar) {d : ℕ}
    {v : Fin d → ℤ} (hv : v ∈ frequencyBox d (2 ^ (Kf + 1))) (h : ℕ) (i : Fin d) :
    |ModeSchedule.Lh h * (v i : ℝ)| ≤ S.Dstar ^ 5 * S.Eh h := by
  refine le_trans ?_ (freqBox_cutoff S hA6 hBA hQB hD hv h i)
  have hQ1 : (1 : ℝ) ≤ S.Q0 := by exact_mod_cast hQ
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : 0 ≤ |ModeSchedule.Lh h| * |(v i : ℝ)| := by positivity
  calc |ModeSchedule.Lh h| * |(v i : ℝ)| = 1 * (|ModeSchedule.Lh h| * |(v i : ℝ)|) :=
        (one_mul _).symm
    _ ≤ |(S.Q0 : ℝ)| * (|ModeSchedule.Lh h| * |(v i : ℝ)|) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ S.Q0)]
        exact mul_le_mul_of_nonneg_right hQ1 h1
    _ = _ := by ring

/-- The full Fourier norm bound of the true periodic cutoff. -/
noncomputable def cutNorm (d : ℕ) (δ : ℝ) : ℝ :=
  5 ^ d + 2 * ((7 : ℝ) ^ d * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
    (2 / δ)))) ^ (d + 1) * Real.sqrt d ^ (d + 1))

/-- The full Fourier norm of the cutoff is at most that of the squared gauge (which the schedule
covers by `D_*`, blueprint line 1944). -/
theorem cutNorm_le_gaugeSqNorm (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : cutNorm d δ ≤ gaugeSqNorm d δ := by
  unfold cutNorm gaugeSqNorm gaugeTail
  have hb := one_le_bumpConst
  set Y := (d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ)))
  have hY : 0 ≤ Y := by positivity
  have hpow : Y ^ (d + 1) ≤ (2 * Y) ^ (d + 1) := pow_le_pow_left₀ hY (by linarith) (d + 1)
  have h7 : (0 : ℝ) ≤ 7 ^ d := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt d ^ (d + 1) := by positivity
  gcongr

/-- Blueprint lines 2471-2476 ("absolute Fourier costs ... are fixed powers of `D_*`; dilation of
indices does not change coefficient sums"), for the true periodic cutoff: its Fourier
coefficients have modulus at most one, every finite absolute coefficient sum is at most `cutNorm`
(at most `gaugeSqNorm ≤ D_*`), and the truncation to the box `|v|_∞ ≤ 2^{K+1}` is uniformly
within `cutTail` (at most `D_*^{-300}` at the Fourier cutoff of the schedule). -/
theorem cutoffP_truncate_full {d : ℕ} (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ)
    (K : ℕ) :
    ∃ c : (Fin d → ℤ) → ℂ, (∀ v, ‖c v‖ ≤ 1) ∧
      (∀ s : Finset (Fin d → ℤ), ∑ v ∈ s, ‖c v‖ ≤ cutNorm d δ) ∧ ∀ w,
      ‖cutoffP δ ρ w - ∑ v ∈ frequencyBox d (2 ^ (K + 1)),
        c v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ cutTail d δ K := by
  set R := 2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ))
  have hR : 0 ≤ R := by have := one_le_bumpConst; positivity
  have hF : ContDiff ℝ (⊤ : ℕ∞) (cutoffP δ ρ) := (chartCoordinateProduct_smooth (d := d)
    (fractProfile_contDiff hδ)).comp (contDiff_id.sub contDiff_const)
  have hD : ∀ w, ‖iteratedFDeriv ℝ (d + 1) (cutoffP δ ρ) w‖ ≤ ((d : ℝ) * R) ^ (d + 1) := by
    intro w
    have e : cutoffP δ ρ = fun w => chartCoordinateProduct (fractProfile δ) (w - ρ) := rfl
    rw [e, iteratedFDeriv_comp_sub]
    refine chartCoordinateProduct_derivative_geometric (fractProfile_contDiff hδ) (w - ρ) hR
      fun j hj x => ?_
    exact (fractProfile_deriv_le hδ hj x).trans (le_of_eq rfl)
  obtain ⟨h1, h2, h3⟩ := periodic_truncate_full hd (cutoffP δ ρ) hF
    (fun w j => cutoffP_periodic δ ρ w j) (by positivity) hD (cutoffP_norm_le δ ρ) K
  refine ⟨periodicFourierCoeff (cutoffP δ ρ), h1, fun s => (h2 s).trans (le_of_eq ?_),
    fun w => (h3 w).trans (le_of_eq ?_)⟩
  · unfold cutNorm; ring
  · unfold cutTail; ring

/-! ## The truncated multiplier `R_z` (blueprint line 2478) -/

/-- Blueprint line 2478 ("in coordinates `u = ξ(y_{l'} - x*)`, `v = ξ t`, denote its shifted
truncated version by `R_z(u, v)`; it has uniformly bounded supremum, including for different
offsets and anchors"): the truncated common progression multiplier of any anchor `l'`, re-centered
at `x*` and lifted to the torus by `L`, is bounded by `1 + τ_m` at every pair of torus points,
where `τ_m` is its truncation tail. -/
theorem multTrunc_sup {d : ℕ} {δ : ℝ} {Q0 : ℕ} (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) (K : ℕ)
    (cm0 : (Fin (d + d) → ℤ) → ℂ) {τm : ℝ}
    (hcmT : ∀ w, ‖gaugeMult δ Q0 l' C ρ w - ∑ v ∈ frequencyBox (d + d) (2 ^ (K + 1)),
      cm0 v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ τm)
    (θ : Fin d → ℝ) (xs : ℝ) (L : ℕ) (u v : StandardTorus d) :
    ‖∑ p ∈ frequencyBox (d + d) (2 ^ (K + 1)), cm0 p *
        (Real.fourierChar (∑ a, (p (Fin.castAdd d a) : ℝ) * (θ a * xs / Q0)) : ℂ) *
        (torusCharacter ((L : ℤ) • fun a => p (Fin.castAdd d a)) u *
          torusCharacter ((L : ℤ) • fun a => p (Fin.natAdd d a)) v)‖ ≤ 1 + τm := by
  choose w₁ hw₁ using fun i => QuotientAddGroup.mk_surjective (u i)
  choose w₂ hw₂ using fun i => QuotientAddGroup.mk_surjective (v i)
  have hu : u = torusMk w₁ := funext fun i => (hw₁ i).symm
  have hv : v = torusMk w₂ := funext fun i => (hw₂ i).symm
  subst hu hv
  set W : Fin (d + d) → ℝ := Fin.append (fun a => (L : ℝ) * w₁ a + θ a * xs / Q0)
    (fun a => (L : ℝ) * w₂ a)
  have e : ∑ p ∈ frequencyBox (d + d) (2 ^ (K + 1)), cm0 p *
      (Real.fourierChar (∑ a, (p (Fin.castAdd d a) : ℝ) * (θ a * xs / Q0)) : ℂ) *
      (torusCharacter ((L : ℤ) • fun a => p (Fin.castAdd d a)) (torusMk w₁) *
        torusCharacter ((L : ℤ) • fun a => p (Fin.natAdd d a)) (torusMk w₂)) =
      ∑ p ∈ frequencyBox (d + d) (2 ^ (K + 1)), cm0 p *
        (Real.fourierChar (∑ i, (p i : ℝ) * W i) : ℂ) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [torusCharacter_mk, torusCharacter_mk, mul_assoc, ← Circle.coe_mul, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, Fin.sum_univ_add]
    congr 3
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [W, Fin.append_left, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [W, Fin.append_right, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
  rw [e]
  have h1 := hcmT W
  have h2 := gaugeMult_norm_le δ Q0 l' C ρ W
  set M := gaugeMult δ Q0 l' C ρ W
  set T := ∑ p ∈ frequencyBox (d + d) (2 ^ (K + 1)),
    cm0 p * (Real.fourierChar (∑ i, (p i : ℝ) * W i) : ℂ)
  calc ‖T‖ = ‖M - (M - T)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖M‖ + ‖M - T‖ := norm_sub_le _ _
    _ ≤ 1 + τm := add_le_add h2 h1

/-! ## The declaration `common-height` (blueprint lines 2463-2480) -/

end TrilinearHT.Auto

end
