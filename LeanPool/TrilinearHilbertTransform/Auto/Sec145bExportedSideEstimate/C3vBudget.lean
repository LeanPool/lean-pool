/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec145bExportedSideEstimate.Setup

/-!
# Trilinear Hilbert transform: C3v_budget
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideLeafM
variable (T : fp.SideLeafM)

open scoped Classical in
private def C3vBudgetHGrStatement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (T : fp.SideLeafM)
    (S : Finset (ℤ × ℤ))
    (_ : S ⊆ A.cells)
    (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp)
    (_ : ∀ I ∈ S, gs I ⊆ gset)
    (ScG : bf.Grp → Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      J.1 J.2 → A.blkStart T.K I.1 ≤ J.1 → J ∈ ScG G)
    (Lp : ℕ)
    (Jm : ℕ)
    (_ : ∀ (l : Fin (4 : ℕ)), (T.pe l).length ≤ Lp)
    (_ : ∀ (c d : Fin (4 : ℕ)) (i i' : ℕ), (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    (C₀ : ℝ)
    (B₀ : ℝ)
    (_ : (0 : ℝ) < C₀)
    (Bs : ℝ)
    (Eb : ℝ)
    (_ : (0 : ℝ) ≤ Eb)
    (_ : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖T.sv l G I‖ ^ (2 : ℕ) ≤ Bs)
    (_ : ∀ (a c d : Fin (4 : ℕ)) (i i' j : ℕ), j < (T.desc c d (T.tOf c i) (T.tOf d
      i')).length → ¬T.cumY c d (T.tOf c i) (T.tOf d i') j → ∑ G ∈ gset, ∑ J ∈ ScG G,
      T.pYe a c d G (T.tOf c i) (T.tOf d i') j J ≤ (↑fp.P : ℝ) * Eb)
    (_ : ∀ (a c d : Fin (4 : ℕ)) (i i' j : ℕ), j < (T.desc c d (T.tOf c i) (T.tOf d
      i')).length → ¬T.cumF c d (T.tOf c i) (T.tOf d i') j → ∑ G ∈ gset, ∑ J ∈ ScG G,
      T.dFe a c d G (T.tOf c i) (T.tOf d i') j J ≤ Eb)
    (_ : (0 : ℝ) ≤ T.frzB C₀ Eb)
    (_ : (0 : ℝ) ≤ Bs),
  let K' : ℝ :=
    (2 : ℝ) * ((1 : ℝ) + (5 : ℝ) * (↑Jm : ℝ))
  let D : ℝ :=
    ((2 : ℝ) / (↑fp.P : ℝ) * localFormUniformConstant κ') ^ (2 : ℕ) * (6 : ℝ)
  let N4 : ℝ :=
    (↑Lp : ℝ) * (↑Lp : ℝ) * ((↑Jm : ℝ) * (5 : ℝ)) * T.frzB C₀ Eb
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), (Finset.range (T.pe l).length).card ≤ Lp)
    (_ : ∀ (c d : Fin (4 : ℕ)) (i i' : ℕ), (Finset.range (T.desc c d (T.tOf c i) (T.tOf d
      i')).length).card ≤ Jm),
  let Y : ℝ :=
    (2 : ℝ) * (localFormUniformConstant κ' * B₀) ^ (2 : ℕ) * Bs + (↑Lp : ℝ) ^ (2 : ℕ) *
      K' * (D * N4)
  ∀ (_ : Y = (2 : ℝ) * (localFormUniformConstant κ' * B₀) ^ (2 : ℕ) * Bs + (↑Lp : ℝ) ^ (2 :
      ℕ) * K' * (D * N4))
    (_ : (0 : ℝ) ≤ Y),
  ∀ (a b c d : Fin (4 : ℕ)), ∑ I ∈ S, ∑ G ∈ gs I, dyadicGridLength A.G I.1 * T.thirdG
    C₀ B₀ a b c d G I ^ (2 : ℕ) ≤ Y


open scoped Classical in
private def C3vBudgetStage1Statement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (T : fp.SideLeafM)
    (S : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp)
    (G₀ : bf.Grp)
    (Lp : ℕ)
    (Jm : ℕ)
    (C₀ : ℝ)
    (B₀ : ℝ)
    (Cy : ℝ)
    (Bs : ℝ)
    (BU : ℝ)
    (Eb : ℝ),
  let K' : ℝ :=
    (2 : ℝ) * ((1 : ℝ) + (5 : ℝ) * (↑Jm : ℝ))
  let D : ℝ :=
    ((2 : ℝ) / (↑fp.P : ℝ) * localFormUniformConstant κ') ^ (2 : ℕ) * (6 : ℝ)
  let N4 : ℝ :=
    (↑Lp : ℝ) * (↑Lp : ℝ) * ((↑Jm : ℝ) * (5 : ℝ)) * T.frzB C₀ Eb
  let X : ℝ :=
    (↑Lp : ℝ) ^ (2 : ℕ) * K' * ((↑Lp : ℝ) ^ (2 : ℕ) * (localFormUniformConstant κ' ^ (2
      : ℕ) * ((8 : ℝ) * Cy ^ (2 : ℕ) * BU)) + D * N4)
  ∀ (_ : X = (↑Lp : ℝ) ^ (2 : ℕ) * K' * ((↑Lp : ℝ) ^ (2 : ℕ) * (localFormUniformConstant κ' ^
      (2 : ℕ) * ((8 : ℝ) * Cy ^ (2 : ℕ) * BU)) + D * N4))
    (_ : ∀ (a b c d : Fin (4 : ℕ)), ∑ I ∈ S, dyadicGridLength A.G I.1 * T.thirdS C₀ a b c d
      G₀ I ^ (2 : ℕ) ≤ X),
  let Y : ℝ :=
    (2 : ℝ) * (localFormUniformConstant κ' * B₀) ^ (2 : ℕ) * Bs + (↑Lp : ℝ) ^ (2 : ℕ) *
      K' * (D * N4)
  ∀ (_ : Y = (2 : ℝ) * (localFormUniformConstant κ' * B₀) ^ (2 : ℕ) * Bs + (↑Lp : ℝ) ^ (2 :
      ℕ) * K' * (D * N4))
    (_ : ∀ (a b c d : Fin (4 : ℕ)), ∑ I ∈ S, ∑ G ∈ gs I, dyadicGridLength A.G I.1 * T.thirdG
      C₀ B₀ a b c d G I ^ (2 : ℕ) ≤ Y),
  ∑ I ∈ S, dyadicGridLength A.G I.1 * T.C3v C₀ B₀ G₀ gs I ^ (2 : ℕ) ≤ (2 : ℝ) * ((36 :
    ℝ) * (256 : ℝ) * (256 : ℝ) * X) + (2 : ℝ) * ((36 : ℝ) * (256 : ℝ) * (256 : ℝ) * Y)




private theorem C3v_budget_hGr : C3vBudgetHGrStatement := by
  classical
  intro κ' c₀ A bf fp T S hS gs gset hgs ScG hScG Lp Jm hLp hJm C₀ B₀ hC₀ Bs Eb hEb hBs hEpG hEFG
    hFb hBs0 K' D N4 hcd hjd Y hY hY0 a b c d
  unfold thirdG
  by_cases hV : T.Val a b c d
  · by_cases hU : T.Ucase c d
    · simp only [hV, hU, ite_true]
      have e : ∀ I G l, dyadicGridLength A.G I.1 * T.ns l G I ^ 2 = ‖T.sv l G I‖ ^ 2 := by
        intro I G l
        have hL := dyadicGridLength_pos A.G I.1
        unfold ns
        rw [div_pow, Real.sq_sqrt hL.le]
        field_simp
      have hpt : ∀ I G, dyadicGridLength A.G I.1 * (localFormUniformConstant κ' * B₀ *
          (T.ns c G I + T.ns d G I)) ^ 2 ≤
          2 * (localFormUniformConstant κ' * B₀) ^ 2 * ∑ l, ‖T.sv l G I‖ ^ 2 := by
        intro I G
        have hL := (dyadicGridLength_pos A.G I.1).le
        have h2 := add_sq_le_two (T.ns c G I) (T.ns d G I)
        have hcd : ‖T.sv c G I‖ ^ 2 + ‖T.sv d G I‖ ^ 2 ≤ ∑ l, ‖T.sv l G I‖ ^ 2 := by
          rw [← Finset.sum_pair (f := fun l => ‖T.sv l G I‖ ^ 2)
            (fun h => hV.2.2.2.2.2.1 h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => sq_nonneg _
        calc dyadicGridLength A.G I.1 * (localFormUniformConstant κ' * B₀ *
              (T.ns c G I + T.ns d G I)) ^ 2
            = (localFormUniformConstant κ' * B₀) ^ 2 *
              (dyadicGridLength A.G I.1 * (T.ns c G I + T.ns d G I) ^ 2) := by ring
          _ ≤ (localFormUniformConstant κ' * B₀) ^ 2 *
              (dyadicGridLength A.G I.1 * (2 * T.ns c G I ^ 2 + 2 * T.ns d G I ^ 2)) := by
              gcongr
          _ = 2 * (localFormUniformConstant κ' * B₀) ^ 2 *
              (‖T.sv c G I‖ ^ 2 + ‖T.sv d G I‖ ^ 2) := by
              rw [← e I G c, ← e I G d]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hcd (by positivity)
      have hY' : 2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs ≤ Y := by
        rw [hY]
        have : 0 ≤ Lp ^ 2 * K' * (D * N4) := by positivity
        linarith
      calc ∑ I ∈ S, ∑ G ∈ gs I, dyadicGridLength A.G I.1 * (localFormUniformConstant κ' * B₀ *
            (T.ns c G I + T.ns d G I)) ^ 2
          ≤ ∑ I ∈ S, ∑ G ∈ gs I,
              2 * (localFormUniformConstant κ' * B₀) ^ 2 * ∑ l, ‖T.sv l G I‖ ^ 2 :=
            Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun G _ => hpt I G
        _ = 2 * (localFormUniformConstant κ' * B₀) ^ 2 *
              ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 := by
            simp only [Finset.mul_sum]
        _ ≤ 2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs :=
            mul_le_mul_of_nonneg_left hBs (by positivity)
        _ ≤ Y := hY'
    · simp only [hV, hU, ite_true, ite_false]
      have hcell : ∀ I ∈ S, ∀ G ∈ gs I, dyadicGridLength A.G I.1 * T.thG C₀ a c d G I ^ 2 ≤
          Lp ^ 2 * K' * (D * ∑ i' ∈ Finset.range (T.pe d).length,
            ∑ i ∈ Finset.range (T.pe c).length,
            ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
              ∑ _o ∈ Finset.range 5, T.frzGrE C₀ a c d G (T.tOf c i) (T.tOf d i') j I) :=
        fun I _ G _ => T.thG_sq C₀ a c d G I hLp (hJm c d)
      have hF : ∑ I ∈ S, ∑ G ∈ gs I, ∑ i' ∈ Finset.range (T.pe d).length,
          ∑ i ∈ Finset.range (T.pe c).length,
          ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
            ∑ _o ∈ Finset.range 5, T.frzGrE C₀ a c d G (T.tOf c i) (T.tOf d i') j I ≤ N4 := by
        rw [Finset.sum_congr rfl fun I _ => sum_swap4 (gs I) _ _ _ _ _, sum_swap4]
        refine sum4_bound _ _ (fun i i' => Finset.range (T.desc c d (T.tOf c i)
          (T.tOf d i')).length) _ hFb (hcd d) (hcd c) (hjd c d) fun i' _ i _ j hj => ?_
        refine (T.grE_sum hC₀ a c d _ _ j S hS gs gset hgs ScG hScG (by positivity) hEb
          (hEpG a c d i i' j (Finset.mem_range.mp hj))
          (hEFG a c d i i' j (Finset.mem_range.mp hj))).trans ?_
        unfold frzB
        have hE0 : 0 ≤ C₀ ^ 2 * ((64 + 8 * T.K) * Eb) := by positivity
        nlinarith only [hE0]
      have hY' : Lp ^ 2 * K' * (D * N4) ≤ Y := by
        rw [hY]
        have : 0 ≤ 2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs := by positivity
        linarith
      calc ∑ I ∈ S, ∑ G ∈ gs I, dyadicGridLength A.G I.1 * T.thG C₀ a c d G I ^ 2
          ≤ ∑ I ∈ S, ∑ G ∈ gs I, Lp ^ 2 * K' * (D * ∑ i' ∈ Finset.range (T.pe d).length,
              ∑ i ∈ Finset.range (T.pe c).length,
              ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
                ∑ _o ∈ Finset.range 5, T.frzGrE C₀ a c d G (T.tOf c i) (T.tOf d i') j I) :=
            Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun G hG => hcell I hI G hG
        _ = Lp ^ 2 * K' * (D * ∑ I ∈ S, ∑ G ∈ gs I, ∑ i' ∈ Finset.range (T.pe d).length,
              ∑ i ∈ Finset.range (T.pe c).length,
              ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
                ∑ _o ∈ Finset.range 5, T.frzGrE C₀ a c d G (T.tOf c i) (T.tOf d i') j I) := by
            simp only [Finset.mul_sum]
        _ ≤ Lp ^ 2 * K' * (D * N4) := by gcongr
        _ ≤ Y := hY'
  · simp only [hV, ite_false, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Finset.sum_const_zero]
    exact hY0
-- combination



private theorem C3v_budget_stage_1 : C3vBudgetStage1Statement := by
  classical
  intro κ' c₀ A bf fp T S gs G₀ Lp Jm C₀ B₀ Cy Bs BU Eb K' D N4 X hX hSh Y hY hGr
  refine (T.C3v_sq_le C₀ B₀ G₀ gs S).trans ?_
  have hS1 : ∑ I ∈ S, dyadicGridLength A.G I.1 * (6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      ∑ d : Fin 4, T.thirdS C₀ a b c d G₀ I) ^ 2 ≤ 36 * 256 * 256 * X := by
    calc _ ≤ ∑ I ∈ S, 36 * 256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
          dyadicGridLength A.G I.1 * T.thirdS C₀ a b c d G₀ I ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          have hL := (dyadicGridLength_pos A.G I.1).le
          have h := sq_sum_fin4_4 (fun a b c d => T.thirdS C₀ a b c d G₀ I)
          calc dyadicGridLength A.G I.1 * (6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdS C₀ a b c d G₀ I) ^ 2
              = 36 * (dyadicGridLength A.G I.1 * (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdS C₀ a b c d G₀ I) ^ 2) := by ring
            _ ≤ 36 * (dyadicGridLength A.G I.1 * (256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdS C₀ a b c d G₀ I ^ 2)) := by gcongr
            _ = _ := by simp only [Finset.mul_sum]; ring_nf
      _ = 36 * 256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
          ∑ I ∈ S, dyadicGridLength A.G I.1 * T.thirdS C₀ a b c d G₀ I ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
      _ ≤ 36 * 256 * ∑ _a : Fin 4, ∑ _b : Fin 4, ∑ _c : Fin 4, ∑ _d : Fin 4, X := by
          gcongr with a _ b _ c _ d _
          exact hSh a b c d
      _ = 36 * 256 * 256 * X := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hG1 : ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I, (6 * ∑ a : Fin 4, ∑ b : Fin 4,
      ∑ c : Fin 4, ∑ d : Fin 4, T.thirdG C₀ B₀ a b c d G I) ^ 2 ≤ 36 * 256 * 256 * Y := by
    calc _ ≤ ∑ I ∈ S, ∑ G ∈ gs I, 36 * 256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          ∑ d : Fin 4, dyadicGridLength A.G I.1 * T.thirdG C₀ B₀ a b c d G I ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun G _ => ?_
          have hL := (dyadicGridLength_pos A.G I.1).le
          have h := sq_sum_fin4_4 (fun a b c d => T.thirdG C₀ B₀ a b c d G I)
          calc dyadicGridLength A.G I.1 * (6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdG C₀ B₀ a b c d G I) ^ 2
              = 36 * (dyadicGridLength A.G I.1 * (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdG C₀ B₀ a b c d G I) ^ 2) := by ring
            _ ≤ 36 * (dyadicGridLength A.G I.1 * (256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
                ∑ d : Fin 4, T.thirdG C₀ B₀ a b c d G I ^ 2)) := by gcongr
            _ = _ := by simp only [Finset.mul_sum]; ring_nf
      _ = 36 * 256 * ∑ I ∈ S, ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          ∑ d : Fin 4, dyadicGridLength A.G I.1 * T.thirdG C₀ B₀ a b c d G I ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ => (Finset.mul_sum _ _ _).symm
      _ = 36 * 256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
          ∑ I ∈ S, ∑ G ∈ gs I, dyadicGridLength A.G I.1 * T.thirdG C₀ B₀ a b c d G I ^ 2 := by
          congr 1
          refine (sum_comm_out S gs Finset.univ _).trans (Finset.sum_congr rfl fun a _ => ?_)
          refine (sum_comm_out S gs Finset.univ _).trans (Finset.sum_congr rfl fun b _ => ?_)
          refine (sum_comm_out S gs Finset.univ _).trans (Finset.sum_congr rfl fun c _ => ?_)
          exact sum_comm_out S gs Finset.univ _
      _ ≤ 36 * 256 * ∑ _a : Fin 4, ∑ _b : Fin 4, ∑ _c : Fin 4, ∑ _d : Fin 4, Y := by
          gcongr with a _ b _ c _ d _
          exact hGr a b c d
      _ = 36 * 256 * 256 * Y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hX] at hS1
  rw [hY] at hG1
  linarith


open Classical in
/-- Blueprint lines 2375-2394 (the third strong factors in integrated form, shared histories
counted once): the length-weighted squares of the cell values `C₃` of the third strong factors are
bounded by the `U` energy `B_U` of the cells (counted once, not per group), the side masses `B_s`,
and the freeze budgets `frzB` of the steps, which come from the freeze energies of the shared
outputs (over the ancestors `S_c` of the uses) and the joint freeze energies of the group-indexed
outputs (over the ancestors `S_G` of the uses of each group). -/
theorem C3v_budget (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (G₀ : bf.Grp) (Sc : Finset (ℤ × ℤ))
    (hSc : ∀ I ∈ S, ∀ J ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 →
      A.blkStart T.K I.1 ≤ J.1 → J ∈ Sc)
    (ScG : bf.Grp → Finset (ℤ × ℤ))
    (hScG : ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → A.blkStart T.K I.1 ≤ J.1 →
        J ∈ ScG G)
    {Lp Jm : ℕ} (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    {C₀ B₀ Cy : ℝ} (hC₀ : 0 < C₀)
    (hy : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {Bs BU Eb : ℝ} (hEb : 0 ≤ Eb)
    (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (hEi : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      ∑ J ∈ Sc, T.iYe a c d G₀ (T.tOf c i) (T.tOf d i') j J ≤ Eb)
    (hEp : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      T.cumY c d (T.tOf c i) (T.tOf d i') j →
      ∑ J ∈ Sc, T.pYe a c d G₀ (T.tOf c i) (T.tOf d i') j J ≤ fp.P * Eb)
    (hEF : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      T.cumF c d (T.tOf c i) (T.tOf d i') j →
      ∑ J ∈ Sc, T.dFe a c d G₀ (T.tOf c i) (T.tOf d i') j J ≤ Eb)
    (hEpG : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      ¬ T.cumY c d (T.tOf c i) (T.tOf d i') j →
      ∑ G ∈ gset, ∑ J ∈ ScG G, T.pYe a c d G (T.tOf c i) (T.tOf d i') j J ≤ fp.P * Eb)
    (hEFG : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      ¬ T.cumF c d (T.tOf c i) (T.tOf d i') j →
      ∑ G ∈ gset, ∑ J ∈ ScG G, T.dFe a c d G (T.tOf c i) (T.tOf d i') j J ≤ Eb) :
    ∑ I ∈ S, dyadicGridLength A.G I.1 * T.C3v C₀ B₀ G₀ gs I ^ 2 ≤
      2 * (36 * 256 * 256 * (Lp ^ 2 * (2 * (1 + 5 * Jm)) *
        (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 * BU)) +
          (2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
            (Lp * Lp * (Jm * 5) * T.frzB C₀ Eb)))) +
      2 * (36 * 256 * 256 * (2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs +
        Lp ^ 2 * (2 * (1 + 5 * Jm)) * ((2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
          (Lp * Lp * (Jm * 5) * T.frzB C₀ Eb)))) := by
  have hCκ := localFormUniformConstant_nonneg κ'
  have hK0 : (0 : ℝ) ≤ T.K := Nat.cast_nonneg _
  have hP0 : (0 : ℝ) ≤ fp.P := Nat.cast_nonneg _
  have hFb : 0 ≤ T.frzB C₀ Eb := by unfold frzB; positivity
  have hBU0 : 0 ≤ BU := le_trans (Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun l _ =>
    sq_nonneg _) hBU
  have hBs0 : 0 ≤ Bs := le_trans (Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun G _ =>
    Finset.sum_nonneg fun l _ => sq_nonneg _) hBs
  set K' : ℝ := 2 * (1 + 5 * Jm) with hK'
  set D : ℝ := (2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 with hD
  set N4 : ℝ := Lp * Lp * (Jm * 5) * T.frzB C₀ Eb with hN4
  have hK'0 : 0 ≤ K' := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hN40 : 0 ≤ N4 := by positivity
  have hLp2 : (0 : ℝ) ≤ Lp ^ 2 := by positivity
  have hcd : ∀ l, ((Finset.range (T.pe l).length).card) ≤ Lp := fun l => by
    rw [Finset.card_range]; exact hLp l
  have hjd : ∀ c d i i', (Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length).card ≤ Jm :=
    fun c d i i' => by rw [Finset.card_range]; exact hJm c d i i'
  -- the shared part, one slot tuple
  set X : ℝ := Lp ^ 2 * K' * (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 * BU)) +
    D * N4) with hX
  have hX0 : 0 ≤ X := by positivity
  have hSh : ∀ a b c d, ∑ I ∈ S, dyadicGridLength A.G I.1 * T.thirdS C₀ a b c d G₀ I ^ 2 ≤ X := by
    intro a b c d
    unfold thirdS
    by_cases hV : T.Val a b c d ∧ ¬ T.Ucase c d
    · simp only [hV]
      have hcu : T.u ≠ some c := fun h => hV.2 (Or.inl h)
      have hdu : T.u ≠ some d := fun h => hV.2 (Or.inr h)
      have hcell : ∀ I ∈ S, dyadicGridLength A.G I.1 * T.thS C₀ a c d G₀ I ^ 2 ≤
          Lp ^ 2 * K' * (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 *
            (‖bf.Ucol fp.Mc c I‖ ^ 2 + ‖bf.Ucol fp.Mc d I‖ ^ 2))) + D *
            ∑ i' ∈ Finset.range (T.pe d).length, ∑ i ∈ Finset.range (T.pe c).length,
              ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
                ∑ _o ∈ Finset.range 5, T.frzShE C₀ a c d G₀ (T.tOf c i) (T.tOf d i') j I) :=
        fun I hI => T.thS_sq C₀ a c d G₀ I hLp (hJm c d) (hy I hI c hcu).1 (hy I hI d hdu).1
          (hy I hI d hdu).2
      refine (Finset.sum_le_sum hcell).trans ?_
      have hU : ∑ I ∈ S, (‖bf.Ucol fp.Mc c I‖ ^ 2 + ‖bf.Ucol fp.Mc d I‖ ^ 2) ≤ BU := by
        refine le_trans (Finset.sum_le_sum fun I _ => ?_) hBU
        rw [← Finset.sum_pair (f := fun l => ‖bf.Ucol fp.Mc l I‖ ^ 2)
          (fun h => hV.1.2.2.2.2.2.1 h)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => sq_nonneg _
      have hF : ∑ I ∈ S, ∑ i' ∈ Finset.range (T.pe d).length, ∑ i ∈ Finset.range (T.pe c).length,
          ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
            ∑ _o ∈ Finset.range 5, T.frzShE C₀ a c d G₀ (T.tOf c i) (T.tOf d i') j I ≤ N4 := by
        rw [sum_swap4]
        refine sum4_bound _ _ (fun i i' => Finset.range (T.desc c d (T.tOf c i)
          (T.tOf d i')).length) _ hFb (hcd d) (hcd c) (hjd c d) fun i' _ i _ j hj => ?_
        refine (T.shE_sum hC₀ a c d G₀ _ _ j S Sc hS hSc (by positivity) hEb
          (hEi a c d i i' j (Finset.mem_range.mp hj)) (hEp a c d i i' j (Finset.mem_range.mp hj))
          (hEF a c d i i' j (Finset.mem_range.mp hj))).trans (le_of_eq ?_)
        unfold frzB
        ring
      calc ∑ I ∈ S, Lp ^ 2 * K' * (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 *
            (‖bf.Ucol fp.Mc c I‖ ^ 2 + ‖bf.Ucol fp.Mc d I‖ ^ 2))) + D *
            ∑ i' ∈ Finset.range (T.pe d).length, ∑ i ∈ Finset.range (T.pe c).length,
              ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
                ∑ _o ∈ Finset.range 5, T.frzShE C₀ a c d G₀ (T.tOf c i) (T.tOf d i') j I)
          = Lp ^ 2 * K' * (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 *
            ∑ I ∈ S, (‖bf.Ucol fp.Mc c I‖ ^ 2 + ‖bf.Ucol fp.Mc d I‖ ^ 2))) + D *
            ∑ I ∈ S, ∑ i' ∈ Finset.range (T.pe d).length, ∑ i ∈ Finset.range (T.pe c).length,
              ∑ j ∈ Finset.range (T.desc c d (T.tOf c i) (T.tOf d i')).length,
                ∑ _o ∈ Finset.range 5, T.frzShE C₀ a c d G₀ (T.tOf c i) (T.tOf d i') j I) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ X := by
            rw [hX]
            gcongr
    · simp only [hV, ite_false, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, Finset.sum_const_zero]
      exact hX0
  -- the group part, one slot tuple
  set Y : ℝ := 2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs + Lp ^ 2 * K' * (D * N4) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hGr : ∀ a b c d, ∑ I ∈ S, ∑ G ∈ gs I,
      dyadicGridLength A.G I.1 * T.thirdG C₀ B₀ a b c d G I ^ 2 ≤ Y := by
    expose_names
    exact @C3v_budget_hGr κ' c₀ A bf fp T S hS gs gset hgs ScG hScG Lp Jm hLp hJm C₀ B₀ hC₀ Bs Eb
      hEb hBs hEpG hEFG hFb hBs0 hcd hjd hY hY0
  expose_names
  exact @C3v_budget_stage_1 κ' c₀ A bf fp T S gs G₀ Lp Jm C₀ B₀ Cy Bs BU Eb hX hSh hY hGr

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## The `2+2` patterns of a leaf (blueprint lines 2446-2456) -/

/-- `min(η, A + B) ≤ A + min(η, B)` for `A ≥ 0`. -/
theorem min_add_le_add_min {η a b : ℝ} (ha : 0 ≤ a) : min η (a + b) ≤ a + min η b := by
  rcases le_total η b with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]
    exact min_le_right _ _

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

theorem ns_mul_le_s2 {a b : Fin 4} (hab : a ≠ b) (G : bf.Grp) (I : ℤ × ℤ) :
    T.ns a G I * T.ns b G I ≤ T.s2 G I := by
  have ha := T.ns_nonneg a G I
  have hb := T.ns_nonneg b G I
  have h1 : T.ns a G I ^ 2 + T.ns b G I ^ 2 ≤ T.s2 G I := by
    unfold s2
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := Finset.univ)
      (f := fun l => T.ns l G I ^ 2) (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
    rw [Finset.sum_pair hab] at this
    exact this
  nlinarith [sq_nonneg (T.ns a G I - T.ns b G I)]

open Classical in
theorem absPart'_nonneg (C₀ τ cF : ℝ) (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (a b c d : Fin 4)
    (G : bf.Grp) (I : ℤ × ℤ) : 0 ≤ T.absPart' C₀ τ cF a b c d G I := by
  unfold absPart'
  split_ifs
  · rw [T.absPart_eq]
    have h1 := T.ns_nonneg a G I
    have h2 := T.ns_nonneg b G I
    have h3 : 0 ≤ T.nearAbs C₀ a b c d G I := by
      unfold nearAbs
      refine list_sum_map_nonneg _ _ fun t' _ => list_sum_map_nonneg _ _ fun t _ =>
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun o _ => ?_
      have : (0 : ℝ) ≤ 2 / fp.P := by positivity
      split_ifs <;> positivity
    positivity
  · exact le_rfl

open Classical in
/-- Blueprint lines 2375-2382 and 2446-2456 on one localization leaf, on the main columns: with the
pair-small restored complements, the far bound, current complement bounds `C₀`, whole outputs
bounded by `B₀`, the side path cap `T_s`, and a cell value `C₃` of the third strong factors
bounding the third factor of every group at the cell ("a third factor is shared or bounded by its
group square sum") with path cap `C_c`, the weighted active minimum of the restored `2+2` patterns
is at most the weighted absolute parts plus `η^{1-p} T_s^p C_c^{p/2} |R|`. -/
theorem two_two_leafM (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 ≤ C₀)
    (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → T.u ≠ some c → T.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤ cF * T.ns a G I * T.ns b G I)
    (hsc : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G I.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖T.out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Ts Cc : ℝ}
    (hTs : ∀ x, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2),
      ∑ G ∈ gs I, T.s2 G I ≤ Ts)
    (C3 : ℤ × ℤ → ℝ) (hC3 : ∀ I ∈ S, ∀ G ∈ gs I, 6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      ∑ d : Fin 4, T.third C₀ B₀ a b c d G I ≤ C3 I)
    (hCc : ∀ x, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2), C3 I ^ 2 ≤ Cc)
    {η p : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) :
    ∑ I ∈ S, dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
      (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
        (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
        (Finset.univ.filter fun l => σ l = 1).card = 2),
        ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      ∑ I ∈ S, dyadicGridLength A.G I.1 * (6 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        ∑ d : Fin 4, T.absPart' C₀ τ cF a b c d G I) +
      η ^ (1 - p) * (Ts ^ (p / 2) * Ts ^ (p / 2) * Cc ^ (p / 2) * dyadicGridLength A.G A.R.1) := by
  have hth0 : ∀ I G a b c d, 0 ≤ T.third C₀ B₀ a b c d G I := fun I G a b c d =>
    T.third_nonneg C₀ B₀ hC₀ hB₀ a b c d G I
  have hab0 : ∀ I G a b c d, 0 ≤ T.absPart' C₀ τ cF a b c d G I := fun I G a b c d =>
    T.absPart'_nonneg C₀ τ cF hτ hcF a b c d G I
  set! Ab : ℤ × ℤ → ℝ := fun I => 6 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    ∑ d : Fin 4, T.absPart' C₀ τ cF a b c d G I with hAb
  set! Bs : ℤ × ℤ → ℝ := fun I => ∑ G ∈ gs I, Real.sqrt (T.s2 G I) * Real.sqrt (T.s2 G I) *
    (6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, T.third C₀ B₀ a b c d G I) with hBs
  have hAb0 : ∀ I, 0 ≤ Ab I := fun I => mul_nonneg (by norm_num) (Finset.sum_nonneg fun G _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun d _ => hab0 I G a b c d)
  -- the cell bound
  have hcell : ∀ I ∈ S, ‖∑ σ ∈ Finset.univ.filter
      (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
        (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
        (Finset.univ.filter fun l => σ l = 1).card = 2),
        ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      Ab I + Bs I := by
    intro I hI
    refine (T.two_two_cellM I (gs I) (fun a b c d G => T.absPart' C₀ τ cF a b c d G I +
        T.s2 G I * T.third C₀ B₀ a b c d G I)
      (fun a b c d G => add_nonneg (hab0 I G a b c d) (mul_nonneg (T.s2_nonneg G I)
        (hth0 I G a b c d))) ?_).trans (le_of_eq ?_)
    · intro a b c d hV G hG
      refine (T.cell_bound2 hV G (hS hI) hτ (fun hU => hpair I hI c d hV.2.2.2.2.2.1
        (fun h => hU (Or.inl h)) (fun h => hU (Or.inr h))) (fun hU =>
          hfar I hI G hG a b c d hV hU) hC₀ hB₀ (hsc I hI) (hout I hI G hG)).trans ?_
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_right (T.ns_mul_le_s2 hV.1 G I)
        (hth0 I G a b c d))
    · simp only [hAb, hBs, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
      congr 1
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [Real.mul_self_sqrt (T.s2_nonneg G I)]
      simp only [← Finset.mul_sum]
      ring
  -- the group sum against the cell value of the third factors
  have hBsC : ∀ I ∈ S, Bs I ≤ Real.sqrt (∑ G ∈ gs I, T.s2 G I) *
      Real.sqrt (∑ G ∈ gs I, T.s2 G I) * C3 I := by
    intro I hI
    rw [Real.mul_self_sqrt (Finset.sum_nonneg fun G _ => T.s2_nonneg G I), Finset.sum_mul]
    refine Finset.sum_le_sum fun G hG => ?_
    rw [Real.mul_self_sqrt (T.s2_nonneg G I)]
    exact mul_le_mul_of_nonneg_left (hC3 I hI G hG) (T.s2_nonneg G I)
  have hmin := min_three_strong A.G S A.R hroot ({()} : Finset Unit) (fun _ => ({()} : Finset Unit))
    (fun _ I _ => Real.sqrt (∑ G ∈ gs I, T.s2 G I))
    (fun _ I _ => Real.sqrt (∑ G ∈ gs I, T.s2 G I)) (fun _ I _ => C3 I)
    (fun _ _ _ => Real.sqrt_nonneg _) (fun _ _ _ => Real.sqrt_nonneg _)
    (fun _ => Ts) (fun _ => Ts) (fun _ => Cc)
    (fun _ _ x => by
      simp_rw [Finset.sum_singleton, Real.sq_sqrt (Finset.sum_nonneg fun G _ => T.s2_nonneg G _)]
      exact hTs x)
    (fun _ _ x => by
      simp_rw [Finset.sum_singleton, Real.sq_sqrt (Finset.sum_nonneg fun G _ => T.s2_nonneg G _)]
      exact hTs x)
    (fun _ _ x => by simp_rw [Finset.sum_singleton]; exact hCc x) Bs
    (fun I hI => by simp_rw [Finset.sum_singleton]; exact hBsC I hI) hη hp hp1
  rw [Finset.sum_singleton] at hmin
  calc ∑ I ∈ S, dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
        (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
          (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
          (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖
      ≤ ∑ I ∈ S, dyadicGridLength A.G I.1 * (Ab I + min η (Bs I)) := by
        refine Finset.sum_le_sum fun I hI => mul_le_mul_of_nonneg_left ?_
          (dyadicGridLength_pos A.G I.1).le
        exact (min_le_min_left η (hcell I hI)).trans (min_add_le_add_min (hAb0 I))
    _ = ∑ I ∈ S, dyadicGridLength A.G I.1 * Ab I +
        ∑ I ∈ S, dyadicGridLength A.G I.1 * min η (Bs I) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun I _ => by ring
    _ ≤ _ := add_le_add le_rfl hmin

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## The two-side estimate of a leaf (blueprint lines 2425-2456) -/

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

open Classical in
/-- Blueprint line 2384 (pair-small main terms and far terms, absolute): the weighted absolute parts
of a leaf are at most `6 · 256 N_p (τ + c_F) T_s |R|` plus the weighted near parts, where `N_p`
bounds the numbers of pairs of positive chains and `T_s` is the side path cap. -/
theorem abs_sum_leM (S : Finset (ℤ × ℤ))
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) {C₀ τ cF Np Ts : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF)
    (hNp : ∀ c d, ((T.pe d).length * (T.pe c).length : ℝ) ≤ Np)
    (hTs : ∀ x, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2),
      ∑ G ∈ gs I, T.s2 G I ≤ Ts) :
    ∑ I ∈ S, dyadicGridLength A.G I.1 * (6 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        ∑ d : Fin 4, T.absPart' C₀ τ cF a b c d G I) ≤
      6 * 256 * Np * (τ + cF) * Ts * dyadicGridLength A.G A.R.1 +
      6 * ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4,
        ∑ c : Fin 4, ∑ d : Fin 4,
          (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0) := by
  have hNp0 : 0 ≤ Np := le_trans (by positivity) (hNp 0 0)
  have hpt : ∀ I G a b c d, T.absPart' C₀ τ cF a b c d G I ≤
      Np * ((τ + cF) * T.s2 G I) +
        (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0) := by
    intro I G a b c d
    unfold absPart'
    have h0 : 0 ≤ Np * ((τ + cF) * T.s2 G I) := by
      have := T.s2_nonneg G I
      positivity
    split_ifs with h
    · rw [T.absPart_eq]
      have hab := T.ns_mul_le_s2 h.1.1 G I
      have h1 := mul_le_mul (hNp c d) hab (mul_nonneg (T.ns_nonneg a G I) (T.ns_nonneg b G I))
        hNp0
      have h2 : ((T.pe d).length * (T.pe c).length : ℝ) * ((τ + cF) * T.ns a G I * T.ns b G I) =
          (τ + cF) * (((T.pe d).length * (T.pe c).length : ℝ) * (T.ns a G I * T.ns b G I)) := by
        ring
      have h3 : 0 ≤ τ + cF := by positivity
      nlinarith only [hτ, hcF, h1]
    · simpa using h0
  have hcell : ∀ I ∈ S, dyadicGridLength A.G I.1 * (6 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4,
      ∑ c : Fin 4, ∑ d : Fin 4, T.absPart' C₀ τ cF a b c d G I) ≤
      6 * 256 * Np * (τ + cF) * (dyadicGridLength A.G I.1 * ∑ G ∈ gs I, T.s2 G I) +
      6 * (dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0)) := by
    intro I _
    have hL := (dyadicGridLength_pos A.G I.1).le
    have hs : ∀ G, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        T.absPart' C₀ τ cF a b c d G I ≤
        256 * (Np * ((τ + cF) * T.s2 G I)) + ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0) := by
      intro G
      have e : (256 : ℝ) * (Np * ((τ + cF) * T.s2 G I)) = ∑ _a : Fin 4, ∑ _b : Fin 4,
          ∑ _c : Fin 4, ∑ _d : Fin 4, Np * ((τ + cF) * T.s2 G I) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [e]
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum
        fun c _ => Finset.sum_le_sum fun d _ => hpt I G a b c d
    have h := Finset.sum_le_sum fun G (_ : G ∈ gs I) => hs G
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have e2 : ∑ G ∈ gs I, Np * ((τ + cF) * T.s2 G I) = Np * (τ + cF) * ∑ G ∈ gs I, T.s2 G I := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun G _ => by ring
    rw [e2] at h
    nlinarith
  have hint := path_cap_integral A.G S A.R hroot (fun I => ∑ G ∈ gs I, T.s2 G I) hTs
  have hC : 0 ≤ 6 * 256 * Np * (τ + cF) := by positivity
  calc _ ≤ ∑ I ∈ S, (6 * 256 * Np * (τ + cF) * (dyadicGridLength A.G I.1 * ∑ G ∈ gs I, T.s2 G I) +
      6 * (dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0))) :=
        Finset.sum_le_sum hcell
    _ = 6 * 256 * Np * (τ + cF) * ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I, T.s2 G I +
      6 * ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then T.nearAbs C₀ a b c d G I else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hint hC
        linarith

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

open Classical in
/-- The side mass of a cell and group, weighted by its length, is the sum of the squared sides. -/
theorem len_s2 (G : bf.Grp) (I : ℤ × ℤ) :
    dyadicGridLength A.G I.1 * T.s2 G I = ∑ l, ‖T.sv l G I‖ ^ 2 := by
  unfold s2 ns
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hL := dyadicGridLength_pos A.G I.1
  rw [div_pow, Real.sq_sqrt hL.le]
  field_simp

open Classical in
/-- Blueprint lines 2425-2456, the two-side estimate of one localization leaf on the main columns:
one cut family of root fraction at most `2ρ` such that on the retained cells the weighted active
minimum of the restored `2+2` patterns is at most the pair-small and far absolute bound
`6·256 N_p (τ + c_F) T_c |R|`, six times the critical near-band bounds `nearBnd` of the slot
triples (`eq:near-band`), and the power cost `η^{1-p} T_c^{3p/2} |R|` of the three strong factors,
with the joint path cap `T_c = (B_s + B_3)/(ρ |R|)` of the side mass `B_s` and the integrated
budget `B_3` of a cell value `C₃` bounding the third strong factors of all groups at the cell. -/
theorem leaf_two_two_boundM {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : T.K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, T.bk I < Bn) (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (okZ : Fin 4 → bf.Grp → ℤ × ℤ → Prop) (BZ EW : Fin 4 → ℝ)
    (hcap : ∀ l, T.u ≠ some l → A.VarCap gset (T.Z l) (okZ l) (BZ l))
    (hok : ∀ l, T.u ≠ some l → ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → okZ l G J)
    (hEW : ∀ l, T.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ T.bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + ((T.K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (T.Wb l G (A.R.1 + ((T.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ EW l)
    {EU : ℝ} (hEU : ∀ l, T.u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) (T.sv l G I)‖ ^ 2 ≤ EU)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → T.u ≠ some c → T.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤ cF * T.ns a G I * T.ns b G I)
    (hsc : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G I.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖T.out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, ((T.pe d).length * (T.pe c).length : ℝ) ≤ Np)
    {Bs B3 : ℝ} (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    (C3 : ℤ × ℤ → ℝ) (hC3 : ∀ I ∈ S, ∀ G ∈ gs I, 6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      ∑ d : Fin 4, T.third C₀ B₀ a b c d G I ≤ C3 I)
    (hB3 : ∑ I ∈ S, dyadicGridLength A.G I.1 * C3 I ^ 2 ≤ B3)
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, T.u ≠ some a → fp.stackEA (nOs Lp Jm) (T.cat a) (T.mbs a) T.Dpre N (BZ a) (EW a) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, T.u ≠ some b → (nOs Lp Jm).card * (N * BZ b + EW b) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (nOs Lp Jm).card * EU ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      6 * 256 * Np * (τ + cF) * ((Bs / dyadicGridLength A.G A.R.1 +
          B3 / dyadicGridLength A.G A.R.1) / ρ) * dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          T.nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (((Bs / dyadicGridLength A.G A.R.1 + B3 / dyadicGridLength A.G A.R.1) / ρ) ^
          (p / 2) * ((Bs / dyadicGridLength A.G A.R.1 + B3 / dyadicGridLength A.G A.R.1) / ρ) ^
          (p / 2) * ((Bs / dyadicGridLength A.G A.R.1 + B3 / dyadicGridLength A.G A.R.1) / ρ) ^
          (p / 2) * dyadicGridLength A.G A.R.1) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, T.s2 G I ≤
        (Bs / dyadicGridLength A.G A.R.1 + B3 / dyadicGridLength A.G A.R.1) / ρ := by
  classical
  have hR0 := dyadicGridLength_pos A.G A.R.1
  -- the joint cut of the two strong families
  set! fam : Fin 2 → ℤ × ℤ → ℝ := fun v I => if v = 0 then ∑ G ∈ gs I, T.s2 G I else
    C3 I ^ 2 with hfam
  have hfam0 : ∀ v, ∀ I ∈ S, 0 ≤ fam v I := by
    intro v I _
    simp only [hfam]
    split_ifs
    · exact Finset.sum_nonneg fun G _ => T.s2_nonneg G I
    · exact sq_nonneg _
  obtain ⟨C1, hC1S, hC1len, hcapc⟩ := caps_cut A.G S A.R hroot fam hfam0
    (fun v => if v = 0 then Bs / dyadicGridLength A.G A.R.1 else
      B3 / dyadicGridLength A.G A.R.1) (fun v => by
      fin_cases v
      · simp only [hfam, Fin.zero_eta, Fin.isValue, ↓reduceIte]
        rw [div_mul_cancel₀ _ hR0.ne']
        calc ∑ I ∈ S, dyadicGridLength A.G I.1 * ∑ G ∈ gs I, T.s2 G I
            = ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 := by
              refine Finset.sum_congr rfl fun I _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun G _ => T.len_s2 G I
          _ ≤ Bs := hBs
      · simp only [hfam, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [div_mul_cancel₀ _ hR0.ne']
        exact hB3) hρ hρ1
  obtain ⟨Cn, hCnc, hCnlen, hnear⟩ := T.near_sumM hq2 hq3 hanc hKNd hKN S hS gs gset hgs Lp Jm
    Bn k hBn hLp hJm Act hact hMp okZ BZ EW hcap hok hEW hEU hC₀ hρ hρ1 hP Γa Γb ΓU hΓa hΓb hΓU
  set Tc := (Bs / dyadicGridLength A.G A.R.1 + B3 / dyadicGridLength A.G A.R.1) / ρ with hTc
  have hcap' : ∀ v x, ∑ I ∈ (S.filter fun I => ¬ ∃ c ∈ C1,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2).filter
      (fun I => x ∈ dyadicGridCell A.G I.1 I.2), fam v I ≤ Tc := by
    intro v x
    refine (hcapc v x).trans (le_of_eq ?_)
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, hTc]
  set Cm := maximalDyadicCells A.G Cn
  refine ⟨C1 ∪ Cm, ?_, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hS (hC1S h)
    · exact hCnc (maximalDyadicCells_subset A.G Cn h)
  · refine (maximalDyadicCells_length_le A.G _).trans ?_
    unfold dyadicRootLength at hC1len hCnlen ⊢
    have h := Finset.sum_union_inter (s₁ := C1) (s₂ := Cm)
      (f := fun c : ℤ × ℤ => dyadicGridLength A.G c.1)
    have h0 : 0 ≤ ∑ c ∈ C1 ∩ Cm, dyadicGridLength A.G c.1 :=
      Finset.sum_nonneg fun c _ => (dyadicGridLength_pos A.G c.1).le
    linarith only [hC1len, hCnlen, h, h0]
  set S' := S.filter (fun I => ¬ ∃ e ∈ C1 ∪ Cm,
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) with hS'
  have hS'1 : ∀ I ∈ S', I ∈ S := fun I hI => (Finset.mem_filter.mp hI).1
  have hS'C1 : ∀ I ∈ S', ¬ ∃ e ∈ C1, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2 :=
    fun I hI ⟨e, he, hsub⟩ => (Finset.mem_filter.mp hI).2 ⟨e, Finset.mem_union_left _ he, hsub⟩
  have hS'Cn : ∀ I ∈ S', ¬ ∃ e ∈ Cn, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2 := by
    intro I hI ⟨e, he, hsub⟩
    obtain ⟨d, hd, hsub'⟩ := maximalDyadicCells_covers A.G Cn he
    exact (Finset.mem_filter.mp hI).2 ⟨d, Finset.mem_union_right _ hd, hsub.trans hsub'⟩
  have hsubcap : ∀ v x, ∑ I ∈ S'.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2), fam v I ≤ Tc :=
      by
    intro v x
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun I hI => ?_)
      fun I hI _ => hfam0 v I (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1) (hcap' v x)
    obtain ⟨hI1, hx⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hS'1 I hI1, hS'C1 I hI1⟩, hx⟩
  have hTs : ∀ x, ∑ I ∈ S'.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2),
      ∑ G ∈ gs I, T.s2 G I ≤ Tc := fun x => by simpa [hfam] using hsubcap 0 x
  have hCc : ∀ x, ∑ I ∈ S'.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2), C3 I ^ 2 ≤ Tc :=
    fun x => by simpa [hfam] using hsubcap 1 x
  have hS'c : S' ⊆ A.cells := fun I hI => hS (hS'1 I hI)
  have hroot' : ∀ I ∈ S', dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 :=
    fun I hI => hroot I (hS'1 I hI)
  have hmain := T.two_two_leafM S' hS'c hroot' gs hτ hcF hC₀ hB₀
    (fun I hI => hpair I (hS'1 I hI)) (fun I hI => hfar I (hS'1 I hI))
    (fun I hI => hsc I (hS'1 I hI)) (fun I hI => hout I (hS'1 I hI)) hTs C3
    (fun I hI => hC3 I (hS'1 I hI)) hCc hη hp hp1
  have habs := T.abs_sum_leM S' hroot' gs (C₀ := C₀) hτ hcF hNp hTs
  have hnp0 : ∀ I G a b c d, 0 ≤ (if T.Val a b c d ∧ ¬ T.Ucase c d then
      T.nearAbs C₀ a b c d G I else 0) := by
    intro I G a b c d
    split_ifs
    · unfold nearAbs
      refine list_sum_map_nonneg _ _ fun t' _ => list_sum_map_nonneg _ _ fun t _ =>
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun o _ => ?_
      have : (0 : ℝ) ≤ 2 / fp.P := by positivity
      split_ifs <;> positivity
    · exact le_rfl
  have hnear' : ∑ I ∈ S', dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4,
      ∑ c : Fin 4, ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then
        T.nearAbs C₀ a b c d G I else 0) ≤
      ∑ I ∈ S.filter (fun I => ¬ ∃ e' ∈ Cn,
        dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e'.1 e'.2),
        dyadicGridLength A.G I.1 * ∑ G ∈ gs I, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          ∑ d : Fin 4, (if T.Val a b c d ∧ ¬ T.Ucase c d then
            T.nearAbs C₀ a b c d G I else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun I hI => Finset.mem_filter.mpr
      ⟨hS'1 I hI, hS'Cn I hI⟩) fun I _ _ => mul_nonneg (dyadicGridLength_pos A.G I.1).le
        (Finset.sum_nonneg fun G _ => Finset.sum_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => Finset.sum_nonneg
            fun d _ => hnp0 I G a b c d)
  refine ⟨?_, hTs⟩
  refine hmain.trans ?_
  have := habs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hnear'.trans hnear)
    (by norm_num : (0 : ℝ) ≤ 6)))
  linarith only [hnear, habs, hnear']

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- The freeze energy of a shared output over certified ancestors from its variation capacity. -/
theorem frz_shared {Z : bf.Grp → ℤ → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)} (G₀ : bf.Grp) {B : ℝ}
    (hcap : A.VarCap {G₀} Z (fun _ _ => True) B) (Sc : Finset (ℤ × ℤ)) (hSc : Sc ⊆ A.cells) :
    ∑ J ∈ Sc, ‖columnL2Restriction (dyadicGridCell A.G J.1 J.2)
      (dyadicGridCell_measurable A.G J.1 J.2) (Z G₀ J.1 - Z G₀ (A.blkStart T.K J.1))‖ ^ 2 ≤
      T.K * B := by
  have h := T.frz_varcap {G₀} Z (fun _ _ => True) hcap (fun _ => Sc)
    (fun g _ J hJ => ⟨hSc hJ, trivial⟩)
  rwa [Finset.sum_singleton] at h

open Classical in
/-- Blueprint lines 2386-2394 (third strong factors with shared histories counted once), from
variation capacities: if the identity outputs, the pads of cumulative steps and the other
complements with cumulative histories have variation capacity `B_v` as shared outputs, and the
pads of ball steps and the other complements with a ball have joint variation capacity `B_v` over
the groups (with the certificates `ok` on the ancestors of their uses), then the cell values `C₃`
of the third strong factors have the integrated bound of `C3v_budget` with `E_b = K B_v`. -/
theorem C3v_budget_cap (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (G₀ : bf.Grp) (Sc : Finset (ℤ × ℤ))
    (hScc : Sc ⊆ A.cells)
    (hSc : ∀ I ∈ S, ∀ J ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 →
      A.blkStart T.K I.1 ≤ J.1 → J ∈ Sc)
    (ScG : bf.Grp → Finset (ℤ × ℤ)) (ok : bf.Grp → ℤ × ℤ → Prop)
    (hScGc : ∀ G ∈ gset, ∀ J ∈ ScG G, J ∈ A.cells ∧ ok G J)
    (hScG : ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → A.blkStart T.K I.1 ≤ J.1 →
        J ∈ ScG G)
    {Lp Jm : ℕ} (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    {C₀ B₀ Cy : ℝ} (hC₀ : 0 < C₀)
    (hy : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {Bs BU Bv : ℝ} (hBv : 0 ≤ Bv)
    (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (hVi : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      A.VarCap {G₀}
        (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (fp.P + 1) h) (fun _ _ => True) Bv)
    (hVp : ∀ a c d i i' j n, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      n < fp.P → T.cumY c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap {G₀} (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) h)
        (fun _ _ => True) Bv)
    (hVF : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      T.cumF c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap {G₀} (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
        (T.Lf.role d) (T.desc c d (T.tOf c i) (T.tOf d i')) j h) (fun _ _ => True) Bv)
    (hVpG : ∀ a c d i i' j n, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      n < fp.P → ¬ T.cumY c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap gset (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) h) ok Bv)
    (hVFG : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      ¬ T.cumF c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap gset (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
        (T.Lf.role d) (T.desc c d (T.tOf c i) (T.tOf d i')) j h) ok Bv) :
    ∑ I ∈ S, dyadicGridLength A.G I.1 * T.C3v C₀ B₀ G₀ gs I ^ 2 ≤
      2 * (36 * 256 * 256 * (Lp ^ 2 * (2 * (1 + 5 * Jm)) *
        (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 * BU)) +
          (2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
            (Lp * Lp * (Jm * 5) * T.frzB C₀ (T.K * Bv))))) +
      2 * (36 * 256 * 256 * (2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs +
        Lp ^ 2 * (2 * (1 + 5 * Jm)) * ((2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
          (Lp * Lp * (Jm * 5) * T.frzB C₀ (T.K * Bv))))) := by
  have hK0 : (0 : ℝ) ≤ T.K := Nat.cast_nonneg _
  have hP0 : (0 : ℝ) ≤ fp.P := Nat.cast_nonneg _
  refine T.C3v_budget S hS gs gset hgs G₀ Sc hSc ScG hScG hLp hJm hC₀ hy
    (by positivity : (0 : ℝ) ≤ T.K * Bv) hBs hBU ?_ ?_ ?_ ?_ ?_
  · intro a c d i i' j hj
    exact T.frz_shared G₀ (hVi a c d i i' j hj) Sc hScc
  · intro a c d i i' j hj hY
    unfold pYe
    rw [Finset.sum_comm]
    calc ∑ n ∈ Finset.range fp.P, ∑ J ∈ Sc, T.dXo a c d G₀ (T.tOf c i) (T.tOf d i') j (n + 1) J
        ≤ ∑ _n ∈ Finset.range fp.P, T.K * Bv := Finset.sum_le_sum fun n hn =>
          T.frz_shared G₀ (hVp a c d i i' j n hj (Finset.mem_range.mp hn) hY) Sc hScc
      _ = fp.P * (T.K * Bv) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro a c d i i' j hj hF
    exact T.frz_shared G₀ (hVF a c d i i' j hj hF) Sc hScc
  · intro a c d i i' j hj hY
    unfold pYe
    calc ∑ G ∈ gset, ∑ J ∈ ScG G, ∑ n ∈ Finset.range fp.P,
          T.dXo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) J
        = ∑ n ∈ Finset.range fp.P, ∑ G ∈ gset, ∑ J ∈ ScG G,
          T.dXo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) J :=
          sum_comm_out gset ScG (Finset.range fp.P) _
      _ ≤ ∑ _n ∈ Finset.range fp.P, T.K * Bv := Finset.sum_le_sum fun n hn =>
          T.frz_varcap gset _ ok (hVpG a c d i i' j n hj (Finset.mem_range.mp hn) hY) ScG hScGc
      _ = fp.P * (T.K * Bv) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro a c d i i' j hj hF
    exact T.frz_varcap gset _ ok (hVFG a c d i i' j hj hF) ScG hScGc

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- The integrated budget of the third strong factors of `C3v_budget_cap`. -/
noncomputable def B3cap (Lp Jm : ℕ) (C₀ B₀ Cy Bs BU Bv : ℝ) : ℝ :=
  2 * (36 * 256 * 256 * (Lp ^ 2 * (2 * (1 + 5 * Jm)) *
    (Lp ^ 2 * (localFormUniformConstant κ' ^ 2 * (8 * Cy ^ 2 * BU)) +
      (2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
        (Lp * Lp * (Jm * 5) * T.frzB C₀ (T.K * Bv))))) +
  2 * (36 * 256 * 256 * (2 * (localFormUniformConstant κ' * B₀) ^ 2 * Bs +
    Lp ^ 2 * (2 * (1 + 5 * Jm)) * ((2 / (fp.P : ℝ) * localFormUniformConstant κ') ^ 2 * 6 *
      (Lp * Lp * (Jm * 5) * T.frzB C₀ (T.K * Bv)))))

open Classical in
/-- Blueprint lines 2375-2456, the two-side estimate of one localization leaf on the main columns
with the third strong factors in integrated form: one cut family of root fraction at most `2ρ`
such that on the retained cells the weighted active minimum of the restored `2+2` patterns is at
most the pair-small and far absolute bound, six times the critical near-band bounds
(`eq:near-band`), and the power cost of the three strong factors with the joint path cap
`T_c = (B_s + B_3)/(ρ |R|)`, where `B_3 = B3cap` collects the `U` energy (counted once per cell),
the side masses and the freeze budgets of the shared and of the group-indexed frozen complements
(blueprint line 2263: "a shared history will not be counted once for every group"). -/
theorem leaf_two_two_capM {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : T.K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, T.bk I < Bn) (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (okZ : Fin 4 → bf.Grp → ℤ × ℤ → Prop) (BZ EW : Fin 4 → ℝ)
    (hcap : ∀ l, T.u ≠ some l → A.VarCap gset (T.Z l) (okZ l) (BZ l))
    (hok : ∀ l, T.u ≠ some l → ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → okZ l G J)
    (hEW : ∀ l, T.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ T.bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + ((T.K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (T.Wb l G (A.R.1 + ((T.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ EW l)
    {EU : ℝ} (hEU : ∀ l, T.u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) (T.sv l G I)‖ ^ 2 ≤ EU)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 < C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → T.u ≠ some c → T.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤ cF * T.ns a G I * T.ns b G I)
    (hbas : ∀ J ∈ A.cells, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l J‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G J.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖T.out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, ((T.pe d).length * (T.pe c).length : ℝ) ≤ Np)
    {Bs : ℝ} (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    -- the third strong factors
    (G₀ : bf.Grp) (Sc : Finset (ℤ × ℤ)) (hScc : Sc ⊆ A.cells)
    (hSc : ∀ I ∈ S, ∀ J ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 →
      A.blkStart T.K I.1 ≤ J.1 → J ∈ Sc)
    (ScG : bf.Grp → Finset (ℤ × ℤ)) (ok : bf.Grp → ℤ × ℤ → Prop)
    (hScGc : ∀ G ∈ gset, ∀ J ∈ ScG G, J ∈ A.cells ∧ ok G J)
    (hScG : ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → A.blkStart T.K I.1 ≤ J.1 →
        J ∈ ScG G)
    {Cy : ℝ} (hy : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {BU Bv : ℝ} (hBv : 0 ≤ Bv) (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (hVi : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      A.VarCap {G₀}
        (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (fp.P + 1) h) (fun _ _ => True) Bv)
    (hVp : ∀ a c d i i' j n, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      n < fp.P → T.cumY c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap {G₀} (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) h)
        (fun _ _ => True) Bv)
    (hVF : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      T.cumF c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap {G₀} (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
        (T.Lf.role d) (T.desc c d (T.tOf c i) (T.tOf d i')) j h) (fun _ _ => True) Bv)
    (hVpG : ∀ a c d i i' j n, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      n < fp.P → ¬ T.cumY c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap gset (fun G h => T.Xo a c d G (T.tOf c i) (T.tOf d i') j (n + 1) h) ok Bv)
    (hVFG : ∀ a c d i i' j, j < (T.desc c d (T.tOf c i) (T.tOf d i')).length →
      ¬ T.cumF c d (T.tOf c i) (T.tOf d i') j →
      A.VarCap gset (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
        (T.Lf.role d) (T.desc c d (T.tOf c i) (T.tOf d i')) j h) ok Bv)
    -- numerics of the near bands
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, T.u ≠ some a → fp.stackEA (nOs Lp Jm) (T.cat a) (T.mbs a) T.Dpre N (BZ a) (EW a) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, T.u ≠ some b → (nOs Lp Jm).card * (N * BZ b + EW b) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (nOs Lp Jm).card * EU ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      6 * 256 * Np * (τ + cF) * ((Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) / ρ) *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          T.nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (((Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) / ρ) ^ (p / 2) *
          ((Bs / dyadicGridLength A.G A.R.1 +
            T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) / ρ) ^ (p / 2) *
          ((Bs / dyadicGridLength A.G A.R.1 +
            T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) / ρ) ^ (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, T.s2 G I ≤
        (Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) / ρ :=
  T.leaf_two_two_boundM hq2 hq3 hanc hKNd hKN S hS hroot gs gset hgs Lp Jm Bn k hBn hLp hJm Act
    hact hMp okZ BZ EW hcap hok hEW hEU hτ hcF hC₀.le hB₀ hpair hfar
    (fun I hI l hl => hbas I (hS hI) l hl) hout hNp hBs (T.C3v C₀ B₀ G₀ gs)
    (fun I _ _ hG => T.third_le_C3v hC₀.le B₀ G₀ gs I hbas hG)
    (T.C3v_budget_cap S hS gs gset hgs G₀ Sc hScc hSc ScG ok hScGc hScG hLp hJm hC₀ hy hBv hBs
      hBU hVi hVp hVF hVpG hVFG) hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## Global complement histories as main-base histories (blueprint lines 2263, 2386-2390) -/

section ConjLayer
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

/-- Averages commute with conjugation. -/
theorem opAvg_conj {P : ℕ} (R : E →L[ℂ] F) (S : F →L[ℂ] E) (Q : Fin P → E →L[ℂ] E) :
    opAvg (fun p => R.comp ((Q p).comp S)) = R.comp ((opAvg Q).comp S) := by
  ext x
  simp only [opAvg, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul]

/-- A left inverse of the conjugation intertwines the layered histories of the conjugated layers
with those of the layers. -/
theorem layerOp_conj_left (R : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hSR : ∀ y, S (R y) = y) (Cum : ℕ → E →L[ℂ] E) (ls : List (ℕ × Bool)) (y : F) :
    S (layerOp (fun m => R.comp ((Cum m).comp S)) ls y) = layerOp Cum ls (S y) := by
  induction ls using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [layerOp_append, layerOp_append]
    by_cases hx : x.2 = true
    · simp only [hx, ite_true, ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply, map_sub, hSR, ih]
    · simp only [hx, Bool.false_eq_true, ite_false, ContinuousLinearMap.comp_apply, hSR, ih]

/-- A nonempty layered history of conjugated averaged layers (without complements) is the
conjugated layered history. -/
theorem layerOp_conj (R : E →L[ℂ] F) (S : F →L[ℂ] E) (hSR : ∀ y, S (R y) = y)
    (Cum : ℕ → E →L[ℂ] E) (ls : List (ℕ × Bool)) (hne : ls ≠ [])
    (hfalse : ∀ x ∈ ls, x.2 = false) (y : F) :
    layerOp (fun m => R.comp ((Cum m).comp S)) ls y = R (layerOp Cum ls (S y)) := by
  obtain ⟨l, x, rfl⟩ : ∃ l x, ls = l ++ [x] :=
    ⟨ls.dropLast, ls.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hx : x.2 = false := hfalse x (List.mem_append_right _ (List.mem_singleton_self x))
  rw [layerOp_append, layerOp_append]
  simp only [hx, Bool.false_eq_true, ite_false, ContinuousLinearMap.comp_apply]
  rw [layerOp_conj_left R S hSR Cum l y]

/-- Reindexing the layers of a layered history. -/
theorem layerOp_map (Cum : ℕ → E →L[ℂ] E) (f : ℕ → ℕ) (ls : List (ℕ × Bool)) :
    layerOp Cum (ls.map fun x => (f x.1, x.2)) = layerOp (fun m => Cum (f m)) ls := by
  induction ls using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.map_append, List.map_singleton, layerOp_append, layerOp_append, ih]

end ConjLayer

/-- The layer indices (innermost first) of the descriptors of slot `v` of a list of descriptors
starting at the position `k`. -/
def restIdxM (v : Bool) : List (Bool × ℕ × Option ℕ) → ℕ → List (ℕ × Bool)
  | [], _ => []
  | e :: es, k => restIdxM v es (k + 1) ++ (if e.1 = v then [(k, false)] else [])

theorem restIdxM_false (v : Bool) :
    ∀ (es : List (Bool × ℕ × Option ℕ)) (k : ℕ), ∀ x ∈ restIdxM v es k, x.2 = false
  | [], _, x, hx => by simp [restIdxM] at hx
  | e :: es, k, x, hx => by
    rw [restIdxM, List.mem_append] at hx
    rcases hx with hx | hx
    · exact restIdxM_false v es (k + 1) x hx
    · split_ifs at hx
      · rw [List.mem_singleton] at hx; rw [hx]
      · simp at hx

/-- The layer indices of slot `v` point to descriptors of slot `v` in the list. -/
theorem restIdxM_mem (v : Bool) (D : List (Bool × ℕ × Option ℕ)) :
    ∀ (es : List (Bool × ℕ × Option ℕ)) (k : ℕ),
      (∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none)) →
      ∀ x ∈ restIdxM v es k, D.getD x.1 (true, 0, none) ∈ es ∧
        (D.getD x.1 (true, 0, none)).1 = v
  | [], _, _, x, hx => by simp [restIdxM] at hx
  | e :: es, k, hes, x, hx => by
    have hes' : ∀ i (hi : i < es.length), es[i] = D.getD (k + 1 + i) (true, 0, none) := by
      intro i hi
      have := hes (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega
    have he : e = D.getD k (true, 0, none) := by
      have := hes 0 (by simp)
      simpa using this
    rw [restIdxM, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := restIdxM_mem v D es (k + 1) hes' x hx
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · split_ifs at hx with hv
      · rw [List.mem_singleton] at hx
        rw [hx, ← he]
        exact ⟨List.mem_cons_self, hv⟩
      · simp at hx

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The inherited complement masks of the descriptors of slot `v` (`true` for `c`, `false` for
`d`) on its main tree, indexed by the position of the descriptor. -/
noncomputable def cmpMaskM (cat : Fin 4 → List (CatCol bf.Vtx))
    (mbs : ∀ l, bf.MainBudget (cat l)) (c d : Fin 4) (G : bf.Grp) (jc jd : ℕ) (v : Bool)
    (D : List (Bool × ℕ × Option ℕ)) (m : ℕ) (p : Fin fp.P) :
    InheritedColumnMask (bf.mainTree fp.Mc (cat (if v then c else d)) (mbs _)) :=
  bf.mainMaskT (if v then c else d) fp.Mc (cat _) (mbs _) (D.getD m (true, 0, none)).2.1
    (fun c' => fp.stepMaskM G (if v then jc else jd) (D.getD m (true, 0, none)).2.2 p c')
    (fp.stepMaskM_mono G _ _ p)

/-- The complement value of slot `v` after global steps is the layered history of the conjugated
global projections with the complement masks of its descriptors. -/
theorem chainVal_globM (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (a c d : Fin 4) (rH : ℕ) (G : bf.Grp) (jc jd : ℕ) (v : Bool)
    (D : List (Bool × ℕ × Option ℕ)) (h : ℤ) (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ∀ (es : List (Bool × ℕ × Option ℕ)) (k : ℕ),
      (∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none)) →
      chainVal fp.P v ((es.map fun e => fp.gStepM cat mbs a c d rH G jc jd e h).map padStep) x =
        layerOp (fun m => opAvg fun p => fp.gProjC (cat (if v then c else d)) (mbs _)
          (fp.cmpMaskM cat mbs c d G jc jd v D m p) h) (restIdxM v es k) x
  | [], k, _ => by simp only [List.map_nil, chainVal, restIdxM]; rfl
  | e :: es, k, hes => by
    have hes' : ∀ i (hi : i < es.length), es[i] = D.getD (k + 1 + i) (true, 0, none) := by
      intro i hi
      have := hes (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega
    have he : e = D.getD k (true, 0, none) := by
      have := hes 0 (by simp)
      simpa using this
    have ih := chainVal_globM cat mbs a c d rH G jc jd v D h x es (k + 1) hes'
    rw [List.map_cons, List.map_cons, chainVal_cons, fp.gStepM_fst, ih, restIdxM]
    by_cases hv : e.1 = v
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hv), ite_eq_left_of_eq_true _ _ (eq_true hv),
        layerOp_append]
      simp only [Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply]
      rw [padStep, filterAvg_padFam]
      subst he
      subst hv
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hv), ite_eq_right_of_eq_false _ _
        (eq_false hv), List.append_nil]

end ActiveSetup.BasicFamilies.FamParams

/-- Complement values over concatenated step lists compose. -/
theorem chainVal_append {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (P : ℕ)
    (v : Bool) (L₁ L₂ : List (TransferStep E)) (y : E) :
    chainVal P v (L₁ ++ L₂) y = chainVal P v L₁ (chainVal P v L₂ y) := by
  induction L₁ with
  | nil => rfl
  | cons st L₁ ih => rw [List.cons_append, chainVal_cons, chainVal_cons, ih]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The descriptors of the merge of the slot descriptors are the ball descriptor or cumulative
descriptors of their slot. -/
theorem mergeDescM_slot (jc jd : ℕ) (t t' : List ℕ) {e : Bool × ℕ × Option ℕ}
    (he : e ∈ fp.mergeDescM jc jd t t') :
    e.2 = (fp.brank (if e.1 then jc else jd), none) ∨ ∃ m, e.2 = (fp.crank m, some m) := by
  cases hv : e.1 with
  | true =>
    have h := rankMerge_filter_true Prod.fst (fp.slotDescM jc t) (fp.slotDescM jd t')
    have hm : e.2 ∈ fp.slotDescM jc t := by
      rw [← h]
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, hv⟩, rfl⟩
    unfold slotDescM at hm
    rcases List.mem_cons.mp hm with h1 | h1
    · left; rw [h1]; rfl
    · right
      obtain ⟨m, -, hm⟩ := List.mem_map.mp h1
      exact ⟨m, hm.symm⟩
  | false =>
    have h := rankMerge_filter_false Prod.fst (fp.slotDescM jc t) (fp.slotDescM jd t')
    have hm : e.2 ∈ fp.slotDescM jd t' := by
      rw [← h]
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hv]⟩, rfl⟩
    unfold slotDescM at hm
    rcases List.mem_cons.mp hm with h1 | h1
    · left; rw [h1]; rfl
    · right
      obtain ⟨m, -, hm⟩ := List.mem_map.mp h1
      exact ⟨m, hm.symm⟩

/-- Blueprint line 2263: a descriptor of a slot that comes after another descriptor of the same
slot is cumulative. -/
theorem mergeDescM_later (jc jd : ℕ) (t t' : List ℕ) {i : ℕ}
    (hi : i < (fp.mergeDescM jc jd t t').length) {e : Bool × ℕ × Option ℕ}
    (he : e ∈ (fp.mergeDescM jc jd t t').drop (i + 1))
    (hev : e.1 = ((fp.mergeDescM jc jd t t').getD i (true, 0, none)).1) :
    ∃ m, e.2 = (fp.crank m, some m) := by
  rw [List.getD_eq_getElem _ _ hi] at hev
  set L := fp.mergeDescM jc jd t t' with hLd
  cases hv : L[i].1 with
  | true =>
    have hL : (L.filter fun e => e.1 = true).map Prod.snd =
        (fp.brank jc, none) :: t.map fun m => (fp.crank m, some m) := by
      have := rankMerge_filter_true Prod.fst (fp.slotDescM jc t) (fp.slotDescM jd t')
      simp only [Bool.decide_eq_true] at this ⊢
      exact this
    have hm := slot_after_mem L true _ _ hL hi hv he (hev.trans hv)
    obtain ⟨m, -, hm⟩ := List.mem_map.mp hm
    exact ⟨m, hm.symm⟩
  | false =>
    have hL : (L.filter fun e => e.1 = false).map Prod.snd =
        (fp.brank jd, none) :: t'.map fun m => (fp.crank m, some m) := by
      have := rankMerge_filter_false Prod.fst (fp.slotDescM jc t) (fp.slotDescM jd t')
      have e2 : (fun e : Bool × ℕ × Option ℕ => decide (e.1 = false)) = fun e => !e.1 := by
        funext e; cases e.1 <;> rfl
      rw [e2]
      exact this
    have hm := slot_after_mem L false _ _ hL hi hv he (hev.trans hv)
    obtain ⟨m, -, hm⟩ := List.mem_map.mp hm
    exact ⟨m, hm.symm⟩

/-- The cumulative layer indices of a list of layer positions in the descriptors `D`. -/
def lsCum (D : List (Bool × ℕ × Option ℕ)) (ls : List (ℕ × Bool)) : List (ℕ × Bool) :=
  ls.map fun y => (((D.getD y.1 (true, 0, none)).2.2).getD 0, y.2)

theorem lsCum_length (D : List (Bool × ℕ × Option ℕ)) (ls : List (ℕ × Bool)) :
    (lsCum D ls).length = ls.length := by
  simp [lsCum]

/-- The complement mask of a cumulative descriptor is the cumulative mask of its split. -/
theorem cmpMaskM_cum (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (c d : Fin 4) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (p : Fin fp.P) {m : ℕ} (hm : (D.getD k (true, 0, none)).2 = (fp.crank m, some m)) :
    fp.cmpMaskM cat mbs c d G jc jd w D k p = fp.cumMaskT (if w then c else d) (cat _) (mbs _) m p
        := by
  have h1 : (D.getD k (true, 0, none)).2.1 = fp.crank m := by rw [hm]
  have h2 : (D.getD k (true, 0, none)).2.2 = some m := by rw [hm]
  unfold cmpMaskM cumMaskT
  congr 1
  all_goals funext c'; rw [h2]; rfl

/-- The layers of slot `v` with cumulative descriptors are the averaged cumulative projections of
the main tree of its slot. -/
theorem globHist_cmp_cum (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (c d : Fin 4) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ))
    (es : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (hes : ∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none))
    (hcum : ∀ e ∈ es, e.1 = w → ∃ m, e.2 = (fp.crank m, some m)) (h : ℤ) :
    layerOp (fun m => opAvg fun p =>
        ((bf.mainBase fp.Mc (cat (if w then c else d)) (mbs _)).withMask
          (fp.cmpMaskM cat mbs c d G jc jd w D m p)).proj h) (restIdxM w es k) =
      fp.gHist (if w then c else d) (cat _) (mbs _) (lsCum D (restIdxM w es k)) h := by
  unfold gHist globHist lsCum
  rw [layerOp_map _ (fun k => ((D.getD k (true, 0, none)).2.2).getD 0)]
  refine layerOp_congr _ fun y hy => ?_
  obtain ⟨hmem, hw⟩ := restIdxM_mem w D es k hes y hy
  obtain ⟨m, hm⟩ := hcum _ hmem hw
  have hm2 : (D.getD y.1 (true, 0, none)).2.2.getD 0 = m := by rw [hm]; rfl
  rw [hm2]
  congr 1
  funext p
  rw [fp.cmpMaskM_cum cat mbs c d G jc jd w D y.1 p hm]

/-- Blueprint line 2263 ("its complementary band history is shared across groups"): the
relabeling adjoint of a complement value of slot `w` after global steps whose descriptors of that
slot are cumulative is the shared main-base history of the relabeled input. -/
theorem cum_hist_left (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (a c d : Fin 4) (rH : ℕ) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ))
    (es : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (hes : ∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none))
    (hcum : ∀ e ∈ es, e.1 = w → ∃ m, e.2 = (fp.crank m, some m)) (h : ℤ)
    (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d))))
        (chainVal fp.P w ((es.map fun e => fp.gStepM cat mbs a c d rH G jc jd e h).map padStep)
          x) =
      fp.gHist (if w then c else d) (cat _) (mbs _) (lsCum D (restIdxM w es k)) h
        (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))) x) := by
  rw [fp.chainVal_globM cat mbs a c d rH G jc jd w D h x es k hes]
  have hlay : (fun m => opAvg fun p => fp.gProjC (cat (if w then c else d)) (mbs _)
      (fp.cmpMaskM cat mbs c d G jc jd w D m p) h) = fun m =>
      (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))).comp ((opAvg fun p =>
        ((bf.mainBase fp.Mc (cat (if w then c else d)) (mbs _)).withMask
          (fp.cmpMaskM cat mbs c d G jc jd w D m p)).proj h).comp
        (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))))) :=
    funext fun m => opAvg_conj _ _ _
  rw [hlay, layerOp_conj_left _ _ (colRelabel_adjoint_apply_relabel (bf.rv_injective _ _)),
    fp.globHist_cmp_cum cat mbs c d G jc jd w D es k hes hcum h]

/-- A complement value of slot `w` after global steps whose descriptors of that slot are
cumulative, at least one of them: the relabeled shared main-base history. -/
theorem cum_hist_full (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (a c d : Fin 4) (rH : ℕ) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ))
    (es : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (hes : ∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none))
    (hcum : ∀ e ∈ es, e.1 = w → ∃ m, e.2 = (fp.crank m, some m)) (hne : restIdxM w es k ≠ [])
    (h : ℤ) (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    chainVal fp.P w ((es.map fun e => fp.gStepM cat mbs a c d rH G jc jd e h).map padStep) x =
      colRelabel (bf.rv fp.Mc (cat (if w then c else d)))
        (fp.gHist (if w then c else d) (cat _) (mbs _) (lsCum D (restIdxM w es k)) h
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d))))
            x)) := by
  rw [fp.chainVal_globM cat mbs a c d rH G jc jd w D h x es k hes]
  have hlay : (fun m => opAvg fun p => fp.gProjC (cat (if w then c else d)) (mbs _)
      (fp.cmpMaskM cat mbs c d G jc jd w D m p) h) = fun m =>
      (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))).comp ((opAvg fun p =>
        ((bf.mainBase fp.Mc (cat (if w then c else d)) (mbs _)).withMask
          (fp.cmpMaskM cat mbs c d G jc jd w D m p)).proj h).comp
        (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))))) :=
    funext fun m => opAvg_conj _ _ _
  rw [hlay, layerOp_conj _ _ (colRelabel_adjoint_apply_relabel (bf.rv_injective _ _)) _ _ hne
    (restIdxM_false w es k), fp.globHist_cmp_cum cat mbs c d G jc jd w D es k hes hcum h]

/-- A complement value of slot `w` after global steps without descriptors of that slot is the
input. -/
theorem cum_hist_empty (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (a c d : Fin 4) (rH : ℕ) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ))
    (es : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (hes : ∀ i (hi : i < es.length), es[i] = D.getD (k + i) (true, 0, none))
    (hemp : restIdxM w es k = []) (h : ℤ) (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    chainVal fp.P w ((es.map fun e => fp.gStepM cat mbs a c d rH G jc jd e h).map padStep) x =
      x := by
  rw [fp.chainVal_globM cat mbs a c d rH G jc jd w D h x es k hes, hemp, layerOp_nil]
  rfl

end ActiveSetup.BasicFamilies.FamParams

/-- The entries of a dropped list are the entries of the list at the shifted positions. -/
theorem drop_getD_eq {α : Type*} (D : List α) (k : ℕ) (d : α) :
    ∀ i (hi : i < (D.drop k).length), (D.drop k)[i] = D.getD (k + i) d := by
  intro i hi
  rw [List.getElem_drop, List.getD_eq_getElem _ _ (by simp at hi; omega)]

/-- Complement values skip steps of the other slot. -/
theorem chainVal_skip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (P : ℕ)
    (v : Bool) (L : List (TransferStep E)) (hL : ∀ st ∈ L, st.1 ≠ v) (y : E) :
    chainVal P v L y = y := by
  induction L with
  | nil => rfl
  | cons st L ih =>
    rw [chainVal_cons, ite_eq_right_of_eq_false _ _ (eq_false (hL st List.mem_cons_self)),
      ih fun s hs => hL s (List.mem_cons_of_mem _ hs)]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The basic input of the slot of a step. -/
theorem gBasic_ite (v : Bool) (c d : Fin 4) (h : ℤ) :
    (if v then bf.gBasic fp.Mc c h else bf.gBasic fp.Mc d h) =
      bf.gBasic fp.Mc (if v then c else d) h := by
  cases v <;> rfl

/-- The later descriptors of the slot of a step of merged descriptors are cumulative. -/
theorem merge_after_cum (jc jd : ℕ) (t t' : List ℕ) (j : ℕ) :
    ∀ e ∈ (fp.mergeDescM jc jd t t').drop (j + 1),
      e.1 = ((fp.mergeDescM jc jd t t').getD j (true, 0, none)).1 →
        ∃ m, e.2 = (fp.crank m, some m) := by
  intro e he hev
  by_cases hj : j < (fp.mergeDescM jc jd t t').length
  · exact fp.mergeDescM_later jc jd t t' hj he hev
  · rw [List.drop_eq_nil_of_le (by omega)] at he
    simp at he

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- The later descriptors of the slot of a step of a chain pair are cumulative. -/
theorem desc_after_cum (c d : Fin 4) (t t' : List ℕ) (j : ℕ) :
    ∀ e ∈ (T.desc c d t t').drop (j + 1),
      e.1 = ((T.desc c d t t').getD j (true, 0, none)).1 → ∃ m, e.2 = (fp.crank m, some m) :=
  fp.merge_after_cum (T.Lf.role c) (T.Lf.role d) t t' j

/-- Blueprint lines 1871 and 2386 ("couple individual pad choices across times"): the pad output
`n + 1` of a step is the single-pad main output of its complement mask after the shared history
of the later descriptors of its slot. -/
theorem Xo_pad (a c d : Fin 4) (G : bf.Grp) (t t' : List ℕ) (j n : ℕ) (hn : n < fp.P) (h : ℤ) :
    T.Xo a c d G t t' j (n + 1) h =
      fp.basicOutM (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d) (T.cat _)
        (T.mbs _) (fp.cmpMaskM T.cat T.mbs c d G (T.Lf.role c) (T.Lf.role d)
          ((T.desc c d t t').getD j (true, 0, none)).1 (T.desc c d t t') j ⟨n, hn⟩)
        (lsCum (T.desc c d t t') (restIdxM ((T.desc c d t t').getD j (true, 0, none)).1
          ((T.desc c d t t').drop (j + 1)) (j + 1))) h := by
  unfold Xo
  simp only [fp.gStM_fst, gBasic_ite]
  have hpad : ∀ y, (fp.gStM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
      (T.desc c d t t') j h).2.2 (n + 1) y =
      fp.gProjC (T.cat (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d)) (T.mbs _)
        (fp.cmpMaskM T.cat T.mbs c d G (T.Lf.role c) (T.Lf.role d)
          ((T.desc c d t t').getD j (true, 0, none)).1 (T.desc c d t t') j ⟨n, hn⟩) h y := by
    intro y
    unfold gStM padStep
    dsimp only
    rw [padFam_succ _ hn]
    rfl
  rw [hpad]
  unfold gProjC gRestM basicOutM gOutM
  simp only [ContinuousLinearMap.comp_apply]
  congr 2
  rw [fp.cum_hist_left T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
    ((T.desc c d t t').getD j (true, 0, none)).1 (T.desc c d t t') ((T.desc c d t t').drop (j + 1))
    (j + 1) (drop_getD_eq _ _ _) (T.desc_after_cum c d t t' j) h]

/-- The identity output of a step: the shared history of the later descriptors of its slot applied
to the basic input, or the basic input itself without later descriptors of its slot. -/
theorem Xo_top (a c d : Fin 4) (G : bf.Grp) (t t' : List ℕ) (j : ℕ) (h : ℤ) :
    T.Xo a c d G t t' j (fp.P + 1) h =
      if restIdxM ((T.desc c d t t').getD j (true, 0, none)).1 ((T.desc c d t t').drop (j + 1))
          (j + 1) = [] then
        bf.gBasic fp.Mc (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d) h
      else fp.histOut (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d)
        (T.cat (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
        (T.mbs (if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
        (lsCum (T.desc c d t t') (restIdxM ((T.desc c d t t').getD j (true, 0, none)).1
          ((T.desc c d t t').drop (j + 1)) (j + 1))) h := by
  unfold Xo
  rw [fp.gStM_top]
  simp only [fp.gStM_fst, gBasic_ite]
  unfold gRestM
  by_cases hemp : restIdxM ((T.desc c d t t').getD j (true, 0, none)).1
    ((T.desc c d t t').drop (j + 1)) (j + 1) = []
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hemp)]
    exact fp.cum_hist_empty T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
      ((T.desc c d t t').getD j (true, 0, none)).1 (T.desc c d t t')
      ((T.desc c d t t').drop (j + 1)) (j + 1) (drop_getD_eq _ _ _) hemp h _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hemp)]
    rw [fp.cum_hist_full T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
      ((T.desc c d t t').getD j (true, 0, none)).1 (T.desc c d t t')
      ((T.desc c d t t').drop (j + 1)) (j + 1) (drop_getD_eq _ _ _)
      (T.desc_after_cum c d t t' j) hemp h]
    rfl

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

theorem restIdxM_length_le (v : Bool) :
    ∀ (es : List (Bool × ℕ × Option ℕ)) (k : ℕ), (restIdxM v es k).length ≤ es.length
  | [], _ => by simp [restIdxM]
  | e :: es, k => by
    rw [restIdxM, List.length_append, List.length_cons]
    have := restIdxM_length_le v es (k + 1)
    split_ifs <;> simp <;> omega

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The basic input of the other slot of a step. -/
theorem gBasic_ite_not (v : Bool) (c d : Fin 4) (h : ℤ) :
    (if v then bf.gBasic fp.Mc d h else bf.gBasic fp.Mc c h) =
      bf.gBasic fp.Mc (if !v then c else d) h := by
  cases v <;> rfl

/-- The complement mask of a ball descriptor is the ball mask of its slot. -/
theorem cmpMaskM_ball (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (c d : Fin 4) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ)) (k : ℕ)
    (p : Fin fp.P) (hm : (D.getD k (true, 0, none)).2 = (fp.brank (if w then jc else jd), none)) :
    fp.cmpMaskM cat mbs c d G jc jd w D k p =
      fp.ballMaskT (if w then c else d) (cat _) (mbs _) G (if w then jc else jd) p := by
  have h1 : (D.getD k (true, 0, none)).2.1 = fp.brank (if w then jc else jd) := by rw [hm]
  have h2 : (D.getD k (true, 0, none)).2.2 = none := by rw [hm]
  unfold cmpMaskM ballMaskT
  congr 1
  all_goals funext c'; rw [h2]; rfl

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- Blueprint line 2263 ("the other complement ... is shared"): with a cumulative later history,
the other complement of a step is the shared history of its slot applied to its basic input, or
the basic input itself without later descriptors of its slot. -/
theorem F_cum (a c d : Fin 4) (G : bf.Grp) (t t' : List ℕ) (j : ℕ) (hF : T.cumF c d t t' j)
    (h : ℤ) :
    fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d) (T.desc c d t t') j h =
      if restIdxM (!((T.desc c d t t').getD j (true, 0, none)).1) ((T.desc c d t t').drop (j + 1))
          (j + 1) = [] then
        bf.gBasic fp.Mc (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d) h
      else fp.histOut (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d)
        (T.cat (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
        (T.mbs (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
        (lsCum (T.desc c d t t') (restIdxM (!((T.desc c d t t').getD j (true, 0, none)).1)
          ((T.desc c d t t').drop (j + 1)) (j + 1))) h := by
  have hcum : ∀ e ∈ (T.desc c d t t').drop (j + 1),
      e.1 = !((T.desc c d t t').getD j (true, 0, none)).1 → ∃ m, e.2 = (fp.crank m, some m) := by
    intro e he hev
    rcases fp.mergeDescM_slot (T.Lf.role c) (T.Lf.role d) t t' (List.mem_of_mem_drop he) with
      h1 | h1
    · exact absurd (by rw [h1]) (hF e he hev)
    · exact h1
  unfold FfrM
  simp only [fp.gStM_fst, gBasic_ite_not]
  unfold gRestM
  by_cases hemp : restIdxM (!((T.desc c d t t').getD j (true, 0, none)).1)
    ((T.desc c d t t').drop (j + 1)) (j + 1) = []
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hemp)]
    exact fp.cum_hist_empty T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
      (!((T.desc c d t t').getD j (true, 0, none)).1) (T.desc c d t t')
      ((T.desc c d t t').drop (j + 1)) (j + 1) (drop_getD_eq _ _ _) hemp h _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hemp)]
    rw [fp.cum_hist_full T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d)
      (!((T.desc c d t t').getD j (true, 0, none)).1) (T.desc c d t t')
      ((T.desc c d t t').drop (j + 1)) (j + 1) (drop_getD_eq _ _ _) hcum hemp h]
    rfl

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-- The average of finitely many operators applied to a vector. -/
theorem opAvg_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {P : ℕ}
    (Q : Fin P → E →L[ℂ] E) (y : E) : opAvg Q y = ((P : ℂ)⁻¹) • ∑ p, Q p y := by
  rw [opAvg, smul_apply, FunLike.coe_sum, Finset.sum_apply]

/-- A padded step of the slot of a complement value applies its pad average. -/
theorem chainVal_cons_pad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (P : ℕ)
    (v : Bool) (st : Bool × (Fin P → E →L[ℂ] E) × (Fin P → E →L[ℂ] E))
    (rest : List (TransferStep E)) (y : E) (h : st.1 = v) :
    chainVal P v (padStep st :: rest) y = opAvg st.2.2 (chainVal P v rest y) := by
  rw [chainVal_cons]
  exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans (filterAvg_padFam _ _)

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- Blueprint line 2263 ("the other complement ... has a positive ball outermost"): a complement
value of slot `w` after global steps whose first descriptor of that slot is its ball descriptor
and whose later descriptors of that slot are cumulative is the pad average of the relabeled
single ball-pad outputs after the shared history. -/
theorem ball_avg_eq (cat : Fin 4 → List (CatCol bf.Vtx)) (mbs : ∀ l, bf.MainBudget (cat l))
    (a c d : Fin 4) (rH : ℕ) (G : bf.Grp) (jc jd : ℕ) (w : Bool) (D : List (Bool × ℕ × Option ℕ))
    (pre post : List (Bool × ℕ × Option ℕ)) (k₀ : ℕ) (hpre : ∀ e ∈ pre, e.1 ≠ w)
    (hpost : ∀ i (hi : i < post.length), post[i] = D.getD (k₀ + 1 + i) (true, 0, none))
    (hcum : ∀ e ∈ post, e.1 = w → ∃ m, e.2 = (fp.crank m, some m)) (h : ℤ)
    (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    chainVal fp.P w (((pre ++ (w, fp.brank (if w then jc else jd), none) :: post).map
        fun e => fp.gStepM cat mbs a c d rH G jc jd e h).map padStep) x =
      ((fp.P : ℂ)⁻¹) • ∑ p : Fin fp.P, colRelabel (bf.rv fp.Mc (cat (if w then c else d)))
        (fp.gOutM (if w then c else d) (cat _) (mbs _)
          (fp.ballMaskT (if w then c else d) (cat _) (mbs _) G (if w then jc else jd) p)
          (lsCum D (restIdxM w post (k₀ + 1))) h
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc (cat (if w then c else d)))) x))
              := by
  rw [List.map_append, List.map_append, chainVal_append]
  rw [chainVal_skip _ _ _ (fun st hst => by
    obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hst'
    exact (fp.gStepM_fst cat mbs a c d rH G jc jd e h).trans_ne (hpre e he))]
  have hfst : (fp.gStepM cat mbs a c d rH G jc jd
      (w, fp.brank (if w then jc else jd), none) h).1 = w := rfl
  simp only [List.map_cons]
  rw [chainVal_cons_pad _ _ _ _ _ hfst, opAvg_apply]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hl := fp.cum_hist_left cat mbs a c d rH G jc jd w D post (k₀ + 1) hpost hcum h x
  unfold gOutM
  rw [ContinuousLinearMap.comp_apply, ← hl]
  rfl

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- Blueprint line 2263 ("the other complement similarly ... has a positive ball outermost"): if
the later history of the other complement of a step contains its ball descriptor, the other
complement is the pad average of the single ball-pad main outputs of its slot after a shared
history, for one list of layers serving all groups and depths. -/
theorem F_ball (a c d : Fin 4) (t t' : List ℕ) (j : ℕ) (hF : ¬ T.cumF c d t t' j) :
    ∃ ls : List (ℕ × Bool), ls.length ≤ (T.desc c d t t').length ∧ ∀ (G : bf.Grp) (h : ℤ),
      fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d) (T.desc c d t t') j h =
        ((fp.P : ℂ)⁻¹) • ∑ p : Fin fp.P,
          fp.basicOutM (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d)
            (T.cat (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
            (T.mbs (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
            (fp.ballMaskT (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d)
              (T.cat (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d))
              (T.mbs (if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d)) G
              (if !((T.desc c d t t').getD j (true, 0, none)).1 then T.Lf.role c else T.Lf.role d)
              p) ls h := by
  set D := T.desc c d t t' with hD
  set w := !(D.getD j (true, 0, none)).1 with hw
  set! es := D.drop (j + 1) with hes
  have hex : ∃ e ∈ es, e.1 = w ∧ e.2.2 = none := by
    unfold cumF at hF
    push Not at hF
    exact hF
  obtain ⟨eb, hebm, hebw, hebn⟩ := hex
  set! pre := es.takeWhile (fun e => !decide (e.1 = w)) with hpre_d
  set! rest := es.dropWhile (fun e => !decide (e.1 = w)) with hrest_d
  have hsplit : pre ++ rest = es := List.takeWhile_append_dropWhile
  have hpre : ∀ e ∈ pre, e.1 ≠ w := fun e he => by
    have := List.mem_takeWhile_imp he
    simpa using this
  have hrest_ne : rest ≠ [] := by
    intro h0
    rw [h0, List.append_nil] at hsplit
    exact hpre eb (hsplit ▸ hebm) hebw
  obtain ⟨e₀, post, hrest⟩ := List.exists_cons_of_ne_nil hrest_ne
  have he₀w : e₀.1 = w := by
    have := List.head_dropWhile_not (fun e : Bool × ℕ × Option ℕ => !decide (e.1 = w)) hrest_ne
    simpa [← hrest_d, hrest] using this
  have hes_eq : es = pre ++ e₀ :: post := by rw [← hsplit, hrest]
  -- positions in the descriptors
  set! k₀ := j + 1 + pre.length with hk₀
  have hlenes : es.length = pre.length + 1 + post.length := by rw [hes_eq]; simp; omega
  have hesD : es.length = D.length - (j + 1) := List.length_drop
  have hlen : k₀ < D.length := by omega
  have hD₀ : D.getD k₀ (true, 0, none) = e₀ := by
    have h1 : es[pre.length]'(by omega) = e₀ := by
      simp only [hes_eq, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
    rw [← h1, drop_getD_eq D (j + 1) _ pre.length]
  have hpost_eq : D.drop (k₀ + 1) = post := by
    rw [show k₀ + 1 = (j + 1) + (pre.length + 1) by omega, ← List.drop_drop, ← hes, hes_eq,
      ← List.drop_drop, List.drop_left]
    rfl
  have hpostD : ∀ i (hi : i < post.length), post[i] = D.getD (k₀ + 1 + i) (true, 0, none) := by
    intro i hi
    rw [← drop_getD_eq D (k₀ + 1) _ i (by rw [hpost_eq]; exact hi)]
    exact List.getElem_of_eq hpost_eq.symm hi
  have hpost_drop : ∀ e ∈ post, e ∈ D.drop (k₀ + 1) := fun e he => hpost_eq ▸ he
  have hk₀v : (D.getD k₀ (true, 0, none)).1 = w := by rw [hD₀, he₀w]
  -- the later descriptors of the slot are cumulative
  have hcum : ∀ e ∈ post, e.1 = w → ∃ m, e.2 = (fp.crank m, some m) := fun e he hew =>
    fp.mergeDescM_later (T.Lf.role c) (T.Lf.role d) t t' hlen (hpost_drop e he)
      (hew.trans hk₀v.symm)
  -- the first descriptor of the slot is its ball descriptor
  have he₀ : e₀ = (w, fp.brank (if w then T.Lf.role c else T.Lf.role d), none) := by
    have hmem : e₀ ∈ D := by
      rw [← hD₀, List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem _
    rcases fp.mergeDescM_slot (T.Lf.role c) (T.Lf.role d) t t' hmem with h1 | ⟨m, hm⟩
    · rw [he₀w] at h1
      exact Prod.ext he₀w h1
    · exfalso
      have hb : eb ∈ e₀ :: post := by
        have : eb ∈ pre ++ e₀ :: post := hes_eq ▸ hebm
        rcases List.mem_append.mp this with h2 | h2
        · exact absurd hebw (hpre eb h2)
        · exact h2
      rcases List.mem_cons.mp hb with h2 | h2
      · rw [h2, hm] at hebn
        simp at hebn
      · obtain ⟨m', hm'⟩ := hcum eb h2 hebw
        rw [hm'] at hebn
        simp at hebn
  refine ⟨lsCum D (restIdxM w post (k₀ + 1)), ?_, fun G h => ?_⟩
  · rw [lsCum_length]
    refine (restIdxM_length_le w post _).trans ?_
    omega
  · unfold FfrM
    simp only [fp.gStM_fst, gBasic_ite_not]
    unfold gRestM
    rw [← hes, hes_eq, he₀]
    rw [fp.ball_avg_eq T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c) (T.Lf.role d) w D pre post
      k₀ hpre hpostD hcum h]
    rfl

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## Variation capacities of the frozen outputs (blueprint lines 1861-1877, 2386-2390) -/

/-- The square of an average is at most the average of the squares. -/
theorem norm_avg_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {P : ℕ} (hP : 0 < P)
    (v : Fin P → E) : ‖((P : ℂ)⁻¹) • ∑ p, v p‖ ^ 2 ≤ (P : ℝ)⁻¹ * ∑ p, ‖v p‖ ^ 2 := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [norm_smul, norm_inv, Complex.norm_natCast, mul_pow]
  have h1 : ‖∑ p, v p‖ ^ 2 ≤ P * ∑ p, ‖v p‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin P))) (f := fun p => ‖v p‖)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans h
  calc (P : ℝ)⁻¹ ^ 2 * ‖∑ p, v p‖ ^ 2 ≤ (P : ℝ)⁻¹ ^ 2 * (P * ∑ p, ‖v p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (P : ℝ)⁻¹ * ∑ p, ‖v p‖ ^ 2 := by field_simp

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The common variation capacity `G₀ · 4 |R|` of the single outputs (`basic_variationM_le`). -/
noncomputable def capV (A : ActiveSetup κ' c₀) (c : ℕ) (kk : ℝ) : ℝ :=
  Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2) * (4 * dyadicGridLength A.G A.R.1)

theorem four_le_capV (c : ℕ) (kk : ℝ) (hk : 1 ≤ kk) :
    4 * dyadicGridLength A.G A.R.1 ≤ capV A c kk := by
  unfold capV
  have hR := (dyadicGridLength_pos A.G A.R.1).le
  have h1 : 1 ≤ Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
      (1 + Real.log (2 * kk)) ^ 2) := Real.one_le_exp (by
    have : 0 ≤ Real.log (2 * kk) := Real.log_nonneg (by linarith)
    positivity)
  nlinarith

/-- Blueprint line 1877 for a basic input without later history: the restricted jumps of the
global basic input over disjoint depth intervals have total square at most `4 |R|`. -/
theorem gBasic_variation (hne : A.cells.Nonempty) (l : Fin 4) {ι : Type*} [Fintype ι]
    (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (Ec : ι → Finset (ℤ × ℤ)) (hEc : ∀ i, ∀ I ∈ Ec i, I ∈ A.cells) :
    ∑ i, ‖columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (bf.gBasic fp.Mc l (A.R.1 + t i) - bf.gBasic fp.Mc l (A.R.1 + r i))‖ ^ 2 ≤
      4 * dyadicGridLength A.G A.R.1 := by
  set! rE : ι → ColumnL2 (bf.Lab ⊕ Fin fp.Mc) →L[ℂ] ColumnL2 (bf.Lab ⊕ Fin fp.Mc) := fun i =>
    columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2) with hrE
  -- one basic family
  have hfam : ∀ jb : Fin 2, ∑ i, ‖rE i (bf.famEmb fp.Mc l jb
      ((bf.P l jb).Ψ.proj (A.R.1 + t i) (bf.P l jb).Z -
        (bf.P l jb).Ψ.proj (A.R.1 + r i) (bf.P l jb).Z))‖ ^ 2 ≤ dyadicGridLength A.G A.R.1 := by
    intro jb
    set Ψ := (bf.P l jb).Ψ
    have hΨG : Ψ.D.grid = A.G := (bf.P l jb).grid
    have hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2 :=
      (bf.P l jb).root_sub
    have hΨr : Ψ.D.root.1 ≤ A.R.1 := dyadicGridCell_depth_le_of_subset A.G A.R Ψ.D.root hΨR
    have hN := famN_ge (bf := bf) hne l jb
    set! rR := columnL2Restriction (V := (bf.P l jb).V) (dyadicGridCell A.G A.R.1 A.R.2)
      (dyadicGridCell_measurable A.G A.R.1 A.R.2)
    -- the basic projections commute with the restriction to the root
    have hcomm : ∀ h, A.R.1 ≤ h → Ψ.proj h (rR (bf.P l jb).Z) = rR (Ψ.proj h (bf.P l jb).Z) := by
      intro h hRh
      have hd : A.R.1 ≤ Ψ.depth h := by
        unfold ColumnDepthFamily.depth
        exact le_trans (le_min hRh hN) (le_max_right _ _)
      have h' := Ψ.proj_commute_restrict h (Q := A.R) hd
      rw [hΨG] at h'
      exact (DFunLike.congr_fun h' (bf.P l jb).Z).symm
    have hsub : ∀ i y, rE i (bf.famEmb fp.Mc l jb y) =
        rE i (bf.famEmb fp.Mc l jb (rR y)) := by
      intro i y
      have e : bf.famEmb fp.Mc l jb (rR y) = columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
          (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.famEmb fp.Mc l jb y) :=
        colRelabel_restrict _ _ _ y
      have hER : (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2) ⊆ dyadicGridCell A.G A.R.1 A.R.2 := by
        intro y hy
        obtain ⟨I, hI, hyI⟩ := Set.mem_iUnion₂.mp hy
        exact A.sub I (hEc i I hI) hyI
      rw [e]
      exact (DFunLike.congr_fun (columnL2Restriction_comp_of_subset _ _ hER) _).symm
    calc ∑ i, ‖rE i (bf.famEmb fp.Mc l jb ((bf.P l jb).Ψ.proj (A.R.1 + t i) (bf.P l jb).Z -
          (bf.P l jb).Ψ.proj (A.R.1 + r i) (bf.P l jb).Z))‖ ^ 2
        = ∑ i, ‖rE i (bf.famEmb fp.Mc l jb ((Ψ.proj (A.R.1 + t i) - Ψ.proj (A.R.1 + r i))
            (rR (bf.P l jb).Z)))‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsub, sub_apply, hcomm _ (by omega), hcomm _ (by omega), map_sub]
      _ ≤ ∑ i, ‖(Ψ.proj (A.R.1 + t i) - Ψ.proj (A.R.1 + r i)) (rR (bf.P l jb).Z)‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (columnL2Indicator_norm_le _ (Finset.measurableSet_biUnion _ fun I _ =>
            dyadicGridCell_measurable A.G I.1 I.2) _).trans ?_
          exact (norm_colRelabel (bf.famEmb_injective fp.Mc l jb) _).le
      _ ≤ ‖rR (bf.P l jb).Z‖ ^ 2 := Ψ.jumps_from_le hΨr r t hrt hdis _
      _ ≤ dyadicGridLength A.G A.R.1 := famInput_energy (bf := bf) l jb
  have hpt : ∀ i, ‖rE i (bf.gBasic fp.Mc l (A.R.1 + t i) - bf.gBasic fp.Mc l (A.R.1 + r i))‖ ^ 2 ≤
      2 * ‖rE i (bf.famEmb fp.Mc l 0 ((bf.P l 0).Ψ.proj (A.R.1 + t i) (bf.P l 0).Z -
        (bf.P l 0).Ψ.proj (A.R.1 + r i) (bf.P l 0).Z))‖ ^ 2 +
      2 * ‖rE i (bf.famEmb fp.Mc l 1 ((bf.P l 1).Ψ.proj (A.R.1 + t i) (bf.P l 1).Z -
        (bf.P l 1).Ψ.proj (A.R.1 + r i) (bf.P l 1).Z))‖ ^ 2 := by
    intro i
    have e : rE i (bf.gBasic fp.Mc l (A.R.1 + t i) - bf.gBasic fp.Mc l (A.R.1 + r i)) =
        rE i (bf.famEmb fp.Mc l 0 ((bf.P l 0).Ψ.proj (A.R.1 + t i) (bf.P l 0).Z -
          (bf.P l 0).Ψ.proj (A.R.1 + r i) (bf.P l 0).Z)) -
        rE i (bf.famEmb fp.Mc l 1 ((bf.P l 1).Ψ.proj (A.R.1 + t i) (bf.P l 1).Z -
          (bf.P l 1).Ψ.proj (A.R.1 + r i) (bf.P l 1).Z)) := by
      unfold ActiveSetup.BasicFamilies.gBasic
      simp only [map_sub]
      abel
    rw [e]
    exact norm_sub_sq_le_two_mul _ _
  calc _ ≤ ∑ i, (2 * ‖rE i (bf.famEmb fp.Mc l 0 ((bf.P l 0).Ψ.proj (A.R.1 + t i) (bf.P l 0).Z -
        (bf.P l 0).Ψ.proj (A.R.1 + r i) (bf.P l 0).Z))‖ ^ 2 +
      2 * ‖rE i (bf.famEmb fp.Mc l 1 ((bf.P l 1).Ψ.proj (A.R.1 + t i) (bf.P l 1).Z -
        (bf.P l 1).Ψ.proj (A.R.1 + r i) (bf.P l 1).Z))‖ ^ 2) := Finset.sum_le_sum fun i _ => hpt i
    _ = 2 * ∑ i, ‖rE i (bf.famEmb fp.Mc l 0 ((bf.P l 0).Ψ.proj (A.R.1 + t i) (bf.P l 0).Z -
        (bf.P l 0).Ψ.proj (A.R.1 + r i) (bf.P l 0).Z))‖ ^ 2 +
      2 * ∑ i, ‖rE i (bf.famEmb fp.Mc l 1 ((bf.P l 1).Ψ.proj (A.R.1 + t i) (bf.P l 1).Z -
        (bf.P l 1).Ψ.proj (A.R.1 + r i) (bf.P l 1).Z))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * dyadicGridLength A.G A.R.1 := by
        have h0 := hfam 0
        have h1 := hfam 1
        linarith

/-- Blueprint line 1868 ("the same assertion holds for a shared history, omitting `G`"): the
shared history outputs have variation capacity `G₀ · 4 |R|`. -/
theorem histOut_variation_le (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) {ι : Type*} [Fintype ι] (ls : List (ℕ × Bool)) (r t : ι → ℕ)
    (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (htd : ∀ i, t i ≤ A.treeDepth) (Ec : ι → Finset (ℤ × ℤ))
    (hEc : ∀ i, ∀ I ∈ Ec i, I ∈ A.cells) (c : ℕ) (hc : 1 ≤ c) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ c) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ c)
    (hn : (ls.length : ℝ) ≤ c * (Real.log kk + 1)) :
    ∑ i, ‖columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.histOut l s mb ls (A.R.1 + t i) - fp.histOut l s mb ls (A.R.1 + r i))‖ ^ 2 ≤
      capV A c kk := by
  refine (fp.basic_history_variation l s mb hne ls r t hrt hdis htd Ec hEc).trans ?_
  refine le_trans ?_ (fp.basic_variationM_le l s mb ls (Cw := 1) (by norm_num) c hc hk hDm hDb hn)
  refine Finset.sum_le_sum fun jb _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hS : 0 ≤ ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC := sq_nonneg (compressionC (bf.mainTree fp.Mc s mb) ls.length)
  have hC1 := sq_nonneg (compressionC (bf.P l jb).Ψ.D 1)
  have hL : (0 : ℝ) ≤ ls.length := Nat.cast_nonneg _
  have h1 : (ls.length : ℝ) * ∑ m ∈ Finset.range ls.length,
      compressionC (bf.mainTree fp.Mc s mb) m ^ 2 ≤ 2 * 1 *
      (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 + ls.length *
        ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2) := by
    have := mul_nonneg hL hS
    nlinarith only [hS]
  have h2 := mul_le_mul_of_nonneg_right h1 hC1
  nlinarith only [h1]

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup
variable {κ' : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ' c₀)

/-- Variation capacities only depend on the outputs of the groups considered. -/
theorem varCap_congr {γ V : Type*} [Fintype V] {Gs : Finset γ} {Z Z' : γ → ℤ → ColumnL2 V}
    {ok : γ → ℤ × ℤ → Prop} {B : ℝ} (hZ : ∀ g ∈ Gs, ∀ h, Z g h = Z' g h)
    (hcap : A.VarCap Gs Z ok B) : A.VarCap Gs Z' ok B := by
  intro ι _ r t hrt hdis htd Ec hEc
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun i _ => ?_))
    (hcap r t hrt hdis htd Ec hEc)
  rw [hZ g hg, hZ g hg]

/-- Blueprint lines 1883 and 2398 ("couple pad choices across times and restore their averages by
Jensen"): pad averages of outputs with a common variation capacity have that capacity. -/
theorem varCap_avg {γ V : Type*} [Fintype V] {P : ℕ} (hP : 0 < P) {Gs : Finset γ}
    {Z : Fin P → γ → ℤ → ColumnL2 V} {ok : γ → ℤ × ℤ → Prop} {B : ℝ}
    (hcap : ∀ p, A.VarCap Gs (Z p) ok B) :
    A.VarCap Gs (fun g h => ((P : ℂ)⁻¹) • ∑ p, Z p g h) ok B := by
  intro ι _ r t hrt hdis htd Ec hEc
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  set! rE : γ → ι → ColumnL2 V →L[ℂ] ColumnL2 V := fun g i =>
    columnL2Restriction (⋃ J ∈ Ec g i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
  have hpt : ∀ g i, ‖rE g i (((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + t i) -
      ((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + r i))‖ ^ 2 ≤
      (P : ℝ)⁻¹ * ∑ p, ‖rE g i (Z p g (A.R.1 + t i) - Z p g (A.R.1 + r i))‖ ^ 2 := by
    intro g i
    have e : rE g i (((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + t i) -
        ((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + r i)) =
        ((P : ℂ)⁻¹) • ∑ p, rE g i (Z p g (A.R.1 + t i) - Z p g (A.R.1 + r i)) := by
      rw [← smul_sub, ← Finset.sum_sub_distrib, map_smul, map_sum]
    rw [e]
    exact norm_avg_sq_le hP _
  calc ∑ g ∈ Gs, ∑ i, ‖rE g i (((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + t i) -
        ((P : ℂ)⁻¹) • ∑ p, Z p g (A.R.1 + r i))‖ ^ 2
      ≤ ∑ g ∈ Gs, ∑ i, (P : ℝ)⁻¹ * ∑ p,
          ‖rE g i (Z p g (A.R.1 + t i) - Z p g (A.R.1 + r i))‖ ^ 2 :=
        Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun i _ => hpt g i
    _ = (P : ℝ)⁻¹ * ∑ p, ∑ g ∈ Gs, ∑ i,
          ‖rE g i (Z p g (A.R.1 + t i) - Z p g (A.R.1 + r i))‖ ^ 2 := by
        simp only [Finset.mul_sum]
        exact sum_comm_out Gs (fun _ => Finset.univ) Finset.univ _
    _ ≤ (P : ℝ)⁻¹ * ∑ _p : Fin P, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ =>
          hcap p r t hrt hdis htd Ec hEc) (by positivity)
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end ActiveSetup

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

open Classical in
/-- Blueprint lines 1861-1877 and 2386 ("joint group budgets for positive ball ranges"): the
single ball-pad outputs of the groups of `G_s` after a shared history have joint variation
capacity `G₀ · 4 |R|` on cells certified for their groups. -/
theorem varCap_ballP (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (dv : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) (Gs : Finset bf.Grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool))
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset ({G // G ∈ Gs} × (bf.Lab ⊕ Fin fp.Mc))).filter
      fun q : {G // G ∈ Gs} × (bf.Lab ⊕ Fin fp.Mc) => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧
        ∃ p : Fin fp.P,
        y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I q.1.1 j (p + 1)) dv).card ≤ N)
    (hτN : τ * N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kk + 1)) (p : Fin fp.P) :
    A.VarCap Gs (fun G h => fp.basicOutM l s mb (fp.ballMaskT l s mb G j p) ls h)
      (fun G J => fp.Cert k G J) (capV A cc kk) := by
  intro ι _ r t hrt hdis htd Ec hEc
  have h := fp.basic_variation_ballP l s hT htag dv mb hanc hne (ι := {G // G ∈ Gs}) (ι' := ι)
    Subtype.val Subtype.val_injective k j hPH ls r t hrt hdis htd (fun G i => Ec G.1 i)
    (fun G i J hJ => ⟨(hEc G.1 i J hJ).1, (hEc G.1 i J hJ).2.1⟩)
    (fun G i J hJ => (hEc G.1 i J hJ).2.2) hroot hτ hτ1 hHed hN hτN cc hc hk hDm hDb hn p
  refine le_trans (le_of_eq ?_) h
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Gs]

/-- Blueprint lines 1868 and 2386 ("shared budgets for group-independent histories"): a single
cumulative-pad output after a shared history has variation capacity `G₀ · 4 |R|`, counted once. -/
theorem varCap_cumP (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (G₀ : bf.Grp) (m : ℕ) (p : Fin fp.P) (ls : List (ℕ × Bool))
    (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap {G₀} (fun _ h => fp.basicOutM l s mb (fp.cumMaskT l s mb m p) ls h)
      (fun _ _ => True) (capV A cc kk) := by
  intro ι _ r t hrt hdis htd Ec hEc
  rw [Finset.sum_singleton]
  exact fp.basic_variation_cumP l s mb hne m p ls r t hrt hdis htd (Ec G₀)
    (fun i J hJ => (hEc G₀ i J hJ).1) cc hc hk hDm hDb hn

/-- The shared history outputs have variation capacity `G₀ · 4 |R|`, counted once. -/
theorem varCap_histOut (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (G₀ : bf.Grp) (ls : List (ℕ × Bool))
    (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap {G₀} (fun _ h => fp.histOut l s mb ls h) (fun _ _ => True) (capV A cc kk) := by
  intro ι _ r t hrt hdis htd Ec hEc
  rw [Finset.sum_singleton]
  exact fp.histOut_variation_le l s mb hne ls r t hrt hdis htd (Ec G₀)
    (fun i J hJ => (hEc G₀ i J hJ).1) cc hc hk hDm hDb hn

/-- The global basic inputs have variation capacity `G₀ · 4 |R|`, counted once. -/
theorem varCap_gBasic (l : Fin 4) (hne : A.cells.Nonempty) (G₀ : bf.Grp) (cc : ℕ) {kk : ℝ}
    (hk : 1 ≤ kk) :
    A.VarCap {G₀} (fun _ h => bf.gBasic fp.Mc l h) (fun _ _ => True) (capV A cc kk) := by
  intro ι _ r t hrt hdis _ Ec hEc
  rw [Finset.sum_singleton]
  exact (fp.gBasic_variation hne l r t hrt hdis (Ec G₀) (fun i J hJ => (hEc G₀ i J hJ).1)).trans
    (four_le_capV cc kk hk)

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

theorem role_ite (c d : Fin 4) (v : Bool) :
    (if v then T.Lf.role c else T.Lf.role d) = T.Lf.role (if v then c else d) := by
  cases v <;> rfl

/-- The cumulative history layers of the later descriptors of a slot are at most the steps. -/
theorem lsCum_drop_le (c d : Fin 4) (t t' : List ℕ) (w : Bool) (j : ℕ) :
    (lsCum (T.desc c d t t') (restIdxM w ((T.desc c d t t').drop (j + 1)) (j + 1))).length ≤
      (T.desc c d t t').length := by
  rw [lsCum_length]
  refine (restIdxM_length_le w _ _).trans ?_
  simp

/-- The descriptor of a step is a slot descriptor. -/
theorem step_slot (c d : Fin 4) (t t' : List ℕ) {j : ℕ} (hj : j < (T.desc c d t t').length) :
    ((T.desc c d t t').getD j (true, 0, none)).2 =
        (fp.brank (if ((T.desc c d t t').getD j (true, 0, none)).1 then T.Lf.role c
          else T.Lf.role d), none) ∨
      ∃ m, ((T.desc c d t t').getD j (true, 0, none)).2 = (fp.crank m, some m) := by
  have hmem : (T.desc c d t t').getD j (true, 0, none) ∈ T.desc c d t t' := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  exact fp.mergeDescM_slot (T.Lf.role c) (T.Lf.role d) t t' hmem

/-- The slot of the step `j` of a chain pair. -/
noncomputable def vS (c d : Fin 4) (t t' : List ℕ) (j : ℕ) : Fin 4 :=
  if ((T.desc c d t t').getD j (true, 0, none)).1 then c else d

/-- The other slot of the step `j` of a chain pair. -/
noncomputable def wS (c d : Fin 4) (t t' : List ℕ) (j : ℕ) : Fin 4 :=
  if !((T.desc c d t t').getD j (true, 0, none)).1 then c else d

/-- The shared history layers of the slot of the step `j`. -/
noncomputable def lsV (c d : Fin 4) (t t' : List ℕ) (j : ℕ) : List (ℕ × Bool) :=
  lsCum (T.desc c d t t') (restIdxM ((T.desc c d t t').getD j (true, 0, none)).1
    ((T.desc c d t t').drop (j + 1)) (j + 1))

/-- The shared history layers of the other slot of the step `j`. -/
noncomputable def lsW (c d : Fin 4) (t t' : List ℕ) (j : ℕ) : List (ℕ × Bool) :=
  lsCum (T.desc c d t t') (restIdxM (!((T.desc c d t t').getD j (true, 0, none)).1)
    ((T.desc c d t t').drop (j + 1)) (j + 1))

/-- Blueprint line 2263 ("split its terminal complementary band into the shared identity"): the
identity outputs of a step have variation capacity `G₀ · 4 |R|`, counted once. -/
theorem varCap_top (a c d : Fin 4) (t t' : List ℕ) (j : ℕ) (hne : A.cells.Nonempty)
    (G₀ : bf.Grp) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hlen : ((T.desc c d t t').length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap {G₀} (fun G h => T.Xo a c d G t t' j (fp.P + 1) h) (fun _ _ => True)
      (capV A cc kk) := by
  intro ι _ r tt hrt hdis htd Ec hEc
  have hls : ((T.lsV c d t t' j).length : ℝ) ≤ cc * (Real.log kk + 1) :=
    (Nat.cast_le.mpr (T.lsCum_drop_le c d t t' _ j)).trans hlen
  by_cases hemp : restIdxM ((T.desc c d t t').getD j (true, 0, none)).1
    ((T.desc c d t t').drop (j + 1)) (j + 1) = []
  · have hZ : ∀ g ∈ ({G₀} : Finset bf.Grp), ∀ h : ℤ,
        bf.gBasic fp.Mc (T.vS c d t t' j) h = T.Xo a c d g t t' j (fp.P + 1) h := by
      intro g _ h
      rw [T.Xo_top, ite_eq_left_of_eq_true _ _ (eq_true hemp)]
      rfl
    exact A.varCap_congr hZ (fp.varCap_gBasic (T.vS c d t t' j) hne G₀ cc hk) r tt hrt hdis htd Ec
      hEc
  · have hZ : ∀ g ∈ ({G₀} : Finset bf.Grp), ∀ h : ℤ,
        fp.histOut (T.vS c d t t' j) (T.cat (T.vS c d t t' j)) (T.mbs (T.vS c d t t' j))
          (T.lsV c d t t' j) h = T.Xo a c d g t t' j (fp.P + 1) h := by
      intro g _ h
      rw [T.Xo_top, ite_eq_right_of_eq_false _ _ (eq_false hemp)]
      rfl
    exact A.varCap_congr hZ (fp.varCap_histOut (T.vS c d t t' j) (T.cat (T.vS c d t t' j))
      (T.mbs (T.vS c d t t' j)) hne G₀ (T.lsV c d t t' j) cc hc hk (hDm _) hDb hls) r tt hrt hdis
      htd Ec hEc

/-- Blueprint line 2263 ("if the outgoing filter is cumulative ... its complementary band history
is shared across groups"): the pad outputs of a cumulative step have variation capacity
`G₀ · 4 |R|`, counted once. -/
theorem varCap_pad_cum (a c d : Fin 4) (t t' : List ℕ) {j : ℕ}
    (hj : j < (T.desc c d t t').length) (n : ℕ) (hn : n < fp.P) (hY : T.cumY c d t t' j)
    (hne : A.cells.Nonempty) (G₀ : bf.Grp) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hlen : ((T.desc c d t t').length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap {G₀} (fun G h => T.Xo a c d G t t' j (n + 1) h) (fun _ _ => True)
      (capV A cc kk) := by
  intro ι _ r tt hrt hdis htd Ec hEc
  have hls : ((T.lsV c d t t' j).length : ℝ) ≤ cc * (Real.log kk + 1) :=
    (Nat.cast_le.mpr (T.lsCum_drop_le c d t t' _ j)).trans hlen
  obtain ⟨m, hm⟩ : ∃ m, ((T.desc c d t t').getD j (true, 0, none)).2 = (fp.crank m, some m) := by
    rcases T.step_slot c d t t' hj with h1 | h1
    · exact absurd (by rw [h1]) hY
    · exact h1
  refine A.varCap_congr (fun g _ h => ?_) (fp.varCap_cumP (T.vS c d t t' j) (T.cat (T.vS c d t t'
      j))
    (T.mbs (T.vS c d t t' j)) hne G₀ m ⟨n, hn⟩ (T.lsV c d t t' j) cc hc hk (hDm _) hDb hls) r tt
        hrt hdis htd Ec hEc
  rw [T.Xo_pad a c d g t t' j n hn h, fp.cmpMaskM_cum _ _ _ _ _ _ _ _ _ j _ hm]
  rfl

/-- Blueprint line 2263 ("the other complement ... is shared"): the other complements with a
cumulative later history have variation capacity `G₀ · 4 |R|`, counted once. -/
theorem varCap_F_cum (a c d : Fin 4) (t t' : List ℕ) (j : ℕ) (hF : T.cumF c d t t' j)
    (hne : A.cells.Nonempty) (G₀ : bf.Grp) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hlen : ((T.desc c d t t').length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap {G₀} (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
      (T.Lf.role d) (T.desc c d t t') j h) (fun _ _ => True) (capV A cc kk) := by
  intro ι _ r tt hrt hdis htd Ec hEc
  have hls : ((T.lsW c d t t' j).length : ℝ) ≤ cc * (Real.log kk + 1) :=
    (Nat.cast_le.mpr (T.lsCum_drop_le c d t t' _ j)).trans hlen
  by_cases hemp : restIdxM (!((T.desc c d t t').getD j (true, 0, none)).1)
    ((T.desc c d t t').drop (j + 1)) (j + 1) = []
  · refine A.varCap_congr (fun g _ h => ?_) (fp.varCap_gBasic (T.wS c d t t' j) hne G₀ cc hk) r tt
      hrt hdis htd Ec hEc
    rw [T.F_cum a c d g t t' j hF, ite_eq_left_of_eq_true _ _ (eq_true hemp)]
    rfl
  · refine A.varCap_congr (fun g _ h => ?_) (fp.varCap_histOut (T.wS c d t t' j) (T.cat (T.wS c d
      t t' j))
      (T.mbs (T.wS c d t t' j)) hne G₀ (T.lsW c d t t' j) cc hc hk (hDm _) hDb hls) r tt hrt hdis
          htd Ec hEc
    rw [T.F_cum a c d g t t' j hF, ite_eq_right_of_eq_false _ _ (eq_false hemp)]
    rfl

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

open Classical in
/-- The localization data of the slot catalogs used by the joint ball variation (the template
catalogs, their tags, the ball levels and the overlap of the ball labels of the groups). -/
structure BallData (gset : Finset bf.Grp) where
  hT : ∀ l, ∀ e ∈ T.cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
    e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag
  htag : ∀ l, ∀ e ∈ T.cat l, bf.occAvail e.tag.2.1 e.tag.1
  /-- Chart tag used as the distinguished representative in each slot. -/
  dv : Fin 4 → bf.Vtx
  hPH : ∀ l, fp.bbase (T.Lf.role l) + fp.P ≤ fp.Hmax
  /-- Uniform count bound for certified main labels visible at a point. -/
  N : ℕ
  hN : ∀ l y, ((Finset.univ : Finset ({G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc))).filter
    fun q : {G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc) => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧
      ∃ p : Fin fp.P,
      y ∈ dyadicGridCell A.G I.1 I.2 ∧
      q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (T.cat l) I (fp.brank (T.Lf.role l))
        (fp.bmask I q.1.1 (T.Lf.role l) (p + 1)) (dv l)).card ≤ N

/-- Blueprint lines 2263 and 2386 ("joint group budgets for positive ball ranges"): the pad outputs
of a ball step have joint variation capacity `G₀ · 4 |R|` over the groups, on cells certified
for their groups. -/
theorem varCap_pad_ball (a c d : Fin 4) (t t' : List ℕ) {j : ℕ}
    (hj : j < (T.desc c d t t').length) (n : ℕ) (hn : n < fp.P) (hY : ¬ T.cumY c d t t' j)
    {gset : Finset bf.Grp} (B : T.BallData gset) (hanc : A.AncClosed) (hne : A.cells.Nonempty)
    (k : ℕ) {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hlen : ((T.desc c d t t').length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap gset (fun G h => T.Xo a c d G t t' j (n + 1) h) (fun G J => fp.Cert k G J)
      (capV A cc kk) := by
  intro ι _ r tt hrt hdis htd Ec hEc
  have hls : ((T.lsV c d t t' j).length : ℝ) ≤ cc * (Real.log kk + 1) :=
    (Nat.cast_le.mpr (T.lsCum_drop_le c d t t' _ j)).trans hlen
  have hb : ((T.desc c d t t').getD j (true, 0, none)).2 =
      (fp.brank (if ((T.desc c d t t').getD j (true, 0, none)).1 then T.Lf.role c
        else T.Lf.role d), none) := by
    rcases T.step_slot c d t t' hj with h1 | ⟨m, hm⟩
    · exact h1
    · exact (hY (by unfold cumY; rw [hm]; simp)).elim
  have hZ : ∀ g ∈ gset, ∀ h : ℤ,
      fp.basicOutM (T.vS c d t t' j) (T.cat (T.vS c d t t' j)) (T.mbs (T.vS c d t t' j))
        (fp.ballMaskT (T.vS c d t t' j) (T.cat (T.vS c d t t' j)) (T.mbs (T.vS c d t t' j)) g
          (T.Lf.role (T.vS c d t t' j)) ⟨n, hn⟩) (T.lsV c d t t' j) h =
        T.Xo a c d g t t' j (n + 1) h := by
    intro g _ h
    rw [T.Xo_pad a c d g t t' j n hn h, fp.cmpMaskM_ball _ _ _ _ _ _ _ _ _ j _ hb, T.role_ite]
    rfl
  exact A.varCap_congr hZ (fp.varCap_ballP (T.vS c d t t' j) (T.cat (T.vS c d t t' j))
    (B.hT _) (B.htag _) (B.dv _) (T.mbs (T.vS c d t t' j)) hanc hne gset k
    (T.Lf.role (T.vS c d t t' j)) (B.hPH _) (T.lsV c d t t' j) hroot hτ hτ1 hHed (B.hN _) hτN cc
    hc hk (hDm _) hDb hls ⟨n, hn⟩) r tt hrt hdis htd Ec hEc

/-- Blueprint lines 2263 and 2386 ("the other complement ... has a positive ball outermost"):
the other complements with a ball in their later history have joint variation capacity
`G₀ · 4 |R|` over the groups (pad averages of single ball-pad outputs, by Jensen). -/
theorem varCap_F_ball (a c d : Fin 4) (t t' : List ℕ) (j : ℕ) (hF : ¬ T.cumF c d t t' j)
    {gset : Finset bf.Grp} (B : T.BallData gset) (hanc : A.AncClosed) (hne : A.cells.Nonempty)
    (k : ℕ) {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hlen : ((T.desc c d t t').length : ℝ) ≤ cc * (Real.log kk + 1)) :
    A.VarCap gset (fun G h => fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) G (T.Lf.role c)
      (T.Lf.role d) (T.desc c d t t') j h) (fun G J => fp.Cert k G J) (capV A cc kk) := by
  intro ι _ r tt hrt hdis htd Ec hEc
  obtain ⟨ls, hls, hFeq⟩ := T.F_ball a c d t t' j hF
  have hp : ∀ p : Fin fp.P, A.VarCap gset (fun G h => fp.basicOutM (T.wS c d t t' j)
      (T.cat (T.wS c d t t' j)) (T.mbs (T.wS c d t t' j))
      (fp.ballMaskT (T.wS c d t t' j) (T.cat (T.wS c d t t' j)) (T.mbs (T.wS c d t t' j)) G
        (T.Lf.role (T.wS c d t t' j)) p) ls h) (fun G J => fp.Cert k G J) (capV A cc kk) :=
    fun p => fp.varCap_ballP (T.wS c d t t' j) (T.cat (T.wS c d t t' j)) (B.hT _) (B.htag _)
      (B.dv _) (T.mbs (T.wS c d t t' j)) hanc hne gset k (T.Lf.role (T.wS c d t t' j)) (B.hPH _)
      ls hroot hτ hτ1 hHed (B.hN _) hτN cc hc hk (hDm _) hDb ((Nat.cast_le.mpr hls).trans hlen) p
  have hZ : ∀ g ∈ gset, ∀ h : ℤ, ((fp.P : ℂ)⁻¹) • ∑ p : Fin fp.P,
      fp.basicOutM (T.wS c d t t' j) (T.cat (T.wS c d t t' j)) (T.mbs (T.wS c d t t' j))
        (fp.ballMaskT (T.wS c d t t' j) (T.cat (T.wS c d t t' j)) (T.mbs (T.wS c d t t' j)) g
          (T.Lf.role (T.wS c d t t' j)) p) ls h =
      fp.FfrM T.cat T.mbs a c d (fp.Lc + 5) g (T.Lf.role c) (T.Lf.role d) (T.desc c d t t') j h :=
          by
    intro g _ h
    rw [hFeq g h, T.role_ite]
    rfl
  exact A.varCap_congr hZ (A.varCap_avg fp.hP hp) r tt hrt hdis htd Ec hEc

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

open Classical in
/-- Blueprint lines 2375-2456, the two-side estimate of one localization leaf on the main columns,
with the freeze budgets of the third strong factors derived from `lem:variation`: the frozen
outputs (identity outputs, cumulative pads and shared other complements counted once; ball pads
and other complements with a ball jointly over the groups, on certified cells) have variation
capacity `G₀ · 4 |R|` (`capV`). -/
theorem leaf_two_two_ballM {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    (hne : A.cells.Nonempty)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : T.K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, T.bk I < Bn) (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    (okZ : Fin 4 → bf.Grp → ℤ × ℤ → Prop) (BZ EW : Fin 4 → ℝ)
    (hcap : ∀ l, T.u ≠ some l → A.VarCap gset (T.Z l) (okZ l) (BZ l))
    (hok : ∀ l, T.u ≠ some l → ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → okZ l G J)
    (hEW : ∀ l, T.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ T.bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + ((T.K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (T.Wb l G (A.R.1 + ((T.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ EW l)
    {EU : ℝ} (hEU : ∀ l, T.u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) (T.sv l G I)‖ ^ 2 ≤ EU)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 < C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → T.u ≠ some c → T.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤ cF * T.ns a G I * T.ns b G I)
    (hbas : ∀ J ∈ A.cells, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l J‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G J.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖T.out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, ((T.pe d).length * (T.pe c).length : ℝ) ≤ Np)
    {Bs : ℝ} (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    -- the third strong factors
    (G₀ : bf.Grp)
    {Cy : ℝ} (hy : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {BU : ℝ} (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (B : T.BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hJc : (Jm : ℝ) ≤ cc * (Real.log kk + 1))
    -- numerics of the near bands
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, T.u ≠ some a → fp.stackEA (nOs Lp Jm) (T.cat a) (T.mbs a) T.Dpre N (BZ a) (EW a) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, T.u ≠ some b → (nOs Lp Jm).card * (N * BZ b + EW b) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (nOs Lp Jm).card * EU ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      6 * 256 * Np * (τ + cF) * ((Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) / dyadicGridLength A.G A.R.1) / ρ) *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          T.nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (((Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) / dyadicGridLength A.G A.R.1) / ρ) ^
            (p / 2) *
          ((Bs / dyadicGridLength A.G A.R.1 +
            T.B3cap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) / dyadicGridLength A.G A.R.1) / ρ) ^
            (p / 2) *
          ((Bs / dyadicGridLength A.G A.R.1 +
            T.B3cap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) / dyadicGridLength A.G A.R.1) / ρ) ^
            (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, T.s2 G I ≤
        (Bs / dyadicGridLength A.G A.R.1 +
          T.B3cap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) / dyadicGridLength A.G A.R.1) / ρ := by
  have hlen : ∀ c d i i', ((T.desc c d (T.tOf c i) (T.tOf d i')).length : ℝ) ≤
      cc * (Real.log kk + 1) := fun c d i i' => (Nat.cast_le.mpr (hJm c d i i')).trans hJc
  have hBv : 0 ≤ capV A cc kk :=
    le_trans (by have := dyadicGridLength_pos A.G A.R.1; positivity) (four_le_capV cc kk hk)
  refine T.leaf_two_two_capM hq2 hq3 hanc hKNd hKN S hS hroot gs gset hgs Lp Jm Bn k hBn hLp hJm
    Act hact hMp okZ BZ EW hcap hok hEW hEU hτ hcF hC₀ hB₀ hpair hfar hbas hout hNp hBs G₀ A.cells
    subset_rfl (fun I hI J hJ _ _ => hJ) (fun G => A.cells.filter fun J => fp.Cert k G J)
    (fun G J => fp.Cert k G J) (fun G _ J hJ => Finset.mem_filter.mp hJ)
    (fun I hI G hG J hJ hsub _ => Finset.mem_filter.mpr ⟨hJ, Cert.mono fp (hcertS I hI G hG)
        hsub⟩) hy
    hBv hBU ?_ ?_ ?_ ?_ ?_ hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1
  · intro a c d i i' j _
    exact T.varCap_top a c d _ _ j hne G₀ cc hc hk hDm hDb (hlen c d i i')
  · intro a c d i i' j n hj hn hY
    exact T.varCap_pad_cum a c d _ _ hj n hn hY hne G₀ cc hc hk hDm hDb (hlen c d i i')
  · intro a c d i i' j _ hF
    exact T.varCap_F_cum a c d _ _ j hF hne G₀ cc hc hk hDm hDb (hlen c d i i')
  · intro a c d i i' j n hj hn hY
    exact T.varCap_pad_ball a c d _ _ hj n hn hY B hanc hne k hroot' hτ' hτ1 hHed hτN cc hc hk
      hDm hDb (hlen c d i i')
  · intro a c d i i' j _ hF
    exact T.varCap_F_ball a c d _ _ j hF B hanc hne k hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb
      (hlen c d i i')

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- The squared normalized side sizes of a group at a cell. -/
theorem s2_eq (G : bf.Grp) (I : ℤ × ℤ) :
    T.s2 G I = ∑ l, ‖T.sv l G I‖ ^ 2 / dyadicGridLength A.G I.1 := by
  unfold s2 ns
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [div_pow, Real.sq_sqrt (dyadicGridLength_pos A.G I.1).le]

/-- The joint path cap `T_c = (B_s + B_3)/(ρ |R|)` of the side estimate. -/
noncomputable def Tcap (Lp Jm : ℕ) (C₀ B₀ Cy Bs BU Bv ρ : ℝ) : ℝ :=
  (Bs / dyadicGridLength A.G A.R.1 + T.B3cap Lp Jm C₀ B₀ Cy Bs BU Bv / dyadicGridLength A.G A.R.1) /
    ρ

open Classical in
/-- Blueprint lines 2446-2456, the side estimate of one localization leaf on the main columns
(unconditional form on the leaf data): one cut family of root fraction at most `2ρ` such that on
the retained cells
* the weighted active minimum of the two-side terms (two sides, whole current outputs in the
  other positions) is at most the pair-small and far absolute bound, six times the critical
  near-band bounds (`eq:near-band`), and the power cost of the three strong factors, with shared
  frozen histories counted once (`leaf_two_two_ballM`);
* on every set of retained cells on which given cores have normalized size at most `B_c`, the
  weighted active minimum of the error-free core/side patterns with at least three sides is at
  most their power cost `η^{1-p} (81 C_κ max(B_c, √T_c))^p T_c^{3p/2} |R|` (`eq:three-sides`,
  `eq:min-power`): the sides have normalized size at most `√T_c` on retained cells;
* the side cap: the retained paths carry squared normalized side sizes at most `T_c`
  (`eq:side-cap`),
with the joint path cap `T_c = (B_s + B_3)/(ρ |R|)`. -/
theorem leaf_side_estimateM {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    (hne : A.cells.Nonempty)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : T.K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, T.bk I < Bn) (hLp : ∀ l, (T.pe l).length ≤ Lp)
    (hJm : ∀ c d i i', (T.desc c d (T.tOf c i) (T.tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    (okZ : Fin 4 → bf.Grp → ℤ × ℤ → Prop) (BZ EW : Fin 4 → ℝ)
    (hcap : ∀ l, T.u ≠ some l → A.VarCap gset (T.Z l) (okZ l) (BZ l))
    (hok : ∀ l, T.u ≠ some l → ∀ I ∈ S, ∀ G ∈ gs I, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → okZ l G J)
    (hEW : ∀ l, T.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ T.bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + ((T.K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (T.Wb l G (A.R.1 + ((T.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ EW l)
    {EU : ℝ} (hEU : ∀ l, T.u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) (T.sv l G I)‖ ^ 2 ≤ EU)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 < C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → T.u ≠ some c → T.u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤ cF * T.ns a G I * T.ns b G I)
    (hbas : ∀ J ∈ A.cells, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l J‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G J.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖T.out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, ((T.pe d).length * (T.pe c).length : ℝ) ≤ Np)
    {Bs : ℝ} (hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖T.sv l G I‖ ^ 2 ≤ Bs)
    (G₀ : bf.Grp)
    {Cy : ℝ} (hy : ∀ I ∈ S, ∀ l, T.u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {BU : ℝ} (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (B : T.BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (T.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hJc : (Jm : ℝ) ≤ cc * (Real.log kk + 1))
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, T.u ≠ some a → fp.stackEA (nOs Lp Jm) (T.cat a) (T.mbs a) T.Dpre N (BZ a) (EW a) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, T.u ≠ some b → (nOs Lp Jm).card * (N * BZ b + EW b) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (nOs Lp Jm).card * EU ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then T.out l G I else T.sv l G I)‖ ≤
      6 * 256 * Np * (τ + cF) * T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          T.nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
          T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
          T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      (∀ (core err : ℤ × ℤ → bf.Grp → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
        (S' : Finset (ℤ × ℤ)), S' ⊆ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∀ {Bc : ℝ}, 0 ≤ Bc →
        (∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
          ‖core I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength A.G I.1)) →
        ∑ I ∈ S', dyadicGridLength A.G I.1 * min η (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
            ‖∑ G ∈ gs I, fp.Λc I (patternPiece (core I G) (fun l => T.sv l G I) (err I G) σ)‖) ≤
        η ^ (1 - p) * (81 * localFormUniformConstant κ' *
          max Bc (Real.sqrt (T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ))) ^ p *
          (T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
            T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
            T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ ^ (p / 2) *
            dyadicGridLength A.G A.R.1)) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, T.s2 G I ≤
        T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ := by
  obtain ⟨C, hC, hlen, htwo, hcapS⟩ := T.leaf_two_two_ballM hq2 hq3 hanc hne hKNd hKN S hS hroot
    gs gset hgs Lp Jm Bn k hBn hLp hJm Act hact hMp hcertS okZ BZ EW hcap hok hEW hEU hτ hcF hC₀
    hB₀ hpair hfar hbas hout hNp hBs G₀ hy hBU B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hJc hP
    Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1
  refine ⟨C, hC, hlen, htwo, fun core err S' hS' Bc hBc hcore => ?_, hcapS⟩
  set Tc := T.Tcap Lp Jm C₀ B₀ Cy Bs BU (capV A cc kk) ρ with hTc
  have hsv : ∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
      ‖T.sv l G I‖ ≤ Real.sqrt Tc * Real.sqrt (dyadicGridLength A.G I.1) := by
    intro I hI G hG l
    have hr := dyadicGridLength_pos A.G I.1
    have hIx : dyadicGridLeft A.G I.1 I.2 ∈ dyadicGridCell A.G I.1 I.2 :=
      dyadicGridCell_left_mem A.G I.1 I.2
    have h1 : T.ns l G I ^ 2 ≤ Tc := by
      refine le_trans ?_ (hcapS (dyadicGridLeft A.G I.1 I.2))
      refine le_trans ?_ (Finset.single_le_sum (f := fun I => ∑ G ∈ gs I, T.s2 G I)
        (fun J _ => Finset.sum_nonneg fun G _ => T.s2_nonneg G J)
        (Finset.mem_filter.mpr ⟨hS' hI, hIx⟩))
      refine le_trans ?_ (Finset.single_le_sum (f := fun G => T.s2 G I)
        (fun G _ => T.s2_nonneg G I) hG)
      exact Finset.single_le_sum (f := fun l => T.ns l G I ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ l)
    have h2 : T.ns l G I ≤ Real.sqrt Tc := by
      rw [← Real.sqrt_sq (T.ns_nonneg l G I)]
      exact Real.sqrt_le_sqrt h1
    have h3 : ‖T.sv l G I‖ = T.ns l G I * Real.sqrt (dyadicGridLength A.G I.1) := by
      unfold ns
      rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr hr).ne']
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  refine three_side_patterns_sum_le A.G S' A.R
    (fun I hI => hroot I (Finset.mem_filter.mp (hS' hI)).1) gs fp.Λc
    (localFormUniformConstant_nonneg κ') (le_max_of_le_left hBc) (fun I _ x => fp.norm_Λc_leM I x)
    core (fun I G l => T.sv l G I) err (fun I hI G hG l => ⟨(hcore I hI G hG l).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)),
      (hsv I hI G hG l).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))⟩)
    (fun x => ?_) hη hp hp1
  refine le_trans ?_ (hcapS x)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun G _ =>
    (T.s2_eq G I).symm)) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun I hI => ?_)
    fun J _ _ => Finset.sum_nonneg fun G _ => T.s2_nonneg G J
  obtain ⟨hI1, hI2⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨hS' hI1, hI2⟩

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## The leaf data from the side states (blueprint lines 2123-2130, 2236-2237) -/

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}

/-- The input of the side estimate on one localization leaf: the slot catalogs with their main
budgets, the search leaf, the optional slot of the basic `U` argument (whose inputs are the basic
sides `U_{l,I}` of prop:base), and the mode systems with the frozen coefficients of the linear
sides (`prop:linear-side`) defining the side states `S_{l,G,s} = Z_{l,G,s} - Z_{l,G,u_b} +
V_{l,G,b}` (blueprint `eq:sides`). -/
structure SideInput (fp : bf.FamParams) where
  /-- Catalog columns in each slot of the mode-side input. -/
  cat : Fin 4 → List (CatCol bf.Vtx)
  /-- Pathwise main-label budget for each slot catalog. -/
  mbs : ∀ l, bf.MainBudget (cat l)
  /-- Search leaf determining the side filters. -/
  Lf : SearchLeaf
  /-- Optional slot carrying the expanded outer input. -/
  u : Option (Fin 4)
  /-- Height and block schedule of the mode-side input. -/
  S : ModeSchedule
  hA : 6 ≤ S.A0
  /-- Coherence and side-event parameters of the mode-side input. -/
  SP : SideParams
  hK : 1 ≤ S.K
  /-- Number of primary column labels in each frozen mode system. -/
  n : ℕ
  /-- Frozen mode system assigned to each slot and group. -/
  Ms : Fin 4 → bf.Grp → ModeSystem A.G n
  /-- Frozen mode coefficients indexed by block start and pre-cell. -/
  c : ∀ l G, ℤ → ℤ × ℤ → (Ms l G).Md → ℂ

variable {fp : bf.FamParams}

/-- The side input with the clearing integer of its schedule replaced by `q` (the side input of
one group, blueprint line 1890); all other data are those of `D`. -/
def SideInput.withQ0 (D : fp.SideInput) (q : ℕ) : fp.SideInput := { D with S := D.S.withQ0 q }

namespace SideInput
variable (D : fp.SideInput) (q : ℕ)

@[simp] theorem withQ0_S : (D.withQ0 q).S = D.S.withQ0 q := rfl
@[simp] theorem withQ0_SP : (D.withQ0 q).SP = D.SP := rfl
@[simp] theorem withQ0_u : (D.withQ0 q).u = D.u := rfl

end SideInput


namespace SideInput
variable (D : fp.SideInput)

/-- The rolling outputs `Z_{l,G,h}` in physical coordinates. -/
noncomputable def Zr (l : Fin 4) (G : bf.Grp) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.basicOut l (D.cat l) (D.mbs l) G (D.Lf.role l)
    (D.Lf.layers l) h)

/-- The block input `W_b = Z_b - Z_{u_b} + V_b` of the block starting at `b`. -/
noncomputable def Wr (l : Fin 4) (G : bf.Grp) (b : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  D.Zr l G b - fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.frozenZ l (D.cat l) (D.mbs l) G
    (D.Lf.role l) (D.Lf.layers l) (b - 4 * D.S.K)) +
    fp.physMain (D.Ms l G).Md ((D.Ms l G).blockSide D.S D.hA D.SP b (fp.retainedV G b D.S.K)
      (D.c l G b))

/-- The global side state at the depth `h` (blueprint `eq:sides`). -/
noncomputable def gs' (l : Fin 4) (G : bf.Grp) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  fp.sideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l) (D.Lf.layers l) D.S D.hA D.SP
    (D.c l G (A.blkStart D.S.K h)) (A.blkStart D.S.K h) h

theorem gs'_eq (l : Fin 4) (G : bf.Grp) (h : ℤ) :
    D.gs' l G h = D.Zr l G h - D.Zr l G (A.blkStart D.S.K h) + D.Wr l G (A.blkStart D.S.K h) := by
  unfold gs' sideState Wr Zr
  abel

theorem gs'_range (l : Fin 4) (G : bf.Grp) (h : ℤ) :
    D.gs' l G h ∈ LinearMap.range (colRelabel (bf.rv fp.Mc (D.cat l))).toLinearMap := by
  unfold gs' sideState
  exact Submodule.add_mem _ (Submodule.sub_mem _ (fp.physMain_mem_range _ _)
    (fp.physMain_mem_range _ _)) (fp.physMain_mem_range _ _)

open Classical in
/-- The leaf data of the side estimate: the basic slots carry the side states restricted to the
cells, the `U` slot (if any) its whole output. -/
noncomputable def toLeaf : fp.SideLeafM where
  cat := D.cat
  mbs := D.mbs
  Lf := D.Lf
  u := D.u
  K := D.S.K
  hK := D.hK
  xin := fun l I => if D.u = some l then bf.Ucol fp.Mc l I else bf.basicIn fp.Mc l I
  xin_basic := fun l hl I => by simp only [hl, ite_false]
  sv := fun l G I => if D.u = some l then
      fp.ballFilt l (D.cat l) I G (D.Lf.role l)
        (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l) (bf.Ucol fp.Mc l I))
    else columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      (D.gs' l G I.1)
  gside := D.gs'
  sv_eq := fun l hl G I _ => by simp only [hl, ite_false]
  gside_range := fun l _ G h => D.gs'_range l G h
  Z := D.Zr
  Wb := D.Wr
  gside_eq := fun l _ G h => D.gs'_eq l G h
  sv_u := fun l hl G I => by simp only [hl, ite_true]

open Classical in
/-- The leaf data with per-group clearing integers `qG` (blueprint line 1890: `Q₀` is chosen for
each group center): the side states, block inputs and global sides of the group `G` are those of
the side input with `Q₀ = qG G`. -/
noncomputable def toLeafQ (qG : bf.Grp → ℕ) : fp.SideLeafM where
  cat := D.cat
  mbs := D.mbs
  Lf := D.Lf
  u := D.u
  K := D.S.K
  hK := D.hK
  xin := D.toLeaf.xin
  xin_basic := D.toLeaf.xin_basic
  sv := fun l G I => (D.withQ0 (qG G)).toLeaf.sv l G I
  gside := fun l G h => (D.withQ0 (qG G)).gs' l G h
  sv_eq := fun l hl G I hI => (D.withQ0 (qG G)).toLeaf.sv_eq l hl G I hI
  gside_range := fun l _ G h => (D.withQ0 (qG G)).gs'_range l G h
  Z := D.Zr
  Wb := fun l G b => (D.withQ0 (qG G)).Wr l G b
  gside_eq := fun l _ G h => (D.withQ0 (qG G)).gs'_eq l G h
  sv_u := fun l hl G I => (D.withQ0 (qG G)).toLeaf.sv_u l hl G I

theorem toLeafQ_sv (qG : bf.Grp → ℕ) (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    (D.toLeafQ qG).sv l G I = (D.withQ0 (qG G)).toLeaf.sv l G I := rfl

theorem toLeafQ_out (qG : bf.Grp → ℕ) (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    (D.toLeafQ qG).out l G I = (D.withQ0 (qG G)).toLeaf.out l G I := by
  unfold SideLeafM.out
  rfl

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The energies of the side-state leaf data (blueprint lines 2159-2163) -/

open scoped Classical in
/-- Relabeling keeps the physical input physical. -/
theorem colRelabel_physicalColumnInput {V W : Type*} [Fintype V] [Fintype W] (f : V → W)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    colRelabel f (physicalColumnInput (V := V) g) = physicalColumnInput (V := W) g := by
  refine Lp.ext ?_
  filter_upwards [colRelabel_coeFn f (physicalColumnInput (V := V) g),
    physicalColumnInput_coeFn (V := V) g, physicalColumnInput_coeFn (V := W) g] with y h1 h2 h3
  rw [h1, h2, h3, relabelCLM_apply]
  rw [Finset.sum_eq_single (none : Option V)]
  · simp
  · intro o _ ho
    simp [ho]
  · simp

/-- The physical input of a cell function vanishes off the cell (without integrability). -/
theorem physicalColumnInput_cellLp_vanish' {V : Type*} [Fintype V] (G : RealDyadicGrid)
    (I : ℤ × ℤ) (f : ℝ → ℂ) :
    ∀ᵐ y ∂volume, y ∉ dyadicGridCell G I.1 I.2 →
      (physicalColumnInput (V := V) (cellLp G I f) : ℝ → ColumnHilbert V) y = 0 := by
  unfold cellLp
  split_ifs with h
  · filter_upwards [physicalColumnInput_coeFn (V := V) (h.toLp _), h.coeFn_toLp] with y h1 h2 hy
    rw [h1, h2, Set.indicator_of_notMem hy, zero_smul]
  · filter_upwards [physicalColumnInput_coeFn (V := V) (0 : Lp ℂ 2 (volume : Measure ℝ)),
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with y h1 h2 _
    rw [h1, h2]
    simp

namespace ActiveSetup.BasicFamilies
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} (bf : A.BasicFamilies)

/-- The basic sides lie in the range of every relabeling of the main columns. -/
theorem Ucol_mem_range (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) (I : ℤ × ℤ) :
    bf.Ucol Mc l I ∈ LinearMap.range (colRelabel (bf.rv Mc s)).toLinearMap :=
  ⟨physicalColumnInput _, colRelabel_physicalColumnInput _ _⟩

/-- The basic side of a cell is supported on the cell. -/
theorem restrict_Ucol (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      (bf.Ucol Mc l I) = bf.Ucol Mc l I :=
  columnL2Restriction_eq_self _ _ _ (physicalColumnInput_cellLp_vanish' _ _ _)

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The cell outputs are the cell restrictions of the global outputs of any input of the range
of the relabeling supported on the cell. -/
theorem cell_out_eq (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp)
    (j : ℕ) (ls : List (ℕ × Bool)) {I : ℤ × ℤ} (hI : I ∈ A.cells)
    (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hx : x ∈ LinearMap.range (colRelabel (bf.rv fp.Mc s)).toLinearMap)
    (hxI : columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      x = x) :
    fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls x) =
      colRelabel (bf.rv fp.Mc s) (columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gOut l s mb G j ls I.1
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) x))) := by
  rw [colRelabel_restrict]
  unfold gOut
  rw [ContinuousLinearMap.comp_apply, fp.ball_bridge l s mb G j hI, fp.hist_bridge l s mb ls hI,
    colRelabel_adjoint_of_mem_range (bf.rv_injective fp.Mc s) hx, hxI]

open Classical in
/-- The current group Bessel inequality on one cell (blueprint line 2159, "a basic `U` side is
bounded by current group Bessel"): for an input of the range of the relabeling supported on an
active cell, the outputs of the groups certified at the cell have total square at most
`(1 + τ N C²)` times its square. -/
theorem cell_bessel (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (gset : Finset bf.Grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool))
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (g : Finset bf.Grp) (hg : g ⊆ gset)
    (hcert : ∀ G ∈ g, fp.Cert k G I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset ({G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc))).filter
      fun q => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I q.1.1 j (p + 1)) d).card ≤ N)
    (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hx : x ∈ LinearMap.range (colRelabel (bf.rv fp.Mc s)).toLinearMap)
    (hxI : columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      x = x) :
    ∑ G ∈ g, ‖fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls x)‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ‖x‖ ^ 2 := by
  set! w := ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) x
  have hw : ‖w‖ = ‖x‖ := by
    obtain ⟨z, rfl⟩ := hx
    change ‖ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s))
      (colRelabel (bf.rv fp.Mc s) z)‖ = _
    rw [colRelabel_adjoint_apply_relabel (bf.rv_injective fp.Mc s)]
    exact (norm_colRelabel (bf.rv_injective fp.Mc s) z).symm
  have hj := fp.main_joint l s hT htag d mb (ι := {G // G ∈ gset}) Subtype.val
    Subtype.val_injective k j hPH ls I.1 (fun G => if G.1 ∈ g then {I} else ∅)
    (fun G J hJ => by
      by_cases hG : G.1 ∈ g
      · simp only [hG, ite_true, Finset.mem_singleton] at hJ
        subst hJ; exact ⟨hI, rfl⟩
      · simp [hG] at hJ)
    (fun G J hJ => by
      by_cases hG : G.1 ∈ g
      · simp only [hG, ite_true, Finset.mem_singleton] at hJ
        subst hJ; exact hcert G.1 hG
      · simp [hG] at hJ) hroot hτ hτ1 hHed hN w
  rw [hw] at hj
  refine le_trans ?_ hj
  calc ∑ G ∈ g, ‖fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls x)‖ ^ 2
      = ∑ G ∈ gset, if G ∈ g then
          ‖fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls x)‖ ^ 2 else 0 := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hg]
    _ = ∑ G : {G // G ∈ gset}, if G.1 ∈ g then
          ‖fp.ballFilt l s I G.1 j (layerOp (fun m => fp.cumFilt l s I m) ls x)‖ ^ 2 else 0 :=
        (Finset.sum_coe_sort gset _).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun G _ => ?_
        by_cases hG : G.1 ∈ g
        · simp only [hG, ite_true, Finset.set_biUnion_singleton]
          rw [fp.cell_out_eq l s mb G.1 j ls hI x hx hxI, norm_colRelabel (bf.rv_injective _ _)]
        · simp only [hG, ite_false]
          positivity

end ActiveSetup.BasicFamilies.FamParams

/-- The restriction to an empty union of cells vanishes. -/
theorem norm_sq_restrict_biUnion_empty {V : Type*} [Fintype V] (Gd : RealDyadicGrid)
    (T : Finset (ℤ × ℤ)) (hT : T = ∅) (x : ColumnL2 V) :
    ‖columnL2Restriction (⋃ J ∈ T, dyadicGridCell Gd J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable Gd J.1 J.2) x‖ ^ 2 =
      0 := by
  subst hT
  rw [columnL2Restriction_norm_sq]
  simp

/-- For a nonnegative integer, the natural quotient of its natural value is the natural value of
its quotient. -/
theorem toNat_ediv_eq {x : ℤ} (hx : 0 ≤ x) (K : ℕ) : (x / K).toNat = x.toNat / K := by
  have h : ((x.toNat / K : ℕ) : ℤ) = x / K := by
    rw [Int.natCast_div, Int.toNat_of_nonneg hx]
  rw [← h, Int.toNat_natCast]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

/-- The block start of a depth below the root. -/
theorem blkStart_nat (K t : ℕ) :
    A.blkStart K (A.R.1 + t) = A.R.1 + ((K * (t / K) : ℕ) : ℤ) := by
  unfold blkStart
  simp only [add_sub_cancel_left]
  push_cast
  rfl

open Classical in
/-- A sum over a subset of the groups as a sum over the group set with indicators. -/
theorem sum_sub_eq_ite {g gset : Finset bf.Grp} (hg : g ⊆ gset) (f : bf.Grp → ℝ) :
    ∑ G ∈ g, f G = ∑ G : {G // G ∈ gset}, if G.1 ∈ g then f G.1 else 0 := by
  calc ∑ G ∈ g, f G = ∑ G ∈ gset, if G ∈ g then f G else 0 := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hg]
    _ = _ := (Finset.sum_coe_sort gset (fun G => if G ∈ g then f G else 0)).symm

namespace SideInput
variable (D : fp.SideInput)

theorem gs'_nat (l : Fin 4) (G : bf.Grp) (t : ℕ) :
    D.gs' l G (A.R.1 + t) = fp.sideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l)
      (D.Lf.layers l) D.S D.hA D.SP (D.c l G (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
      (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t) := by
  unfold gs'
  rw [blkStart_nat]

theorem toLeaf_sv_basic {l : Fin 4} (hl : D.u ≠ some l) (G : bf.Grp) (I : ℤ × ℤ) :
    D.toLeaf.sv l G I = columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (D.gs' l G I.1) := by
  change (if D.u = some l then _ else _) = _
  simp only [hl, ↓reduceIte]

theorem toLeaf_sv_U {l : Fin 4} (hl : D.u = some l) (G : bf.Grp) (I : ℤ × ℤ) :
    D.toLeaf.sv l G I = fp.ballFilt l (D.cat l) I G (D.Lf.role l)
      (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l) (bf.Ucol fp.Mc l I)) := by
  change (if D.u = some l then _ else _) = _
  simp only [hl, ↓reduceIte]

/-- The bound of the integrated side energies of a basic slot: the rolling part
`2 K (20 G₀ + 32) |R|` (`eq:variation`) and twice `K` times the linear-side energy `V_l |R|`
(`eq:linear-energy`). -/
noncomputable def sideB (cc : ℕ) (kk Vl : ℝ) : ℝ :=
  2 * (D.S.K * (20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2) + 32) * dyadicGridLength A.G A.R.1) +
  2 * (D.S.K * (Vl * dyadicGridLength A.G A.R.1))

/-- The energy bound of the block inputs of a basic slot at the block starts (eq:stack-energy,
lines 2393-2399 and 2415-2419): the rolling block inputs `2 (20 G₀ + 32) |R|` (bounded overlap of
the intervals `[u_b, b]`, `rolling_budget_blocks`) and twice the linear-side energy `V_l |R|`, each
`V_{l,G,b}` once; no factor `K`. -/
noncomputable def sideB0 (A' : ActiveSetup κ' c₀) (cc : ℕ) (kk Vl : ℝ) : ℝ :=
  2 * ((20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2) + 32) * dyadicGridLength A'.G A'.R.1) +
  2 * (Vl * dyadicGridLength A'.G A'.R.1)

/-- The linear-side energies of the block starts of a set of depths `K β`, `β < B_n`, are at most
those of all block starts below `B_n`. -/
theorem V_sum_le (qG : bf.Grp → ℕ) (l : Fin 4) (gset : Finset bf.Grp) (Bn : ℕ) (Sd : Finset ℕ)
    (hSd : ∀ t ∈ Sd, ∃ β < Bn, t = D.S.K * β) :
    ∑ b ∈ Sd, ∑ G : {G // G ∈ gset}, ‖(D.Ms l G.1).blockSide (D.S.withQ0 (qG G.1)) D.hA D.SP (A.R.1
        + (b : ℤ))
        (fp.retainedV G.1 (A.R.1 + (b : ℤ)) D.S.K) (D.c l G.1 (A.R.1 + (b : ℤ)))‖ ^ 2 ≤
      ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 := by
  have hK := D.hK
  set! f : ℕ → ℝ := fun b => ∑ G ∈ gset, ‖(D.Ms l G).blockSide (D.S.withQ0 (qG G)) D.hA D.SP (A.R.1
      + (b : ℤ))
    (fp.retainedV G (A.R.1 + (b : ℤ)) D.S.K) (D.c l G (A.R.1 + (b : ℤ)))‖ ^ 2 with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ = ∑ b ∈ Sd, f b := Finset.sum_congr rfl fun b _ => Finset.sum_coe_sort gset _
    _ ≤ ∑ b ∈ (Finset.range Bn).image (fun β => D.S.K * β), f b := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun b _ _ => hf0 b
        obtain ⟨β, hβ, rfl⟩ := hSd t ht
        exact Finset.mem_image.mpr ⟨β, Finset.mem_range.mpr hβ, rfl⟩
    _ = ∑ β ∈ Finset.range Bn, f (D.S.K * β) :=
        Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy
    _ = _ := by
        rw [hf]
        exact Finset.sum_comm

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint line 2159 for a basic `B` slot of the leaf data: the sides on the cells of all
groups have total square at most `sideB` (`sideState_budget` on the cells of each depth, which are
disjoint, `cell_budget_eq`; the rolling sides by `eq:variation` and the fixed `V_{l,G,b}` by the
linear-side bound `eq:linear-energy`). -/
theorem basic_side_energy (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) {l : Fin
    4}
    (hl : D.u ≠ some l) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (k Bn : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (hBn : ∀ I ∈ S, (D.toLeafQ qG).bk I < Bn)
    (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : ℝ}
    (hlin : ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ Vl * dyadicGridLength A.G A.R.1) :
    ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2 ≤ D.sideB cc kk Vl := by
  have hK := D.hK
  have hdep : ∀ I ∈ S, A.R.1 ≤ I.1 := fun I hI =>
    dyadicGridCell_depth_le_of_subset A.G I A.R (A.sub I (hS hI))
  set! Sd : Finset ℕ := S.image (fun I => (I.1 - A.R.1).toNat) with hSd_def
  set! Ec : {G // G ∈ gset} → ℕ → Finset (ℤ × ℤ) := fun G t =>
    S.filter fun I => I.1 = A.R.1 + t ∧ G.1 ∈ gs I with hEc_def
  have hbud := fp.sideState_budget l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc hne
    (ι := {G // G ∈ gset}) Subtype.val Subtype.val_injective k (D.Lf.role l) (B.hPH l)
    (D.Lf.layers l) D.S D.hA D.SP D.hK (fun G => D.Ms l G.1) (fun G => qG G.1) (fun G => D.c l G.1)
        Sd
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.le_sup (f := fun I => (I.1 - A.R.1).toNat) (hS hI))
    Ec (fun G t I hI => by
      obtain ⟨hIS, hIt, -⟩ := Finset.mem_filter.mp hI
      exact ⟨hS hIS, hIt⟩)
    (fun G t I hI => by
      obtain ⟨hIS, -, hG⟩ := Finset.mem_filter.mp hI
      exact hcertS I hIS G.1 hG) hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb (hLs l)
  have heq := cell_budget_eq A.G S (fun (G : {G // G ∈ gset}) h => (D.withQ0 (qG G.1)).gs' l G.1 h)
    (fun G I => G.1 ∈ gs I) Sd A.R.1 Ec (fun G t => rfl) (fun I hI => ⟨(I.1 - A.R.1).toNat,
      Finset.mem_image_of_mem _ hI, by have := hdep I hI; omega⟩)
  calc ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2
      = ∑ I ∈ S, ∑ G : {G // G ∈ gset}, (if G.1 ∈ gs I then
          ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
            ((D.withQ0 (qG G.1)).gs' l G.1 I.1)‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun I hI => ?_
        rw [sum_sub_eq_ite (hgs I hI)]
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [D.toLeafQ_sv, (D.withQ0 (qG G.1)).toLeaf_sv_basic hl]
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, ‖columnL2Restriction
          (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
          ((D.withQ0 (qG G.1)).gs' l G.1 (A.R.1 + t))‖ ^ 2 := by
        refine Eq.trans ?_ heq
        refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun G _ => ?_
        split_ifs <;> rfl
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, ‖columnL2Restriction
          (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
          (fp.sideState (D.Ms l G.1) l (D.cat l) (D.mbs l) G.1 (D.Lf.role l) (D.Lf.layers l)
              (D.S.withQ0 (qG G.1))
            D.hA D.SP (D.c l G.1 (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
            (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun G _ => ?_
        rw [(D.withQ0 (qG G.1)).gs'_nat]; rfl
    _ ≤ _ := hbud
    _ ≤ D.sideB cc kk Vl := by
        unfold sideB
        have hV := D.V_sum_le qG l gset Bn (Sd.image fun t => D.S.K * (t / D.S.K)) (fun t' ht' => by
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
          refine ⟨(I.1 - A.R.1).toNat / D.S.K, ?_, rfl⟩
          have h1 := hBn I hI
          change ((I.1 - A.R.1) / D.S.K).toNat < Bn at h1
          rwa [toNat_ediv_eq (by have := hdep I hI; omega)] at h1)
        gcongr
        exact hV.trans hlin

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lines 2393-2399 and 2415-2419 (eq:stack-energy) for the block inputs
`W_b = Z_b - Z_{u_b} + V_b` of a basic slot at the block starts `b = R + K β`, restricted to the
ancestors at depth `b` of the cells of the block `β` of each group: total square at most `sideB0`
(`sideState_budget_blocks` at the depths `K β`, where the side state is the block input), with no
factor `K`. -/
theorem block_energy (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) {l : Fin 4}
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (k Bn : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (hBn : ∀ I ∈ S, (D.toLeafQ qG).bk I < Bn)
    (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : ℝ}
    (hlin : ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ Vl * dyadicGridLength A.G A.R.1) :
    ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ (D.toLeafQ qG).bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + (((D.toLeafQ qG).K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1
            J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      ((D.toLeafQ qG).Wb l G (A.R.1 + (((D.toLeafQ qG).K * β : ℕ) : ℤ)))‖ ^ 2 ≤ sideB0 A cc kk Vl :=
          by
  have hK := D.hK
  have hdep : ∀ I ∈ S, A.R.1 ≤ I.1 := fun I hI =>
    dyadicGridCell_depth_le_of_subset A.G I A.R (A.sub I (hS hI))
  have hbkle : ∀ I ∈ S, D.S.K * (D.toLeafQ qG).bk I ≤ (I.1 - A.R.1).toNat := by
    intro I hI
    change D.S.K * ((I.1 - A.R.1) / D.S.K).toNat ≤ _
    rw [toNat_ediv_eq (by have := hdep I hI; omega)]
    exact Nat.mul_div_le _ _
  have hle : ∀ I ∈ S, A.R.1 + ((D.S.K * (D.toLeafQ qG).bk I : ℕ) : ℤ) ≤ I.1 := by
    intro I hI
    have h1 := hbkle I hI
    have h2 : (((I.1 - A.R.1).toNat : ℕ) : ℤ) = I.1 - A.R.1 :=
      Int.toNat_of_nonneg (by have := hdep I hI; omega)
    have h3 : ((D.S.K * (D.toLeafQ qG).bk I : ℕ) : ℤ) ≤ ((I.1 - A.R.1).toNat : ℤ) := by
      exact_mod_cast h1
    omega
  set! Sd : Finset ℕ := S.image (fun I => D.S.K * (D.toLeafQ qG).bk I) with hSd_def
  set! Ec : bf.Grp → ℕ → Finset (ℤ × ℤ) := fun G t =>
    (S.filter fun I => G ∈ gs I ∧ D.S.K * (D.toLeafQ qG).bk I = t).image
      (fun I => ancAt A.G I (A.R.1 + t)) with hEc_def
  have hEc : ∀ (G : {G // G ∈ gset}) t, ∀ J ∈ Ec G.1 t, J ∈ A.cells ∧ J.1 = A.R.1 + t := by
    intro G t J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, -, ht⟩ := Finset.mem_filter.mp hI
    have h1 := hle I hIS
    rw [ht] at h1
    exact ⟨hanc I (hS hIS) _ (subset_ancAt A.G I h1)
      (ancAt_subset (A.sub I (hS hIS)) (by omega)), rfl⟩
  have hcert : ∀ (G : {G // G ∈ gset}) t, ∀ J ∈ Ec G.1 t, fp.Cert k G.1 J := by
    intro G t J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hG, ht⟩ := Finset.mem_filter.mp hI
    have h1 := hle I hIS
    rw [ht] at h1
    exact (hcertS I hIS G.1 hG).mono fp (subset_ancAt A.G I h1)
  have hbud := fp.sideState_budget_blocks l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc
    hne (ι := {G // G ∈ gset}) Subtype.val Subtype.val_injective k (D.Lf.role l) (B.hPH l)
    (D.Lf.layers l) D.S D.hA D.SP D.hK (fun G => D.Ms l G.1) (fun G => qG G.1) (fun G => D.c l G.1)
        Sd
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact (hbkle I hI).trans (Finset.le_sup (f := fun I => (I.1 - A.R.1).toNat) (hS hI)))
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact Dvd.intro _ rfl)
    (fun G t => Ec G.1 t) hEc hcert hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb (hLs l)
  set! H : bf.Grp → ℕ → ℝ := fun G t => ‖columnL2Restriction
    (⋃ J ∈ Ec G t, dyadicGridCell A.G J.1 J.2)
    (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
    (fp.sideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l) (D.Lf.layers l) (D.S.withQ0
        (qG G))
      D.hA D.SP (D.c l G (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
      (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 with hH
  have hsub : S.image (D.toLeafQ qG).bk ⊆ Finset.range Bn := fun β hβ => by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hβ
    exact Finset.mem_range.mpr (hBn I hI)
  have hterm : ∀ G β, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ (D.toLeafQ qG).bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + (((D.toLeafQ qG).K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1
            J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      ((D.toLeafQ qG).Wb l G (A.R.1 + (((D.toLeafQ qG).K * β : ℕ) : ℤ)))‖ ^ 2 = H G (D.S.K * β) :=
          by
    intro G β
    have e1 : D.S.K * β / D.S.K = β := Nat.mul_div_cancel_left β (by omega)
    have e2 : (S.filter fun I => G ∈ gs I ∧ D.S.K * (D.toLeafQ qG).bk I = D.S.K * β) =
        S.filter fun I => G ∈ gs I ∧ (D.toLeafQ qG).bk I = β := by
      refine Finset.filter_congr fun I _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.eq_of_mul_eq_mul_left (by omega) h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]⟩
    simp only [hH, hEc_def, e1, e2]
    rfl
  calc _ = ∑ G ∈ gset, ∑ β ∈ S.image (D.toLeafQ qG).bk, H G (D.S.K * β) := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [← Finset.sum_subset hsub fun β _ hβ => ?_]
        · exact Finset.sum_congr rfl fun β _ => hterm G β
        · refine norm_sq_restrict_biUnion_empty A.G _ ?_ _
          rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
          rintro I hI ⟨-, hb⟩
          exact hβ (Finset.mem_image.mpr ⟨I, hI, hb⟩)
    _ = ∑ G ∈ gset, ∑ t ∈ Sd, H G t := by
        refine Finset.sum_congr rfl fun G _ => ?_
        have e : Sd = (S.image (D.toLeafQ qG).bk).image (fun β => D.S.K * β) := by
          rw [Finset.image_image]; rfl
        rw [e, Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy]
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, H G.1 t := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => (Finset.sum_coe_sort gset _).symm
    _ ≤ _ := hbud
    _ ≤ sideB0 A cc kk Vl := by
        unfold sideB0
        have hV := D.V_sum_le qG l gset Bn Sd (fun t ht => by
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
          exact ⟨(D.toLeafQ qG).bk I, hBn I hI, rfl⟩)
        gcongr
        exact hV.trans hlin

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint line 2159 for the basic `U` slot of the leaf data ("a basic `U` side is bounded by
current group Bessel and `eq:basic-side`"): on each cell the outputs of the certified groups have
total square at most twice the square of the basic side (`cell_bessel`). -/
theorem U_side_energy (qG : bf.Grp → ℕ) {l : Fin 4} (hl : D.u = some l)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (k : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) :
    ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2 ≤ 2 * ∑ I ∈ S, ‖bf.Ucol fp.Mc l I‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  have h := fp.cell_bessel l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) gset k
    (D.Lf.role l) (B.hPH l) (D.Lf.layers l) (hS hI) (gs I) (hgs I hI) (hcertS I hI) hroot' hτ'
    hτ1 hHed (B.hN l) (bf.Ucol fp.Mc l I) (bf.Ucol_mem_range fp.Mc (D.cat l) l I)
    (bf.restrict_Ucol fp.Mc l I)
  have hC : 1 + τ' * B.N * A.colBudget ^ 2 ≤ 2 := by linarith
  calc ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2
      = ∑ G ∈ gs I, ‖fp.ballFilt l (D.cat l) I G (D.Lf.role l)
          (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l)
            (bf.Ucol fp.Mc l I))‖ ^ 2 :=
        Finset.sum_congr rfl fun G _ => by rw [D.toLeafQ_sv, (D.withQ0 (qG G)).toLeaf_sv_U hl]; rfl
    _ ≤ _ := h
    _ ≤ 2 * ‖bf.Ucol fp.Mc l I‖ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)

/-- Blueprint lem:variation for the leaf data: the rolling outputs of every slot have variation
capacity `capV` over the certified cells (`varCap_basicOut`). -/
theorem toLeaf_cap (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) (gset : Finset
    bf.Grp) (k : ℕ)
    (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) (l : Fin 4) :
    A.VarCap gset ((D.toLeafQ qG).Z l) (fun G J => fp.Cert k G J) (capV A cc kk) := by
  intro ι _ r t hrt hdis htd Ec hEc
  exact fp.varCap_basicOut l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc hne gset k
    (D.Lf.role l) (B.hPH l) (D.Lf.layers l) hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb
    (hLs l) r t hrt hdis htd Ec hEc

/-- The integrated side budget of the leaf data: `2 B_U` for the basic `U` slot and `sideB` for
the basic `B` slots. -/
noncomputable def sideBs (cc : ℕ) (kk : ℝ) (Vl : Fin 4 → ℝ) (BU : ℝ) : ℝ :=
  ∑ l, if D.u = some l then 2 * BU else D.sideB cc kk (Vl l)

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lines 2446-2456, the side estimate of one localization leaf on the side states
(`eq:sides`): `leaf_side_estimateM` for the leaf data `toLeaf` of the side input, with the
variation capacities of the rolling outputs (`toLeaf_cap`, lem:variation), the energies of the
block inputs (`block_energy`) and of the sides (`basic_side_energy`, `U_side_energy`) derived from
`eq:variation`, the linear-side bound `eq:linear-energy` (`hlin`), current group Bessel and the
basic-side energy `B_U` (`eq:basic-side`); the joint side budget is `sideBs`. The outputs are the
cut family, the two-side bound, the three-side power bound on retained cells with bounded cores, and
the side cap on the retained paths. -/
theorem side_estimate (qG : bf.Grp → ℕ) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    (hne : A.cells.Nonempty)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : (D.toLeafQ qG).K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S
        ⊆
        A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, (D.toLeafQ qG).bk I < Bn)
    (hLp : ∀ l, ((D.toLeafQ qG).pe l).length ≤ Lp)
    (hJm : ∀ c d i i',
      ((D.toLeafQ qG).desc c d ((D.toLeafQ qG).tOf c i) ((D.toLeafQ qG).tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 < C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → (D.toLeafQ qG).u ≠ some c → (D.toLeafQ qG).u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, (D.toLeafQ qG).Val a b c d → ¬ (D.toLeafQ qG).Ucase c d
        →
      ∀ t ∈ (D.toLeafQ qG).pe c, ∀ t' ∈ (D.toLeafQ qG).pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => (D.toLeafQ qG).sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM (D.toLeafQ qG).cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G ((D.toLeafQ qG).Lf.role c) I t.2) (fp.slotFiltM G ((D.toLeafQ qG).Lf.role
              d) I t'.2))
        ((D.toLeafQ qG).sv a G I)‖ ≤ cF * (D.toLeafQ qG).ns a G I * (D.toLeafQ qG).ns b G I)
    (hbas : ∀ J ∈ A.cells, ∀ l, (D.toLeafQ qG).u ≠ some l →
      ‖bf.basicIn fp.Mc l J‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G J.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖(D.toLeafQ qG).out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, (((D.toLeafQ qG).pe d).length * ((D.toLeafQ qG).pe c).length : ℝ) ≤ Np)
    (G₀ : bf.Grp)
    {Cy : ℝ} (hy : ∀ I ∈ S, ∀ l, (D.toLeafQ qG).u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {BU : ℝ} (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (B : (D.toLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * ((D.toLeafQ qG).mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hJc : (Jm : ℝ) ≤ cc * (Real.log kk + 1))
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : Fin 4 → ℝ}
    (hlin : ∀ l, D.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).blockSide
        (D.S.withQ0 (qG G))
        D.hA D.SP (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ))
          D.S.K) (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤
        Vl l * dyadicGridLength A.G A.R.1)
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, (D.toLeafQ qG).u ≠ some a → fp.stackEA (SideLeafM.nOs Lp Jm) ((D.toLeafQ qG).cat a)
        ((D.toLeafQ qG).mbs a) (D.toLeafQ qG).Dpre N (capV A cc kk)
      (sideB0 A cc kk (Vl a)) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, (D.toLeafQ qG).u ≠ some b → (SideLeafM.nOs Lp Jm).card * (N * capV A cc kk +
        sideB0 A cc
        kk (Vl b)) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (SideLeafM.nOs Lp Jm).card * (2 * BU) ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then (D.toLeafQ qG).out l G I else
              (D.toLeafQ qG).sv l G
              I)‖ ≤
      6 * 256 * Np * (τ + cF) * (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU
          (capV A cc
          kk) ρ *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          (D.toLeafQ qG).nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * ((D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk)
            ρ ^
            (p / 2) *
          (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
          (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      (∀ (core err : ℤ × ℤ → bf.Grp → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
        (S' : Finset (ℤ × ℤ)), S' ⊆ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∀ {Bc : ℝ}, 0 ≤ Bc →
        (∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
          ‖core I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength A.G I.1)) →
        ∑ I ∈ S', dyadicGridLength A.G I.1 * min η (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
            ‖∑ G ∈ gs I, fp.Λc I (patternPiece (core I G) (fun l => (D.toLeafQ qG).sv l G I) (err I
                G)
                σ)‖) ≤
        η ^ (1 - p) * (81 * localFormUniformConstant κ' *
          max Bc (Real.sqrt ((D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A
              cc kk)
              ρ))) ^ p *
          ((D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
            (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2)
                *
            (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2)
                *
            dyadicGridLength A.G A.R.1)) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, (D.toLeafQ qG).s2 G I ≤
        (D.toLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ := by
  have hK := D.hK
  have hUle : ∀ l, ∑ I ∈ S, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU := fun l =>
    (Finset.sum_le_sum fun I _ => Finset.single_le_sum (f := fun l' => ‖bf.Ucol fp.Mc l' I‖ ^ 2)
      (fun l' _ => sq_nonneg _) (Finset.mem_univ l)).trans hBU
  have hEU : ∀ l, (D.toLeafQ qG).u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) ((D.toLeafQ qG).sv l G I)‖ ^ 2 ≤ 2 * BU := by
    intro l hl
    refine le_trans (Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun G _ =>
      columnL2Restriction_norm_sq_le _ _ _) ?_
    refine (D.U_side_energy qG hl S hS gs gset hgs k hcertS B hroot' hτ' hτ1 hHed hτN).trans ?_
    linarith [hUle l]
  have hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.toLeafQ qG).sv l G I‖ ^ 2 ≤ D.sideBs cc kk Vl BU := by
    calc ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.toLeafQ qG).sv l G I‖ ^ 2
        = ∑ I ∈ S, ∑ l, ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2 :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ l, ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.toLeafQ qG).sv l G I‖ ^ 2 := Finset.sum_comm
      _ ≤ D.sideBs cc kk Vl BU := by
          unfold sideBs
          refine Finset.sum_le_sum fun l _ => ?_
          split_ifs with hl
          · refine (D.U_side_energy qG hl S hS gs gset hgs k hcertS B hroot' hτ' hτ1 hHed
              hτN).trans ?_
            linarith [hUle l]
          · exact D.basic_side_energy qG hanc hne hl S hS gs gset hgs k Bn hcertS hBn B hroot' hτ'
              hτ1 hHed hτN cc hc hk hDm hDb hLs (hlin l hl)
  exact (D.toLeafQ qG).leaf_side_estimateM hq2 hq3 hanc hne hKNd hKN S hS hroot gs gset hgs Lp Jm
      Bn k
    hBn hLp hJm Act hact hMp hcertS (fun _ G J => fp.Cert k G J) (fun _ => capV A cc kk)
    (fun l => sideB0 A cc kk (Vl l))
    (fun l _ => D.toLeaf_cap qG hanc hne gset k B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hLs l)
    (fun l _ I hI G hG J _ hIJ => (hcertS I hI G hG).mono fp hIJ)
    (fun l hl => D.block_energy qG hanc hne S hS gs gset k Bn hcertS hBn B hroot' hτ' hτ1 hHed hτN
      cc hc hk hDm hDb hLs (hlin l hl)) (EU := 2 * BU) hEU hτ hcF hC₀ hB₀ hpair hfar hbas hout
    hNp (Bs := D.sideBs cc kk Vl BU) hBs G₀ hy hBU B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hJc
    hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The far bound of the side-state leaf data (blueprint lines 2252-2258) -/

/-- A bound valid with every positive enlargement of the two sizes holds for the sizes. -/
theorem le_of_forall_pos_mul_le {X K a b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → X ≤ K * ((2 * a + ε) * (b + ε))) : X ≤ K * (2 * a * b) := by
  have hc : Continuous fun ε : ℝ => K * ((2 * a + ε) * (b + ε)) := by fun_prop
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)
  simpa using this

/-- The normalized `L²` size of the physical part on a cell is at most the normalized size. -/
theorem eLpNorm_augPhys_le_ns {V : Type*} [Fintype V] (Gd : RealDyadicGrid) (I : ℤ × ℤ)
    (x : ColumnL2 V) :
    eLpNorm (augPhys x) 2 (normalizedIntervalMeasure (dyadicGridLeft Gd I.1 I.2)
      (dyadicGridLength Gd I.1)) ≤ ENNReal.ofReal (‖x‖ / Real.sqrt (dyadicGridLength Gd I.1)) := by
  refine (eLpNorm_augPhys_cell_le Gd I x).trans (ENNReal.ofReal_le_ofReal ?_)
  have hr := dyadicGridLength_pos Gd I.1
  have h1 : (∫ y in dyadicGridCell Gd I.1 I.2, ‖(x : ℝ → ColumnHilbert V) y none‖ ^ 2) ≤
      ‖x‖ ^ 2 := by
    rw [columnInput_norm_sq_integral]
    calc (∫ y in dyadicGridCell Gd I.1 I.2, ‖(x : ℝ → ColumnHilbert V) y none‖ ^ 2)
        ≤ ∫ y in dyadicGridCell Gd I.1 I.2, ‖(x : ℝ → ColumnHilbert V) y‖ ^ 2 := by
          refine integral_mono
            ((memLp_column_coord x none).integrable_norm_pow two_ne_zero).restrict
            ((Lp.memLp x).integrable_norm_pow two_ne_zero).restrict fun y => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le _ none) 2
      _ ≤ ∫ y, ‖(x : ℝ → ColumnHilbert V) y‖ ^ 2 :=
          setIntegral_le_integral ((Lp.memLp x).integrable_norm_pow two_ne_zero)
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have h2 : ‖x‖ / Real.sqrt (dyadicGridLength Gd I.1) =
      Real.sqrt (‖x‖ ^ 2 / dyadicGridLength Gd I.1) := by
    rw [Real.sqrt_div' _ hr.le, Real.sqrt_sq (norm_nonneg _)]
  rw [h2]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h1 hr.le)

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

open Classical in
/-- Blueprint lines 2252-2258 on leaf data at a leaf of the guarded search (`leaf_far_search`):
when the catalogs pass all residual tests of the basic inputs and all helper tests whose bases are
the cell sides (the instantiated helper catalog, lines 2167-2169), the far band defects of the
transfer steps of every valid pattern of an actual use have absolute value at most
`c_F n_a n_b` with `c_F = (2 fuel + 2) (P + 1)² 16 τ₃ S_z²` and the normalized side sizes `n`. -/
theorem far_bound {fuel : ℕ} {up₀ : Fin 4} {s : ℕ} (hLf : T.Lf = leafAt fuel fp.Lc up₀ s)
    (hmH : 2 * fuel + 2 ≤ fp.mH)
    (hT : ∀ l, ∀ e ∈ T.cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ l, ∀ e ∈ T.cat l, bf.occAvail e.tag.2.1 e.tag.1)
    (S : Finset (ℤ × ℤ)) (gs : ℤ × ℤ → Finset bf.Grp)
    (huse : ∀ I ∈ S, ∀ G ∈ gs I, fp.ActualUse G I) {τ : ℕ → ℝ}
    (hpass : ∀ I ∈ S, ∀ l, T.u ≠ some l → ∀ w : fp.TestName I Unit, fp.MainRk w →
      (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc
        bf.vtag (A.w I) (τ (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).r) fp.mH (T.cat l))
    {τH : ℝ} (hτH : 0 ≤ τH) {Bh : Type} (gE : ℤ × ℤ → Bh → bf.Grp)
    (hgE : ∀ I ∈ S, ∀ G ∈ gs I, ∃ i, gE I i = G)
    (hhpass : ∀ I ∈ S, ∀ a, ∀ w : fp.HelperName I Bh,
      (fp.helperOf a I (fun i => T.sv a (gE I i) I) w).Pass A.G (bf.origCols a) I A.csrc A.Hsrc
        bf.vtag (A.w I) τH fp.mH (T.cat a))
    {τ₃ Sz : ℝ} (hτ0 : ∀ R, 0 ≤ τ R) (n : ℕ → ℝ) (hn : Monotone n)
    (hn0 : 2 * A.colBudget ≤ n 0)
    (hτ : ∀ R, 1 ≤ R → R ≤ fp.Lc + 4 → τ R * (A.colBudget * Real.sqrt (n (R - 1))) ≤ τ₃)
    (hτH' : τH * (A.colBudget * Real.sqrt (n (fp.Lc + 4))) ≤ τ₃) (hSz : 0 < Sz)
    (hSzl : ∀ I ∈ S, ∀ l, ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz)
    (d₀ : bf.Vtx) {NH : ℝ}
    (hNl : ∀ I ∈ S, ∀ l, ∀ r ≤ fp.Lc + 4, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols l) (T.cat l) I r M d₀).card : ℝ) ≤ n r)
    (hNH : ∀ I ∈ S, ∀ a, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols a) (T.cat a) I (fp.Lc + 5) M d₀).card : ℝ) ≤ NH)
    {τ₂ : ℝ} (hτ₂ : 0 < τ₂) (hτ₂1 : τ₂ ≤ 1)
    (hτ₂' : τ₂ * (A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt NH)) ≤ τ₃)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed) :
    ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, T.Val a b c d → ¬ T.Ucase c d →
      ∀ t ∈ T.pe c, ∀ t' ∈ T.pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => T.sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G (T.Lf.role c) I t.2) (fp.slotFiltM G (T.Lf.role d) I t'.2))
        (T.sv a G I)‖ ≤
        (2 * fuel + 2) * ((fp.P + 1) ^ 2 * (16 * τ₃ * Sz ^ 2)) * T.ns a G I * T.ns b G I := by
  intro I hI G hG a b c d hV hU t ht t' ht'
  obtain ⟨hab, hac, had, hbc, hbd, hcd, -⟩ := hV
  have hUc : T.u ≠ some c := fun h => hU (Or.inl h)
  have hUd : T.u ≠ some d := fun h => hU (Or.inr h)
  obtain ⟨hIc, v₀, hv₀, hs₀, hgrp⟩ := huse I hI G hG
  obtain ⟨i₀, hi₀⟩ := hgE I hI G hG
  subst hgrp
  have hcb0 : 0 ≤ A.colBudget := by have := A.two_le_colBudget; linarith
  have hτ3 : 0 ≤ τ₃ := le_trans (mul_nonneg (hτ0 1) (by positivity)) (hτ 1 le_rfl (by omega))
  unfold pe at ht ht'
  rw [hLf] at ht ht' ⊢
  have hlen : ∀ l, ∀ u ∈ posExpand ((leafAt fuel fp.Lc up₀ s).layers l).reverse,
      u.2.length ≤ fuel := by
    intro l u hu
    have h1 := posExpand_mem_length _ u hu
    rw [List.length_reverse] at h1
    exact h1.trans (leafAt_layers_length_le fuel fp.Lc up₀ s l)
  set G := fp.K.grp bf.admT A.famVtxBound (bf.admAt I) v₀ with hG_def
  have hst : ((fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
      (fp.slotFiltM G ((leafAt fuel fp.Lc up₀ s).role c) I t.2)
      (fp.slotFiltM G ((leafAt fuel fp.Lc up₀ s).role d) I t'.2)).length : ℝ) ≤
      2 * fuel + 2 := by
    rw [fp.mergeStepsM_length]
    unfold slotFiltM
    simp only [List.length_cons, List.length_map]
    have h1' : (t.2.length : ℝ) ≤ fuel := by exact_mod_cast hlen c t ht
    have h2' : (t'.2.length : ℝ) ≤ fuel := by exact_mod_cast hlen d t' ht'
    push_cast
    linarith
  have hna := T.ns_nonneg a G I
  have hnb := T.ns_nonneg b G I
  have key := le_of_forall_pos_mul_le (X := ‖chainDefectSel (fp.Λc I) fp.P a c d
      (fun l => T.sv l G I) (bf.basicIn fp.Mc c I) (bf.basicIn fp.Mc d I)
      (fun p q => q + 2 < p ∨ p + 2 < q)
      (fp.mergeStepsM T.cat a c d (fp.Lc + 5) I
        (fp.slotFiltM G ((leafAt fuel fp.Lc up₀ s).role c) I t.2)
        (fp.slotFiltM G ((leafAt fuel fp.Lc up₀ s).role d) I t'.2))
      (T.sv a G I)‖)
    (K := (2 * fuel + 2) * ((fp.P + 1) ^ 2 * (8 * τ₃ * Sz ^ 2)))
    (a := T.ns a G I) (b := T.ns b G I) fun ε hε => by
      have h := fp.leaf_far_search T.cat hT htag hIc (Ne.symm hac) hcd (Ne.symm hbc)
        (Ne.symm had) (Ne.symm hbd) hab
        (fun l hl => hpass I hI l (by rcases hl with rfl | rfl <;> assumption)) (Bh := Bh)
        (fun i => T.sv a (gE I i) I) i₀ hτH
        (hhpass I hI a) (fun l => T.sv l G I) (by show T.sv a G I = T.sv a (gE I i₀) I; rw [hi₀])
        hv₀ hs₀ s hmH ht ht' hτ0 n hn hn0 hτ hτH' hSz
        (hSzl I hI) d₀ (hNl I hI) (hNH I hI a) hτ₂ hτ₂1 hτ₂' hHed
        (Sa := 2 * T.ns a G I + ε) (by positivity)
        (by unfold ns; rw [mul_div_assoc]; linarith)
        (Sb := T.ns b G I + ε) (by positivity)
        ((eLpNorm_augPhys_le_ns A.G I _).trans
          (ENNReal.ofReal_le_ofReal (by unfold ns; linarith)))
      refine h.trans ?_
      have hQ : 0 ≤ ((fp.P : ℝ) + 1) ^ 2 * (8 * τ₃ * Sz ^ 2 * (2 * T.ns a G I + ε) *
          (T.ns b G I + ε)) := by positivity
      calc _ ≤ (2 * fuel + 2 : ℝ) * (((fp.P : ℝ) + 1) ^ 2 * (8 * τ₃ * Sz ^ 2 *
            (2 * T.ns a G I + ε) * (T.ns b G I + ε))) := mul_le_mul_of_nonneg_right hst hQ
        _ = _ := by ring
  calc _ ≤ _ := key
    _ = _ := by ring

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

/-! ## The sizes of the leaf inputs (blueprint prop:base, lines 1607-1616) -/

namespace ActiveSetup.BasicFamilies
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} (bf : A.BasicFamilies)

/-- On a normalized root (`‖1_U F_{l,j}‖² ≤ C_F |U|` on the active cells) the basic inputs have
normalized size at most `2 √C_F` (blueprint prop:base, "their normalized `L²` sizes are
bounded"). -/
theorem norm_basicIn_le (Mc : ℕ) (l : Fin 4) {I : ℤ × ℤ} (hI : I ∈ A.cells) {CF : ℝ}
    (hCF : 0 ≤ CF)
    (hnorm : ∀ jb : Fin 2, ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (bf.P l jb).Z‖ ^ 2 ≤
        CF * dyadicGridLength A.G I.1) :
    ‖bf.basicIn Mc l I‖ ≤ 2 * Real.sqrt CF * Real.sqrt (dyadicGridLength A.G I.1) := by
  have hfam : ∀ jb : Fin 2, ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (bf.P l jb).Z‖ ≤
        Real.sqrt CF * Real.sqrt (dyadicGridLength A.G I.1) := fun jb => by
    rw [← Real.sqrt_mul hCF]
    exact Real.le_sqrt_of_sq_le (hnorm jb)
  rw [bf.basicIn_eq Mc l hI]
  refine (norm_sub_le _ _).trans ?_
  have h0 := bf.norm_basicCell_le l 0 hI
  have h1 := bf.norm_basicCell_le l 1 hI
  rw [ActiveSetup.BasicFamilies.famEmb, norm_colRelabel (bf.famEmb_injective Mc l 0),
    ActiveSetup.BasicFamilies.famEmb, norm_colRelabel (bf.famEmb_injective Mc l 1)]
  linarith [hfam 0, hfam 1]

/-- The basic family inputs are normalized on every cell of the setup (blueprint prop:base, "their
normalized `L²` sizes are bounded"): `‖1_U F_{l,j}‖² ≤ |U|` (the `hnormF` input with `C_F = 1`). -/
theorem normF (l : Fin 4) (jb : Fin 2) {U : ℤ × ℤ} (hU : U ∈ A.cells) :
    ‖columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
      (bf.P l jb).Z‖ ^ 2 ≤ 1 * dyadicGridLength A.G U.1 := by
  rw [columnL2Restriction_norm_sq]
  exact bf.energy l jb U hU

/-- The squared norm of a basic side is its length times its normalized square size. -/
theorem norm_sq_Ucol_le (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) :
    ‖bf.Ucol Mc l I‖ ^ 2 ≤
      dyadicGridLength A.G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 := by
  unfold Ucol
  by_cases h : l = A.a ∨ l = A.b
  · simp only [h, ↓reduceIte]
    rw [norm_sq_physicalColumnInput_cellLp (A.U_L2 l I), A.U_cell_energy]
  · simp only [h, ↓reduceIte]
    rw [norm_sq_physicalColumnInput_cellLp (f := 0) MemLp.zero]
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, integral_zero]
    exact mul_nonneg (dyadicGridLength_pos A.G I.1).le (sq_nonneg _)

/-- The basic sides have normalized size at most `S`. -/
theorem norm_Ucol_le (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) :
    ‖bf.Ucol Mc l I‖ ≤ A.S * Real.sqrt (dyadicGridLength A.G I.1) := by
  have hr := dyadicGridLength_pos A.G I.1
  have he := A.U_le l I
  have hS : 0 ≤ A.S := le_trans ENNReal.toReal_nonneg he
  have h1 := bf.norm_sq_Ucol_le Mc l I
  have h2 : dyadicGridLength A.G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
      (A.S * Real.sqrt (dyadicGridLength A.G I.1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr.le, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ENNReal.toReal_nonneg he 2) hr.le
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h1.trans h2)

open Classical in
/-- Blueprint `eq:basic-side` for the basic sides of the four slots on a set of active cells:
total square at most `4 E |R|`. -/
theorem Ucol_energy {η₀ E : ℝ} (h : A.SubRootProps η₀ E) (Mc : ℕ) (S : Finset (ℤ × ℤ))
    (hS : S ⊆ A.cells) :
    ∑ I ∈ S, ∑ l, ‖bf.Ucol Mc l I‖ ^ 2 ≤ 4 * E * dyadicGridLength A.G A.R.1 := by
  rw [Finset.sum_comm]
  have hl : ∀ l, ∑ I ∈ S, ‖bf.Ucol Mc l I‖ ^ 2 ≤ E * dyadicGridLength A.G A.R.1 := by
    intro l
    refine le_trans (Finset.sum_le_sum fun I _ => bf.norm_sq_Ucol_le Mc l I) ?_
    refine le_trans ?_ ((h A.R subset_rfl).1 l)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun I hI => ?_) fun I _ _ =>
      mul_nonneg (dyadicGridLength_pos A.G I.1).le (sq_nonneg _)
    exact Finset.mem_filter.mpr ⟨hS hI, A.sub I (hS hI)⟩
  calc ∑ l, ∑ I ∈ S, ‖bf.Ucol Mc l I‖ ^ 2 ≤ ∑ _l : Fin 4, E * dyadicGridLength A.G A.R.1 :=
        Finset.sum_le_sum fun l _ => hl l
    _ = 4 * E * dyadicGridLength A.G A.R.1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideLeafM
variable (T : fp.SideLeafM)

/-- The whole leaf outputs are at most the slot inputs (contractions). -/
theorem norm_out_le (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) : ‖T.out l G I‖ ≤ ‖T.xin l I‖ :=
  (fp.norm_ballFilt_apply_le l (T.cat l) I G (T.Lf.role l) _).trans
    (norm_layerOp_apply_le _ (fun m y => (fp.norm_cumFilt_apply_le l (T.cat l) I m y).1)
      (fun m y => (fp.norm_cumFilt_apply_le l (T.cat l) I m y).2) _ _)

end SideLeafM

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}

/-- The far constant `c_F = (2 fuel + 2) (P + 1)² 16 τ₃ S_z²` of `far_bound`. -/
noncomputable def farC (fp : bf.FamParams) (fuel : ℕ) (τ₃ Sz : ℝ) : ℝ :=
  (2 * fuel + 2) * ((fp.P + 1) ^ 2 * (16 * τ₃ * Sz ^ 2))

variable {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The joint path cap of the side estimate on the side states: `T_c` of `Tcap` with the basic
sizes `2 √C_F` (normalized root), the output and side sizes `max(2 √C_F, S)` and the basic-side
energy `4 E |R|` (`eq:basic-side`). -/
noncomputable def Tside (qG : bf.Grp → ℕ) (Lp Jm : ℕ) (CF E : ℝ) (cc : ℕ) (kk : ℝ) (Vl : Fin 4 → ℝ)
    (ρ : ℝ) : ℝ :=
  (D.toLeafQ qG).Tcap Lp Jm (2 * Real.sqrt CF) (max (2 * Real.sqrt CF) A.S)
    (max (2 * Real.sqrt CF) A.S) (D.sideBs cc kk Vl (4 * E * dyadicGridLength A.G A.R.1))
    (4 * E * dyadicGridLength A.G A.R.1) (capV A cc kk) ρ

open Classical in
/-- Blueprint lines 2446-2456, the unconditional side estimate of one localization leaf of the
guarded search on its side states. The input consists of the finite base data (pair smallness of
the full arguments `hpair`, the normalized root `hnormF` and the basic-side energy `hsub`,
prop:base), the fixed localization leaf (`hLf`, with its actual uses, certificates and counts),
the linear-side bound (`hlin`, prop:linear-side) and the instantiated helper catalog (all residual
tests of the basic inputs `hpass` and all helper tests on the cell sides `hhpass` pass). The
outputs, on one cut family of root fraction at most `2ρ`, are:
* the two-side bound: the pair-small and far absolute bound (`far_bound`), six times the critical
  near-band bounds (`eq:near-band`) and the power cost of the three strong factors (with the
  freeze and restoration terms and the frozen complements);
* the power bound of the patterns with at least three sides on retained cells with bounded cores;
* the side cap `eq:side-cap` on the retained paths, with the joint path cap `Tside`. -/
theorem side_estimate_leaf (qG : bf.Grp → ℕ) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3)
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
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I
            (fun l => if σ l = 0 then (D.toLeafQ qG).out l G I else (D.toLeafQ qG).sv l G I)‖ ≤
      6 * 256 * Np * (τ + fp.farC fuel τ₃ Sz) * D.Tside qG Lp Jm CF E cc kk Vl ρ *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          (D.toLeafQ qG).nearBnd hq2 hq3 Nd N Lp Jm Mp (2 * Real.sqrt CF) (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * (D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
          D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      (∀ (core err : ℤ × ℤ → bf.Grp → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
        (S' : Finset (ℤ × ℤ)), S' ⊆ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∀ {Bc : ℝ}, 0 ≤ Bc →
        (∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
          ‖core I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength A.G I.1)) →
        ∑ I ∈ S', dyadicGridLength A.G I.1 * min η (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
            ‖∑ G ∈ gs I, fp.Λc I
              (patternPiece (core I G) (fun l => (D.toLeafQ qG).sv l G I) (err I G) σ)‖) ≤
        η ^ (1 - p) * (81 * localFormUniformConstant κ' *
          max Bc (Real.sqrt (D.Tside qG Lp Jm CF E cc kk Vl ρ))) ^ p *
          (D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) *
            D.Tside qG Lp Jm CF E cc kk Vl ρ ^ (p / 2) * dyadicGridLength A.G A.R.1)) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, (D.toLeafQ qG).s2 G I ≤
        D.Tside qG Lp Jm CF E cc kk Vl ρ := by
  have hcb0 : 0 ≤ A.colBudget := by have := A.two_le_colBudget; linarith
  have hτ3 : 0 ≤ τ₃ := le_trans (mul_nonneg (hτ0 1) (by positivity)) (hτr 1 le_rfl (by omega))
  have hsq : 0 < Real.sqrt CF := Real.sqrt_pos.mpr hCF
  have hSz0 : 0 < Sz := by linarith
  have hS0 : 0 ≤ A.S := le_trans ENNReal.toReal_nonneg (A.U_le 0 A.R)
  have hbasic : ∀ J ∈ A.cells, ∀ l, ‖bf.basicIn fp.Mc l J‖ ≤
      2 * Real.sqrt CF * Real.sqrt (dyadicGridLength A.G J.1) := fun J hJ l =>
    bf.norm_basicIn_le fp.Mc l hJ hCF.le fun jb => hnormF l jb J hJ
  have hnorm' : ∀ I ∈ S, ∀ l, ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤
      2 * Real.sqrt CF := fun I hI l => by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (dyadicGridLength_pos A.G I.1))]
    exact hbasic I (hS hI) l
  have hU' : ∀ I l, ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ A.S :=
    fun I l => by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (dyadicGridLength_pos A.G I.1))]
      exact bf.norm_Ucol_le fp.Mc l I
  have hfar := (D.toLeafQ qG).far_bound hLf hmH B.hT B.htag S gs huse hpass hτH gE hgE hhpass
    hτ0 n hn hn0
    hτr hτH' hSz0 (fun I hI l => (hnorm' I hI l).trans hSz) d₀ hNl hNH hτ₂ hτ₂1 hτ₂' hHed₂
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
  exact D.side_estimate qG hq2 hq3 hanc hne hKNd hKN S hS hroot gs gset hgs Lp Jm Bn k hBn hLp hJm
    Act hact hMp hcertS (cF := fp.farC fuel τ₃ Sz) (C₀ := 2 * Real.sqrt CF)
    (B₀ := max (2 * Real.sqrt CF) A.S) hτ (by unfold farC; positivity) (by positivity)
    (le_max_of_le_left (by positivity)) hpair hfar (fun J hJ l _ => hbasic J hJ l) hout hNp G₀
    (Cy := max (2 * Real.sqrt CF) A.S)
    (fun I hI l _ => ⟨(hnorm' I hI l).trans (le_max_left _ _), (hU' I l).trans (le_max_right _ _)⟩)
    (BU := 4 * E * dyadicGridLength A.G A.R.1) (bf.Ucol_energy hsub fp.Mc S hS) B hroot' hτ'
    hτ1 hHed hτN cc hc hk hDm hDb hJc hLs hlin hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ}

/-- The restriction of an active setup to a sub-root `R'` and a subfamily `C` of its cells below
`R'` (blueprint line 2451, "every hypothesis is available anew on a normalized subroot", and
prop:normalized, lines 2840-2842: restarts act on the original base summands with unchanged basic
arguments and inherited lists). -/
def restrictTo (A : ActiveSetup κ c₀) (R' : ℤ × ℤ) (C : Finset (ℤ × ℤ))
    (hC : ∀ I ∈ C, I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2) :
    ActiveSetup κ c₀ where
  G := A.G
  R := R'
  cells := C
  sub := fun I hI => (hC I hI).2
  w := A.w
  adm := fun I hI => A.adm I (hC I hI).1
  L := A.L
  fin := A.fin
  φ := A.φ
  φ_meas := A.φ_meas
  φ_bound := A.φ_bound
  H := A.H
  coef := A.coef
  path_chart := fun y v => by
    obtain ⟨d, B, h1, h2, h3⟩ := A.path_chart y v
    exact ⟨d, B, h1, h2, fun I hI => h3 I (hC I hI).1⟩
  nested_chart := fun I hI => A.nested_chart I (hC I hI).1
  nested_cons := fun I hI I' hI' => A.nested_cons I (hC I hI).1 I' (hC I' hI').1
  Dc := A.Dc
  Dc_nonneg := A.Dc_nonneg
  coef_le := A.coef_le
  a := A.a
  b := A.b
  hab := A.hab
  U := A.U
  U_meas := A.U_meas
  S := A.S
  U_L2 := A.U_L2
  U_le := A.U_le
  η := A.η
  small := fun I hI => A.small I (hC I hI).1

variable (A : ActiveSetup κ c₀) (R' : ℤ × ℤ) (C : Finset (ℤ × ℤ))
  (hC : ∀ I ∈ C, I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2)

end ActiveSetup

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

open Classical in
/-- The restriction of an active setup to all of its cells below a sub-root `R'`. -/
noncomputable def below (R' : ℤ × ℤ) : ActiveSetup κ c₀ :=
  A.restrictTo R' (A.cells.filter fun I =>
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2)
    (fun _ hI => Finset.mem_filter.mp hI)

variable (R' : ℤ × ℤ)

open Classical in
@[simp] theorem below_cells : (A.below R').cells = A.cells.filter fun I =>
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2 := rfl

@[simp] theorem below_R : (A.below R').R = R' := rfl

end ActiveSetup

end TrilinearHT.Auto

end
