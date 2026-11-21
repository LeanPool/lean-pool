/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Top
public import Mathlib.Data.List.GetD

/-!
# The input `sepInput` of the specification

`PlanarSeparator.sepInput R w di` (in `PlanarSeparator/Spec.lean`) lists a rotation system of a
graph on `Fin n` with a numbering `di` of its darts. When the numbering puts the darts leaving
lower vertices first, the list is an encoding in the sense of `Enc` and `InHolds` (`enc_sepInput`,
`inHolds_sepInput`), so the separator program prints a separation on it
(`separatorMachine_holds`, the target `SeparatorMachine`).
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt

theorem getD_flatMap3 {α : Type*} (l : List α) (f : α → List ℕ) (hf : ∀ a, (f a).length = 3)
    (i r : ℕ) (hi : i < l.length) (hr : r < 3) :
    (l.flatMap f).getD (3 * i + r) 0 = (f l[i]).getD r 0 := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rw [List.getD_append _ _ _ _ (by rw [hf]; omega)]; simp
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
        show 3 * (i + 1) + r - 3 = 3 * i + r by omega, ih i (by simp at hi; omega)]
      simp

variable {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  (R : Kasteleyn.RotationSystem G) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m)

/-- The offsets of the darts of the vertices. -/
def ofsI (v : ℕ) : ℕ := #{d : G.Dart | (d.fst : ℕ) < v}
/-- The weights, numerically. -/
def wI (v : ℕ) : ℕ := if h : v < n then w ⟨v, h⟩ else 0
/-- The initial vertices of the darts, numerically. -/
def tlI (i : ℕ) : ℕ := if h : i < m then ((di.symm ⟨i, h⟩).fst : ℕ) else 0
/-- The reversals, numerically. -/
def rvI (i : ℕ) : ℕ := if h : i < m then (di (di.symm ⟨i, h⟩).symm : ℕ) else 0
/-- The rotation, numerically. -/
def roI (i : ℕ) : ℕ := if h : i < m then (di (R.rot (di.symm ⟨i, h⟩)) : ℕ) else 0

theorem enc_sepInput (hdi : ∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') :
    Enc R w n m (Equiv.refl _) di (ofsI (G := G)) (wI w) (tlI di) (rvI di) (roI R di) where
  tl_eq d := by simp [tlI]
  rv_eq d := by simp [rvI]
  ro_eq d := by simp [roI]
  w_eq v := by simp [wI]
  ofs_mono u v huv _ := card_le_card fun d hd => by
    simp only [mem_filter, mem_univ, true_and] at hd ⊢; omega
  ofs_n := by
    rw [ofsI, filter_true_of_mem fun d _ => d.fst.2, card_univ, Fintype.card_congr di,
      Fintype.card_fin]
  blk d := by
    simp only [Equiv.refl_apply, ofsI]
    constructor
    · -- the darts of lower vertices come before `d`
      have : ((univ : Finset G.Dart).filter fun d' => (d'.fst : ℕ) < d.fst).map
          (di.toEmbedding.trans (Fin.valEmbedding)) ⊆ range (di d) := by
        intro x hx
        obtain ⟨d', hd', rfl⟩ := mem_map.1 hx
        simp only [mem_filter, mem_univ, true_and] at hd'
        simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply,
          mem_range]
        exact hdi d' d (Fin.lt_def.2 hd')
      have := card_le_card this
      simpa using this
    · -- the darts up to `d` leave vertices up to that of `d`
      have : range (di d + 1) ⊆ ((univ : Finset G.Dart).filter fun d' =>
          (d'.fst : ℕ) < d.fst + 1).map (di.toEmbedding.trans (Fin.valEmbedding)) := by
        intro x hx
        have hx' : x < m := lt_of_lt_of_le (mem_range.1 hx) (di d).2
        refine mem_map.2 ⟨di.symm ⟨x, hx'⟩, ?_, by simp⟩
        simp only [mem_filter, mem_univ, true_and]
        by_contra h
        have := hdi d (di.symm ⟨x, hx'⟩) (Fin.lt_def.2 (by omega))
        simp only [Equiv.apply_symm_apply, Fin.lt_def] at this
        have := mem_range.1 hx
        omega
      have := card_le_card this
      simp only [card_range, card_map] at this
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_of_le_of_eq this (by congr))

theorem inHolds_sepInput :
    InHolds (sepInput R w di) n m (ofsI (G := G)) (wI w) (tlI di) (rvI di) (roI R di) := by
  have hlen : ([n, m] ++ (List.range (n + 1)).map (fun v => #{d : G.Dart | (d.fst : ℕ) < v}) ++
      (List.finRange n).map w).length = 2 * n + 3 := by simp; omega
  have hC : ∀ i (hi : i < m) r, r < 3 → (sepInput R w di).data.getD (2 * n + 3 + 3 * i + r) 0 =
      [((di.symm ⟨i, hi⟩).fst : ℕ), (di (di.symm ⟨i, hi⟩).symm : ℕ),
        (di (R.rot (di.symm ⟨i, hi⟩)) : ℕ)].getD r 0 := by
    intro i hi r hr
    unfold sepInput
    simp only
    rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
      show 2 * n + 3 + 3 * i + r - (2 * n + 3) = 3 * i + r by omega,
      getD_flatMap3 _ _ (fun _ => rfl) i r (by simpa using hi) hr]
    simp
  refine ⟨?_, ?_, fun v hv => ?_, fun v hv => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · unfold sepInput; simp
  · unfold sepInput; simp
  · unfold sepInput
    simp only
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]
    simp [ofsI]
  · unfold sepInput
    simp only
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp; omega)]
    simp [wI, hv]
  · have := hC i hi 0 (by omega); simp only [Nat.add_zero] at this
    rw [this]; simp [tlI, hi]
  · rw [hC i hi 1 (by omega)]; simp [rvI, hi]
  · rw [hC i hi 2 (by omega)]; simp [roI, hi]

theorem sepInput_le {W : ℕ} (hW : 16 * m + 12 * n + 3 * ∑ v, w v + 22 ≤ W) (j : ℕ) :
    (sepInput R w di).data.getD j 0 ≤ W := by
  have hm : Fintype.card G.Dart = m := by rw [Fintype.card_congr di, Fintype.card_fin]
  have hwle : ∀ v, w v ≤ ∑ v, w v := fun v => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
  rw [List.getD_eq_getElem?_getD]
  rcases h : (sepInput R w di).data[j]? with _ | x
  · simp
  · have hx := List.mem_of_getElem? h
    simp only [Option.getD_some]
    unfold sepInput at hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_range, List.mem_finRange, true_and, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | ((⟨v, -, rfl⟩ | ⟨v, rfl⟩) | ⟨i, rfl | rfl | rfl⟩)
    · omega
    · omega
    · have := card_le_card (filter_subset (fun d : G.Dart => (d.fst : ℕ) < v) univ)
      rw [card_univ, hm] at this; omega
    · have := hwle v; omega
    · have := ((di.symm i).fst).2; omega
    · have := (di (di.symm i).symm).2; omega
    · have := (di (R.rot (di.symm i))).2; omega

/-- **The target `SeparatorMachine`.** -/
theorem separatorMachine_holds : SeparatorMachine := by
  refine ⟨compile sepProg 0 ++ [Instr.halt], ?_⟩
  intro n m G _ R hR w di hdi W hW
  have hE := enc_sepInput R w di hdi
  have hIn := inHolds_sepInput R w di
  have hsum : ∑ v ∈ range n, wI w v = ∑ v, w v := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [wI]
  have hW' : memTop n m + 3 * ∑ v ∈ range n, wI w v + 2 * n + 3 * m + 10 ≤ W := by
    rw [hsum]; unfold memTop; omega
  obtain ⟨out, h1, h2⟩ := sepProg_sepOut hR w hE hIn hW' (sepInput_le R w di hW)
  exact ⟨out, h1, h2⟩

end SepProg

end PlanarSeparator
