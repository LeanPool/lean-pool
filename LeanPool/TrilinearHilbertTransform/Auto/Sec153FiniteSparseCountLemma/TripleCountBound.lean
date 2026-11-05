/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec153FiniteSparseCountLemma.Setup

/-!
# Trilinear Hilbert transform: triple_count_bound
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
section TripleCount
open Pointwise

open scoped Classical in
private def TripleCountBoundHP₃cardStatement.{u_1} : Prop :=
  ∀ (d : ℕ)
    (ι : Type u_1)
    (ζ : Fin d → ℤ)
    (N : ℕ)
    (H : ℕ)
    (ε : Fin (3 : ℕ) → ℕ)
    (α : Fin (3 : ℕ) → ℤ)
    (β : Fin (3 : ℕ) → ℤ)
    (_ : ∀ (j : Fin (3 : ℕ)), α j * β j = (6 : ℤ))
    (_ : ∀ (j : Fin (3 : ℕ)), |α j| ≤ (3 : ℤ))
    (B : Fin (3 : ℕ) → Finset ℤ)
    (B₀ : Fin (3 : ℕ) → Finset ℤ)
    (P : Fin (3 : ℕ) → Finset ℤ)
    (_ : ∀ (j : Fin (3 : ℕ)), B₀ j ⊆ B j)
    (_ : ∀ (j : Fin (3 : ℕ)), (B₀ j).Nonempty)
    (_ : ∀ (j : Fin (3 : ℕ)), ∀ a ∈ B j, ∀ b ∈ B j, ∃ p ∈ P j, a - b - p ∈ shiftBox ζ N (ε j)
      (2 : ℕ))
    (_ : ∀ (j : Fin (3 : ℕ)), (shiftBox ζ N (ε j) (H + (2 : ℕ))).card ≤ (2 : ℕ) * (shiftBox ζ
      N (ε j) H).card)
    (Q : ℝ)
    (S : ℝ)
    (ν : ℝ)
    (Rs : ℝ)
    (Bw : ℝ)
    (_ : (0 : ℝ) ≤ Rs)
    (_ : (0 : ℝ) ≤ ν)
    (_ : (0 : ℝ) ≤ Bw)
    (_ : ∀ (j : Fin (3 : ℕ)), ∀ a ∈ B₀ j, ∀ a' ∈ B₀ j, ∀ (k : Fin d → ℤ), (∀ (i : Fin d),
      |(↑(k i) : ℝ)| ≤ Q) → |(↑(a - a' - shiftDot k ζ) : ℝ)| ≤ S → a = a')
    (V : Finset ι)
    (tv : ι → Fin (3 : ℕ) → ℤ)
    (F : Finset (Fin (3 : ℕ) → ℤ))
    (nv : ι → Fin d → ℤ)
    (nf : (Fin (3 : ℕ) → ℤ) → Fin d → ℤ)
    (_ : ∀ v ∈ V, ∀ (i : Fin d), |(↑(nv v i) : ℝ)| ≤ Bw)
    (_ : ∀ f ∈ F, ∀ (i : Fin d), |(↑(nf f i) : ℝ)| ≤ Bw)
    (_ : (144 : ℝ) * Bw + (216 : ℝ) * ((↑H : ℝ) * (↑N : ℝ)) ≤ Q)
    (_ : (12 : ℝ) * ((↑H : ℝ) * ((↑(ε (0 : Fin (3 : ℕ))) : ℝ) + (↑(ε (1 : Fin (3 : ℕ))) : ℝ)
      + (↑(ε (2 : Fin (3 : ℕ))) : ℝ))) + (4 : ℝ) * ν * Rs ≤ S)
    (_ : (0 : ℝ) ≤ (↑H : ℝ) * (↑N : ℝ))
    (_ : ∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ (↑H : ℝ) * (↑(ε j) : ℝ)),
  let out : ι × (Fin (3 : ℕ) → ℤ) → Fin (3 : ℕ) → ℤ :=
    fun (q : ι × (Fin (3 : ℕ) → ℤ)) => tv q.1 + q.2
  ∀ (_ : ∀ q ∈ V ×ˢ F, ∀ (j : Fin (3 : ℕ)), out q j ∈ (2 : ℕ) • B j),
  let nout : ι × (Fin (3 : ℕ) → ℤ) → Fin d → ℤ :=
    fun (q : ι × (Fin (3 : ℕ) → ℤ)) => nv q.1 + nf q.2
  ∀ (_ : ∀ q ∈ V ×ˢ F, |(↑(tripleResidual ζ α (out q) (nout q)) : ℝ)| ≤ (2 : ℝ) * ν * Rs),
  let Lc : ℤ × ℤ → Finset ℤ :=
    fun (pp : ℤ × ℤ) => Finset.image (fun (q : ι × (Fin (3 : ℕ) → ℤ)) => out q (2 : Fin
      (3 : ℕ))) ({q ∈ V ×ˢ F | out q (0 : Fin (3 : ℕ)) - pp.1 ∈ shiftBox ζ N (ε (0 : Fin
      (3 : ℕ))) (H + H) ∧ out q (1 : Fin (3 : ℕ)) - pp.2 ∈ shiftBox ζ N (ε (1 : Fin (3 :
      ℕ))) (H + H)})
  ∀ (P₃ : ℤ × ℤ → Finset ℤ)
    (_ : ∀ (pp : ℤ × ℤ), P₃ pp ⊆ Lc pp)
    (_ : ∀ (pp : ℤ × ℤ), ∀ p ∈ P₃ pp, ∀ p' ∈ P₃ pp, p - p' ∈ shiftBox ζ N (ε (2 : Fin (3 :
      ℕ))) (H + H) → p = p'),
  ∀ (pp : ℤ × ℤ), (↑(P₃ pp).card : ℚ) ≤ ((2 : ℚ) * (↑(P (2 : Fin (3 : ℕ))).card : ℚ) /
    (↑(B₀ (2 : Fin (3 : ℕ))).card : ℚ)) ^ (3 : ℕ)


open scoped Classical in
private def TripleCountBoundStage1Statement.{u_1} : Prop :=
  ∀ (d : ℕ)
    (ι : Type u_1)
    (ζ : Fin d → ℤ)
    (N : ℕ)
    (H : ℕ)
    (ε : Fin (3 : ℕ) → ℕ)
    (α : Fin (3 : ℕ) → ℤ)
    (_ : ∀ (j : Fin (3 : ℕ)), |α j| ≤ (3 : ℤ))
    (B : Fin (3 : ℕ) → Finset ℤ)
    (B₀ : Fin (3 : ℕ) → Finset ℤ)
    (P : Fin (3 : ℕ) → Finset ℤ)
    (Q : ℝ)
    (μ : ℝ)
    (ν : ℝ)
    (Bw : ℝ)
    (_ : (0 : ℝ) ≤ Bw)
    (V : Finset ι)
    (tv : ι → Fin (3 : ℕ) → ℤ)
    (Rv : ι → ℝ)
    (F : Finset (Fin (3 : ℕ) → ℤ))
    (Rf : (Fin (3 : ℕ) → ℤ) → ℝ)
    (nv : ι → Fin d → ℤ)
    (nf : (Fin (3 : ℕ) → ℤ) → Fin d → ℤ)
    (_ : ∀ v ∈ V, ∀ (i : Fin d), |(↑(nv v i) : ℝ)| ≤ Bw)
    (_ : ∀ f ∈ F, ∀ (i : Fin d), |(↑(nf f i) : ℝ)| ≤ Bw)
    (_ : ∀ v ∈ V, μ * Rv v ≤ |(↑(tripleResidual ζ α (tv v) (nv v)) : ℝ)| ∧ |(↑(tripleResidual
      ζ α (tv v) (nv v)) : ℝ)| ≤ ν * Rv v)
    (_ : ∀ f ∈ F, |(↑(tripleResidual ζ α f (nf f)) : ℝ)| ≤ ν * Rf f)
    (_ : ∀ f ∈ F, ∀ f' ∈ F, ∀ (j : Fin (3 : ℕ)) (k : Fin d → ℤ), (∀ (i : Fin d), |(↑(k i) :
      ℝ)| ≤ Q) → |(↑(f j - f' j - shiftDot k ζ) : ℝ)| ≤ (4 : ℝ) * ((↑H : ℝ) * (↑(ε j) :
      ℝ)) → f j = f' j)
    (_ : ∀ v ∈ V, ∀ v' ∈ V, v ≠ v' → Rv v' < Rv v ∨ Rv v < Rv v')
    (_ : ∀ v ∈ V, ∀ v' ∈ V, Rv v' < Rv v → ν * Rv v' ≤ μ * Rv v / (1000 : ℝ))
    (_ : ∀ v ∈ V, ∀ f ∈ F, ν * Rf f ≤ μ * Rv v / (1000 : ℝ))
    (_ : ∀ v ∈ V, ∀ (j : Fin (3 : ℕ)), (36 : ℝ) * ((↑H : ℝ) * (↑(ε j) : ℝ)) ≤ μ * Rv v /
      (1000 : ℝ))
    (_ : ∀ v ∈ V, ∀ (m : Fin d → ℤ), (∀ (i : Fin d), |(↑(m i) : ℝ)| ≤ Q) → ¬(μ * Rv v / (50 :
      ℝ) ≤ |(↑(shiftDot m ζ) : ℝ)| ∧ |(↑(shiftDot m ζ) : ℝ)| ≤ (50 : ℝ) * ν * Rv v))
    (_ : (144 : ℝ) * Bw + (216 : ℝ) * ((↑H : ℝ) * (↑N : ℝ)) ≤ Q)
    (_ : ∀ v ∈ V, (0 : ℝ) ≤ μ * Rv v)
    (_ : (0 : ℝ) ≤ (↑H : ℝ) * (↑N : ℝ))
    (Pc : Fin (3 : ℕ) → Finset ℤ)
    (_ : ∀ (j : Fin (3 : ℕ)), ∀ x ∈ (2 : ℕ) • B j, ∃ p ∈ Pc j, x - p ∈ shiftBox ζ N (ε j) (H
      + H))
    (_ : ∀ (j : Fin (3 : ℕ)), (↑(Pc j).card : ℚ) ≤ ((2 : ℚ) * (↑(P j).card : ℚ) / (↑(B₀
      j).card : ℚ)) ^ (2 : ℕ) * (↑(B₀ j).card : ℚ)),
  let out : ι × (Fin (3 : ℕ) → ℤ) → Fin (3 : ℕ) → ℤ :=
    fun (q : ι × (Fin (3 : ℕ) → ℤ)) => tv q.1 + q.2
  ∀ (_ : ∀ q ∈ V ×ˢ F, ∀ (j : Fin (3 : ℕ)), out q j ∈ (2 : ℕ) • B j),
  let Lc : ℤ × ℤ → Finset ℤ :=
    fun (pp : ℤ × ℤ) => Finset.image (fun (q : ι × (Fin (3 : ℕ) → ℤ)) => out q (2 : Fin
      (3 : ℕ))) ({q ∈ V ×ˢ F | out q (0 : Fin (3 : ℕ)) - pp.1 ∈ shiftBox ζ N (ε (0 : Fin
      (3 : ℕ))) (H + H) ∧ out q (1 : Fin (3 : ℕ)) - pp.2 ∈ shiftBox ζ N (ε (1 : Fin (3 :
      ℕ))) (H + H)})
  ∀ (P₃ : ℤ × ℤ → Finset ℤ)
    (_ : ∀ (pp : ℤ × ℤ), ∀ x ∈ Lc pp, ∃ p ∈ P₃ pp, x - p ∈ shiftBox ζ N (ε (2 : Fin (3 : ℕ)))
      (H + H))
    (_ : ∀ (pp : ℤ × ℤ), (↑(P₃ pp).card : ℚ) ≤ ((2 : ℚ) * (↑(P (2 : Fin (3 : ℕ))).card : ℚ) /
      (↑(B₀ (2 : Fin (3 : ℕ))).card : ℚ)) ^ (3 : ℕ)),
  (↑(V.card * F.card) : ℚ) ≤ ((2 : ℚ) * (↑(P (0 : Fin (3 : ℕ))).card : ℚ) / (↑(B₀ (0 :
    Fin (3 : ℕ))).card : ℚ)) ^ (2 : ℕ) * (↑(B₀ (0 : Fin (3 : ℕ))).card : ℚ) * (((2 :
    ℚ) * (↑(P (1 : Fin (3 : ℕ))).card : ℚ) / (↑(B₀ (1 : Fin (3 : ℕ))).card : ℚ)) ^ (2
    : ℕ) * (↑(B₀ (1 : Fin (3 : ℕ))).card : ℚ)) * ((2 : ℚ) * (↑(P (2 : Fin (3 :
    ℕ))).card : ℚ) / (↑(B₀ (2 : Fin (3 : ℕ))).card : ℚ)) ^ (3 : ℕ)




private theorem triple_count_bound_hP₃card : TripleCountBoundHP₃cardStatement := by
  classical
  intro d ι ζ N H ε α β hαβ hα3 B B₀ P hB₀ hB₀ne hcov hdouble Q S ν Rs Bw hRs hν hBw hanch V tv F
    nv nf hnv hnf hQ hS hHN hHε out hout nout hres Lc P₃ hP₃sub hP₃pack pp
  refine column_packing_bound ζ N (ε 2) H (B 2) (B₀ 2) (P 2) (hB₀ 2) (hB₀ne 2) (hcov 2)
    (hdouble 2) (hanch 2) (hαβ 2) (hα3 2) (Lc pp) ?_ (Kc := 24 * (H * N) + 24 * Bw)
    (Ec := 12 * (H * ε 0) + 12 * (H * ε 1) + 4 * ν * Rs) ?_ ?_ ?_ ?_ ?_ (P₃ pp) (hP₃sub pp)
    (hP₃pack pp)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact hout q (Finset.mem_filter.mp hq).1 2
  · intro x hx x' hx'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨hqVF, hq0, hq1⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq'VF, hq'0, hq'1⟩ := Finset.mem_filter.mp hq'
    have hd0 := sub_mem_shiftBox hq0 hq'0
    have hd1 := sub_mem_shiftBox hq1 hq'1
    rw [show out q 0 - pp.1 - (out q' 0 - pp.1) = out q 0 - out q' 0 by ring] at hd0
    rw [show out q 1 - pp.2 - (out q' 1 - pp.2) = out q 1 - out q' 1 by ring] at hd1
    obtain ⟨k0, hk0, w0, hw0, he0⟩ := mem_shiftBox_real hd0
    obtain ⟨k1, hk1, w1, hw1, he1⟩ := mem_shiftBox_real hd1
    refine ⟨-(α 0 • k0) - α 1 • k1 - (6 : ℤ) • (nout q - nout q'), fun i => ?_, ?_⟩
    · obtain ⟨hv, hf⟩ := Finset.mem_product.mp hqVF
      obtain ⟨hv', hf'⟩ := Finset.mem_product.mp hq'VF
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, nout, Pi.add_apply]
      push_cast
      have a0 : |(α 0 : ℝ)| ≤ 3 := by rw [← Int.cast_abs]; exact_mod_cast hα3 0
      have a1 : |(α 1 : ℝ)| ≤ 3 := by rw [← Int.cast_abs]; exact_mod_cast hα3 1
      have b0 := hk0 i; have b1 := hk1 i
      have c1 := hnv _ hv i; have c2 := hnf _ hf i
      have c3 := hnv _ hv' i; have c4 := hnf _ hf' i
      push_cast at b0 b1
      have t0 : |(α 0 : ℝ) * k0 i| ≤ 3 * ((H + H + (H + H)) * N) := by
        rw [abs_mul]; exact mul_le_mul a0 b0 (abs_nonneg _) (by norm_num)
      have t1 : |(α 1 : ℝ) * k1 i| ≤ 3 * ((H + H + (H + H)) * N) := by
        rw [abs_mul]; exact mul_le_mul a1 b1 (abs_nonneg _) (by norm_num)
      have t2 : |6 * ((nv q.1 i : ℝ) + nf q.2 i - (nv q'.1 i + nf q'.2 i))| ≤ 6 * (4 * Bw) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        gcongr
        calc _ ≤ |(nv q.1 i : ℝ)| + |(nf q.2 i : ℝ)| +
              (|(nv q'.1 i : ℝ)| + |(nf q'.2 i : ℝ)|) := by
              refine (abs_sub _ _).trans ?_
              exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
          _ ≤ 4 * Bw := by linarith
      calc _ ≤ |(α 0 : ℝ) * k0 i| + |(α 1 : ℝ) * k1 i| +
            |6 * ((nv q.1 i : ℝ) + nf q.2 i - (nv q'.1 i + nf q'.2 i))| := by
            refine (abs_sub _ _).trans ?_
            refine add_le_add ((abs_sub _ _).trans ?_) le_rfl
            rw [abs_neg]
        _ ≤ _ := by linarith
    · have hr := hres q hqVF
      have hr' := hres q' hq'VF
      have hid : α 2 * (out q 2 - out q' 2) -
          6 * shiftDot (-(α 0 • k0) - α 1 • k1 - (6 : ℤ) • (nout q - nout q')) ζ =
          tripleResidual ζ α (out q) (nout q) - tripleResidual ζ α (out q') (nout q') -
            α 0 * w0 - α 1 * w1 := by
        simp only [tripleResidual, Fin.sum_univ_three]
        simp only [sub_eq_add_neg, shiftDot_add, shiftDot_neg, shiftDot_smul] at he0 he1 ⊢
        linear_combination (-(α 0)) * he0 + (-(α 1)) * he1
      rw [hid]
      push_cast
      have a0 : |(α 0 : ℝ)| ≤ 3 := by rw [← Int.cast_abs]; exact_mod_cast hα3 0
      have a1 : |(α 1 : ℝ)| ≤ 3 := by rw [← Int.cast_abs]; exact_mod_cast hα3 1
      push_cast at hw0 hw1
      have t0 : |(α 0 : ℝ) * w0| ≤ 3 * ((H + H + (H + H)) * ε 0) := by
        rw [abs_mul]; exact mul_le_mul a0 hw0 (abs_nonneg _) (by norm_num)
      have t1 : |(α 1 : ℝ) * w1| ≤ 3 * ((H + H + (H + H)) * ε 1) := by
        rw [abs_mul]; exact mul_le_mul a1 hw1 (abs_nonneg _) (by norm_num)
      calc _ ≤ |(tripleResidual ζ α (out q) (nout q) : ℝ)| +
            |(tripleResidual ζ α (out q') (nout q') : ℝ)| + |(α 0 : ℝ) * w0| +
              |(α 1 : ℝ) * w1| := by
            refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add ((abs_sub _ _).trans le_rfl) le_rfl)) le_rfl)
        _ ≤ _ := by linarith
  · nlinarith
  · nlinarith
  · have : (H * (ε 0 + ε 1 + ε 2) : ℝ) = H * ε 0 + H * ε 1 + H * ε 2 := by ring
    nlinarith [hHε 2]
  · have : (H * (ε 0 + ε 1 + ε 2) : ℝ) = H * ε 0 + H * ε 1 + H * ε 2 := by ring
    nlinarith [hHε 0, hHε 1, hHε 2, mul_nonneg hν hRs]
-- the box map



private theorem triple_count_bound_stage_1 : TripleCountBoundStage1Statement := by
  classical
  intro d ι ζ N H ε α hα3 B B₀ P Q μ ν Bw hBw V tv Rv F Rf nv nf hnv hnf hannv hannf hsepF hdist
    hsmallv hsmallf hsmallε hgap hQ hμR hHN Pc hPccov hPccard out hout Lc P₃ hP₃cov hP₃card
  have hbox : ∀ q ∈ V ×ˢ F, ∃ p₁ ∈ Pc 0, ∃ p₂ ∈ Pc 1, ∃ p₃ ∈ P₃ (p₁, p₂),
      out q 0 - p₁ ∈ shiftBox ζ N (ε 0) (H + H) ∧ out q 1 - p₂ ∈ shiftBox ζ N (ε 1) (H + H) ∧
        out q 2 - p₃ ∈ shiftBox ζ N (ε 2) (H + H) := by
    intro q hq
    obtain ⟨p₁, hp₁, h₁⟩ := hPccov 0 _ (hout q hq 0)
    obtain ⟨p₂, hp₂, h₂⟩ := hPccov 1 _ (hout q hq 1)
    have hmem : out q 2 ∈ Lc (p₁, p₂) :=
      Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, h₁, h₂⟩, rfl⟩
    obtain ⟨p₃, hp₃, h₃⟩ := hP₃cov _ _ hmem
    exact ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, h₁, h₂, h₃⟩
  choose! b₁ hb₁ b₂ hb₂ b₃ hb₃ hbx₁ hbx₂ hbx₃ using hbox
  set! boxes := (Pc 0 ×ˢ Pc 1).sigma fun pp => P₃ pp
  have hinj : (V ×ˢ F).card ≤ boxes.card := by
    refine Finset.card_le_card_of_injOn (fun q => (⟨(b₁ q, b₂ q), b₃ q⟩ : Σ _ : ℤ × ℤ, ℤ))
      (fun q hq => Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hb₁ q hq, hb₂ q hq⟩,
        hb₃ q hq⟩) ?_
    intro q hq q' hq' heq
    simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at heq
    obtain ⟨⟨e₁, e₂⟩, e₃⟩ := heq
    -- coordinate differences lie in `U_j(4H)`
    have hd : ∀ j, out q j - out q' j ∈ shiftBox ζ N (ε j) (H + H + (H + H)) := by
      intro j
      fin_cases j
      · have := sub_mem_shiftBox (hbx₁ q hq) (hbx₁ q' hq')
        rwa [e₁, show out q 0 - b₁ q' - (out q' 0 - b₁ q') = out q 0 - out q' 0 by ring] at this
      · have := sub_mem_shiftBox (hbx₂ q hq) (hbx₂ q' hq')
        rwa [e₂, show out q 1 - b₂ q' - (out q' 1 - b₂ q') = out q 1 - out q' 1 by ring] at this
      · have := sub_mem_shiftBox (hbx₃ q hq) (hbx₃ q' hq')
        rwa [e₃, show out q 2 - b₃ q' - (out q' 2 - b₃ q') = out q 2 - out q' 2 by ring] at this
    choose k hk w hw hkw using fun j => mem_shiftBox_real (hd j)
    obtain ⟨hv, hf⟩ := Finset.mem_product.mp hq
    obtain ⟨hv', hf'⟩ := Finset.mem_product.mp hq'
    by_cases hvv : q.1 = q'.1
    · have hff : q.2 = q'.2 := by
        funext j
        refine hsepF _ hf _ hf' j ((6 : ℤ) • k j) (fun i => ?_) ?_
        · simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, abs_mul]
          have := hk j i; push_cast at this ⊢; norm_num; nlinarith
        · have : q.2 j - q'.2 j - shiftDot ((6 : ℤ) • k j) ζ = w j := by
            rw [shiftDot_smul]
            have h := hkw j
            simp only [out, Pi.add_apply, hvv] at h
            linarith
          rw [this]; have := hw j; push_cast at this ⊢; linarith
      exact Prod.ext hvv hff
    · exfalso
      have hwj : ∀ v ∈ V, ∀ j, |(w j : ℝ)| ≤ μ * Rv v / 9000 := by
        intro v hvV j
        have := hw j; have := hsmallε v hvV j; push_cast at *; nlinarith
      rcases hdist _ hv _ hv' hvv with hlt | hlt
      · refine translated_triples_gap ζ α hα3 (tv q.1) (tv q'.1) q.2 q'.2 (nv q.1) (nv q'.1)
          (nf q.2) (nf q'.2) k w (fun j => hkw j)
          (μ := μ) (ν := ν) (R := Rv q.1) (e₁ := μ * Rv q.1 / 1000) (e₂ := μ * Rv q.1 / 9000)
          (Bw := Bw) (Kb := 4 * (H * N)) (Q := Q) (hμR _ hv) (hannv _ hv).1 (hannv _ hv).2
          ((hannv _ hv').2.trans (hsmallv _ hv _ hv' hlt)) ((hannf _ hf).trans (hsmallf _ hv _ hf))
          ((hannf _ hf').trans (hsmallf _ hv _ hf')) (hwj _ hv) (by nlinarith [hμR _ hv])
          (fun i => ⟨hnv _ hv i, hnv _ hv' i, hnf _ hf i, hnf _ hf' i⟩)
          (fun j i => by have := hk j i; push_cast at this ⊢; linarith) (by linarith)
          (hgap _ hv)
      · refine translated_triples_gap ζ α hα3 (tv q'.1) (tv q.1) q'.2 q.2 (nv q'.1) (nv q.1)
          (nf q'.2) (nf q.2) (fun j => -k j) (fun j => -w j) (fun j => by
            have h := hkw j
            change (tv q.1 j + q.2 j) - (tv q'.1 j + q'.2 j) = _ at h
            rw [shiftDot_neg]; linarith)
          (μ := μ) (ν := ν) (R := Rv q'.1) (e₁ := μ * Rv q'.1 / 1000)
          (e₂ := μ * Rv q'.1 / 9000) (Bw := Bw) (Kb := 4 * (H * N)) (Q := Q) (hμR _ hv')
          (hannv _ hv').1 (hannv _ hv').2 ((hannv _ hv).2.trans (hsmallv _ hv' _ hv hlt))
          ((hannf _ hf').trans (hsmallf _ hv' _ hf')) ((hannf _ hf).trans (hsmallf _ hv' _ hf))
          (fun j => by rw [Int.cast_neg, abs_neg]; exact hwj _ hv' j) (by nlinarith [hμR _ hv'])
          (fun i => ⟨hnv _ hv' i, hnv _ hv i, hnf _ hf' i, hnf _ hf i⟩)
          (fun j i => by
            have := hk j i; simp only [Pi.neg_apply, Int.cast_neg, abs_neg]
            push_cast at this ⊢; linarith) (by linarith) (hgap _ hv')
  -- count the boxes
  have hboxes : (boxes.card : ℚ) ≤ ((Pc 0).card : ℚ) * (Pc 1).card *
      (2 * (P 2).card / (B₀ 2).card : ℚ) ^ 3 := by
    rw [Finset.card_sigma]
    push_cast
    calc ∑ pp ∈ Pc 0 ×ˢ Pc 1, ((P₃ pp).card : ℚ)
        ≤ ∑ _pp ∈ Pc 0 ×ˢ Pc 1, (2 * (P 2).card / (B₀ 2).card : ℚ) ^ 3 :=
          Finset.sum_le_sum fun pp _ => hP₃card pp
      _ = _ := by rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
  rw [Finset.card_product] at hinj
  have h1 : ((V.card * F.card : ℕ) : ℚ) ≤ boxes.card := by exact_mod_cast hinj
  refine h1.trans (hboxes.trans ?_)
  have hr : (0 : ℚ) ≤ (2 * (P 2).card / (B₀ 2).card : ℚ) ^ 3 :=
    pow_nonneg (div_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) 3
  have hA0 : (0 : ℚ) ≤ (2 * (P 0).card / (B₀ 0).card : ℚ) ^ 2 * (B₀ 0).card :=
    mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hPccard 0) (hPccard 1) (Nat.cast_nonneg _) hA0) hr


/-- Blueprint lines 2678-2694 (slab cover and separation of translated triples): with growth
data for three roles, the indexed outputs `t_v + f` of the selected middle-range triples `t_v`
and the last-range triples `f ∈ F` lie in distinct cover boxes, so
`q |F| ≤ (2|P₀|/|B₀₀|)² |B₀₀| (2|P₁|/|B₀₁|)² |B₀₁| (2|P₂|/|B₀₂|)³`. -/
theorem triple_count_bound {d : ℕ} {ι : Type*} (ζ : Fin d → ℤ) (N H : ℕ)
    (ε : Fin 3 → ℕ) (α β : Fin 3 → ℤ) (hαβ : ∀ j, α j * β j = 6) (hα3 : ∀ j, |α j| ≤ 3)
    (B B₀ P : Fin 3 → Finset ℤ) (hB₀ : ∀ j, B₀ j ⊆ B j) (hB₀ne : ∀ j, (B₀ j).Nonempty)
    (hcov : ∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∃ p ∈ P j, a - b - p ∈ shiftBox ζ N (ε j) 2)
    (hdouble : ∀ j, (shiftBox ζ N (ε j) (H + 2)).card ≤ 2 * (shiftBox ζ N (ε j) H).card)
    {Q S μ ν Rs Bw : ℝ} (hRs : 0 ≤ Rs) (hν : 0 ≤ ν) (hBw : 0 ≤ Bw)
    (hanch : ∀ j, ∀ a ∈ B₀ j, ∀ a' ∈ B₀ j, ∀ k : Fin d → ℤ, (∀ i, |(k i : ℝ)| ≤ Q) →
      |((a - a' - shiftDot k ζ : ℤ) : ℝ)| ≤ S → a = a')
    (V : Finset ι) (tv : ι → Fin 3 → ℤ) (htv : ∀ v ∈ V, ∀ j, tv v j ∈ B j) (Rv : ι → ℝ)
    (F : Finset (Fin 3 → ℤ)) (hF : ∀ f ∈ F, ∀ j, f j ∈ B j) (Rf : (Fin 3 → ℤ) → ℝ)
    (nv : ι → Fin d → ℤ) (nf : (Fin 3 → ℤ) → Fin d → ℤ)
    (hnv : ∀ v ∈ V, ∀ i, |(nv v i : ℝ)| ≤ Bw) (hnf : ∀ f ∈ F, ∀ i, |(nf f i : ℝ)| ≤ Bw)
    (hannv : ∀ v ∈ V, μ * Rv v ≤ |(tripleResidual ζ α (tv v) (nv v) : ℝ)| ∧
      |(tripleResidual ζ α (tv v) (nv v) : ℝ)| ≤ ν * Rv v)
    (hannf : ∀ f ∈ F, |(tripleResidual ζ α f (nf f) : ℝ)| ≤ ν * Rf f)
    (hRv : ∀ v ∈ V, Rv v ≤ Rs) (hRf : ∀ f ∈ F, Rf f ≤ Rs)
    (hsepF : ∀ f ∈ F, ∀ f' ∈ F, ∀ j, ∀ k : Fin d → ℤ, (∀ i, |(k i : ℝ)| ≤ Q) →
      |((f j - f' j - shiftDot k ζ : ℤ) : ℝ)| ≤ 4 * (H * ε j : ℝ) → f j = f' j)
    (hdist : ∀ v ∈ V, ∀ v' ∈ V, v ≠ v' → Rv v' < Rv v ∨ Rv v < Rv v')
    (hsmallv : ∀ v ∈ V, ∀ v' ∈ V, Rv v' < Rv v → ν * Rv v' ≤ μ * Rv v / 1000)
    (hsmallf : ∀ v ∈ V, ∀ f ∈ F, ν * Rf f ≤ μ * Rv v / 1000)
    (hsmallε : ∀ v ∈ V, ∀ j, 36 * (H * ε j : ℝ) ≤ μ * Rv v / 1000)
    (hgap : ∀ v ∈ V, ∀ m : Fin d → ℤ, (∀ i, |(m i : ℝ)| ≤ Q) →
      ¬ (μ * Rv v / 50 ≤ |(shiftDot m ζ : ℝ)| ∧ |(shiftDot m ζ : ℝ)| ≤ 50 * ν * Rv v))
    (hQ : 144 * Bw + 216 * (H * N : ℝ) ≤ Q)
    (hS : 12 * (H * (ε 0 + ε 1 + ε 2) : ℝ) + 4 * ν * Rs ≤ S) (hμR : ∀ v ∈ V, 0 ≤ μ * Rv v) :
    ((V.card * F.card : ℕ) : ℚ) ≤
      ((2 * (P 0).card / (B₀ 0).card : ℚ) ^ 2 * (B₀ 0).card) *
        ((2 * (P 1).card / (B₀ 1).card : ℚ) ^ 2 * (B₀ 1).card) *
          (2 * (P 2).card / (B₀ 2).card : ℚ) ^ 3 := by
  classical
  have hHN : (0 : ℝ) ≤ H * N := by positivity
  have hHε : ∀ j, (0 : ℝ) ≤ H * ε j := fun j => by positivity
  have hsep : ∀ j, ∀ a ∈ B₀ j, ∀ a' ∈ B₀ j, a - a' ∈ shiftBox ζ N (ε j) (H + H) → a = a' := by
    intro j
    refine anchor_sep_shiftBox (hanch j) (by nlinarith [hHN]) ?_
    have h0 := hHε 0; have h1 := hHε 1; have h2 := hHε 2
    have : (H * ε j : ℝ) ≤ H * (ε 0 + ε 1 + ε 2) := by
      fin_cases j <;> simp <;> nlinarith
    nlinarith [mul_nonneg hν hRs]
  -- packings of the first two roles
  have hpk : ∀ j, ∃ P' ⊆ 2 • B j, (∀ p ∈ P', ∀ p' ∈ P', p - p' ∈ shiftBox ζ N (ε j) (H + H) →
      p = p') ∧ ∀ x ∈ 2 • B j, ∃ p ∈ P', x - p ∈ shiftBox ζ N (ε j) (H + H) := fun j =>
    exists_packing_cover _ _ (zero_mem_shiftBox _ _ _ _) fun x hx => neg_mem_shiftBox hx
  choose Pc hPcsub hPcpack hPccov using hpk
  have hPccard : ∀ j, ((Pc j).card : ℚ) ≤ (2 * (P j).card / (B₀ j).card : ℚ) ^ 2 * (B₀ j).card :=
    fun j => growth_packing_bound (fun t => shiftBox ζ N (ε j) t)
      (fun t => zero_mem_shiftBox _ _ _ t) (fun t t' x y hx hy => add_mem_shiftBox hx hy)
      (fun t x hx => neg_mem_shiftBox hx) (B j) (B₀ j) (P j) (hB₀ j) (hB₀ne j) H (hsep j)
      (hcov j) (hdouble j) 2 (Pc j) (hPcsub j) (hPcpack j)
  -- outputs
  set! out : ι × (Fin 3 → ℤ) → Fin 3 → ℤ := fun q => tv q.1 + q.2
  have hout : ∀ q ∈ V ×ˢ F, ∀ j, out q j ∈ 2 • B j := by
    intro q hq j
    obtain ⟨hv, hf⟩ := Finset.mem_product.mp hq
    rw [two_nsmul]
    exact Finset.add_mem_add (htv _ hv j) (hF _ hf j)
  set! nout : ι × (Fin 3 → ℤ) → Fin d → ℤ := fun q => nv q.1 + nf q.2
  have hres : ∀ q ∈ V ×ˢ F, |(tripleResidual ζ α (out q) (nout q) : ℝ)| ≤ 2 * ν * Rs := by
    intro q hq
    obtain ⟨hv, hf⟩ := Finset.mem_product.mp hq
    simp only [out, nout, tripleResidual_add]
    push_cast
    have h1 := (hannv _ hv).2
    have h2 := hannf _ hf
    have h3 := hRv _ hv
    have h4 := hRf _ hf
    calc _ ≤ |(tripleResidual ζ α (tv q.1) (nv q.1) : ℝ)| +
          |(tripleResidual ζ α q.2 (nf q.2) : ℝ)| := abs_add_le _ _
      _ ≤ ν * Rv q.1 + ν * Rf q.2 := add_le_add h1 h2
      _ ≤ 2 * ν * Rs := by nlinarith
  -- columns
  set! Lc : ℤ × ℤ → Finset ℤ := fun pp => ((V ×ˢ F).filter fun q =>
    out q 0 - pp.1 ∈ shiftBox ζ N (ε 0) (H + H) ∧
      out q 1 - pp.2 ∈ shiftBox ζ N (ε 1) (H + H)).image fun q => out q 2
  have hpk3 : ∀ pp : ℤ × ℤ, ∃ P' ⊆ Lc pp, (∀ p ∈ P', ∀ p' ∈ P',
      p - p' ∈ shiftBox ζ N (ε 2) (H + H) → p = p') ∧
      ∀ x ∈ Lc pp, ∃ p ∈ P', x - p ∈ shiftBox ζ N (ε 2) (H + H) := fun pp =>
    exists_packing_cover _ _ (zero_mem_shiftBox _ _ _ _) fun x hx => neg_mem_shiftBox hx
  choose P₃ hP₃sub hP₃pack hP₃cov using hpk3
  have hP₃card : ∀ pp, ((P₃ pp).card : ℚ) ≤ (2 * (P 2).card / (B₀ 2).card : ℚ) ^ 3 := by
    expose_names
    exact @triple_count_bound_hP₃card d ι ζ N H ε α β hαβ hα3 B B₀ P hB₀ hB₀ne hcov hdouble Q S ν
      Rs Bw hRs hν hBw hanch V tv F nv nf hnv hnf hQ hS hHN hHε hout hres P₃ hP₃sub hP₃pack
  expose_names
  exact @triple_count_bound_stage_1 d ι ζ N H ε α hα3 B B₀ P Q μ ν Bw hBw V tv Rv F Rf nv nf hnv
    hnf hannv hannf hsepF hdist hsmallv hsmallf hsmallε hgap hQ hμR hHN Pc hPccov hPccard hout P₃
    hP₃cov hP₃card

end TripleCount

/-! ### The integer form of the sparse-count data (blueprint lines 2587-2604) -/

/-- The progression coefficient `α_r = r - l'` of role `r` for the excluded role `l'`. -/
def roleCoeff (r l : Fin 4) : ℤ := (r : ℕ) - (l : ℕ)

theorem roleCoeff_table : ∀ r l : Fin 4, r ≠ l →
    |roleCoeff r l| ≤ 3 ∧ roleCoeff r l * (6 / roleCoeff r l) = 6 := by
  decide

theorem roleCoeff_spec {r l : Fin 4} (h : r ≠ l) :
    |roleCoeff r l| ≤ 3 ∧ ∃ β : ℤ, roleCoeff r l * β = 6 :=
  ⟨(roleCoeff_table r l h).1, _, (roleCoeff_table r l h).2⟩

/-- Blueprint `lem:sparse-count`, data after the reduction to a common grid: integer labels
divisible by six, integer reserved frequencies `ζ`, scales `R_s = R₀ 2^s`, and the five
hypotheses (pair determination with multiplicity `L`, side incidence, separation, annular
witnesses, and the pure-shift gap with the relaxed constants). -/
structure SparseCountData where
  /-- Dimension of the integer relation used in sparse counting. -/
  d : ℕ
  /-- Integer coefficients of the sparse-counting relation. -/
  ζ : Fin d → ℤ
  /-- Set of three or four core slots participating in sparse counting. -/
  core : Finset (Fin 4)
  core_card : core.card = 3 ∨ core.card = 4
  /-- Finite set of integer scales used in the counting estimate. -/
  S : Finset ℤ
  /-- Positive base length defining the physical scale at integer depth `s`. -/
  R₀ : ℝ
  R₀_pos : 0 < R₀
  /-- Finite family of integer slot tuples at each scale. -/
  E : ℤ → Finset (Fin 4 → ℤ)
  /-- Allowed coordinate values in each slot. -/
  A : Fin 4 → Finset ℤ
  /-- Uniform bound for the allowed coordinate counts and total incidence weight. -/
  M : ℝ
  one_le_M : 1 ≤ M
  card_A : ∀ i ∈ core, ((A i).card : ℝ) ≤ M
  mem_A : ∀ s ∈ S, ∀ x ∈ E s, ∀ i ∈ core, x i ∈ A i
  six_dvd : ∀ s ∈ S, ∀ x ∈ E s, ∀ i ∈ core, (6 : ℤ) ∣ x i
  /-- Upper bound for the number of scales sharing the same slot tuple. -/
  L : ℕ
  one_le_L : 1 ≤ L
  pair : ∀ i ∈ core, ∀ j ∈ core, i ≠ j → ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s',
    x i = x' i → x j = x' j → x = x'
  mult : ∀ x, (S.filter fun s => x ∈ E s).card ≤ L
  /-- Nonnegative scale weights controlling triple-core coordinate incidences. -/
  w : ℤ → ℝ
  w_nonneg : ∀ s, 0 ≤ w s
  w_sum : ∑ s ∈ S, w s ≤ M
  w_inc : core.card = 3 → ∀ s ∈ S, ∀ i ∈ core, ∀ a,
    (((E s).filter fun x => x i = a).card : ℝ) ≤ w s
  /-- Positive lower frequency scale in the sparse-counting separation assumptions. -/
  μ : ℝ
  /-- Upper frequency scale dominating the lower scale. -/
  ν : ℝ
  /-- Separation parameter entering the sparse-counting hypotheses. -/
  Sg : ℝ
  /-- Arithmetic parameter of the sparse-counting frequency relations. -/
  Q : ℝ
  /-- Positive complexity bound used in the sparse-counting estimates. -/
  B : ℝ
  μ_pos : 0 < μ
  μ_le_ν : μ ≤ ν
  one_le_B : 1 ≤ B
  one_le_μR : ∀ s ∈ S, 1 ≤ μ * (R₀ * 2 ^ s)
  sep : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i ≠ x' i →
    ∀ n : Fin d → ℤ, (∀ r, |(n r : ℝ)| ≤ Q) →
      Sg * max (R₀ * 2 ^ s) (R₀ * 2 ^ s') < |((x i - x' i + shiftDot n ζ : ℤ) : ℝ)|
  ann : ∀ T ⊆ core, T.card = 3 → ∀ l, l ∉ T → ∀ s ∈ S, ∀ x ∈ E s, ∃ n : Fin d → ℤ,
    (∀ r, |(n r : ℝ)| ≤ B) ∧
      μ * (R₀ * 2 ^ s) ≤ |((∑ r ∈ T, roleCoeff r l * x r + 36 * shiftDot n ζ : ℤ) : ℝ)| ∧
        |((∑ r ∈ T, roleCoeff r l * x r + 36 * shiftDot n ζ : ℤ) : ℝ)| ≤ ν * (R₀ * 2 ^ s)
  gap : ∀ s ∈ S, (E s).Nonempty → ∀ n : Fin d → ℤ, (∀ r, |(n r : ℝ)| ≤ Q) →
    ¬ (μ * (R₀ * 2 ^ s) / 50 ≤ |(shiftDot n ζ : ℝ)| ∧
      |(shiftDot n ζ : ℝ)| ≤ 50 * ν * (R₀ * 2 ^ s))

namespace SparseCountData
variable (D : SparseCountData)

/-- The scale `R_s = R₀ 2^s`. -/
noncomputable def R (s : ℤ) : ℝ := D.R₀ * 2 ^ s

theorem R_pos (s : ℤ) : 0 < D.R s := mul_pos D.R₀_pos (zpow_pos (by norm_num) s)

theorem R_strictMono : StrictMono D.R := fun s t h =>
  mul_lt_mul_of_pos_left (zpow_lt_zpow_right₀ (by norm_num) h) D.R₀_pos

theorem R_add (s : ℤ) (g : ℕ) : D.R (s + g) = 2 ^ g * D.R s := by
  unfold R; rw [zpow_add₀ (by norm_num), zpow_natCast]; ring

/-- Three distinct core roles exist besides any given core role. -/
theorem exists_two_other (D : SparseCountData) {i : Fin 4} (hi : i ∈ D.core) :
    ∃ j ∈ D.core, ∃ k ∈ D.core, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  have h3 : 3 ≤ D.core.card := by rcases D.core_card with h | h <;> omega
  have h2 : 2 ≤ (D.core.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp h2
  exact ⟨j, Finset.mem_of_mem_erase hj, k, Finset.mem_of_mem_erase hk,
    (Finset.ne_of_mem_erase hj).symm, (Finset.ne_of_mem_erase hk).symm, hjk⟩

/-- The total mass is at most `L M²` (pair determination and multiplicity). -/
theorem total_mass_le (S' : Finset ℤ) (hS' : S' ⊆ D.S) :
    (∑ s ∈ S', ((D.E s).card : ℝ)) ≤ D.L * D.M ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : D.core.Nonempty := by
    rw [← Finset.card_pos]; rcases D.core_card with h | h <;> omega
  obtain ⟨j, hj, -, -, hij, -, -⟩ := D.exists_two_other hi
  set O := S'.sigma fun s => D.E s
  have hO : (O.card : ℝ) = ∑ s ∈ S', ((D.E s).card : ℝ) := by
    rw [Finset.card_sigma]; push_cast; rfl
  have himg : (O.image fun o => (o.2 i, o.2 j)) ⊆ D.A i ×ˢ D.A j := by
    intro e he
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hs, hx⟩ := Finset.mem_sigma.mp ho
    exact Finset.mem_product.mpr ⟨D.mem_A _ (hS' hs) _ hx i hi, D.mem_A _ (hS' hs) _ hx j hj⟩
  have hfib : ∀ e ∈ O.image (fun o => (o.2 i, o.2 j)),
      (O.filter fun o => (o.2 i, o.2 j) = e).card ≤ D.L := by
    intro e he
    obtain ⟨o₀, ho₀, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hs₀, hx₀⟩ := Finset.mem_sigma.mp ho₀
    calc (O.filter fun o => (o.2 i, o.2 j) = (o₀.2 i, o₀.2 j)).card
        ≤ (D.S.filter fun s => o₀.2 ∈ D.E s).card := by
          refine Finset.card_le_card_of_injOn (fun o => o.1) ?_ ?_
          · intro o ho
            obtain ⟨ho, he'⟩ := Finset.mem_filter.mp ho
            obtain ⟨hs, hx⟩ := Finset.mem_sigma.mp ho
            simp only [Prod.mk.injEq] at he'
            have := D.pair i hi j hj hij _ (hS' hs) _ (hS' hs₀) _ hx _ hx₀ he'.1 he'.2
            exact Finset.mem_filter.mpr ⟨hS' hs, this ▸ hx⟩
          · intro o ho o' ho' h
            obtain ⟨ho, he'⟩ := Finset.mem_filter.mp ho
            obtain ⟨ho', he''⟩ := Finset.mem_filter.mp ho'
            obtain ⟨hs, hx⟩ := Finset.mem_sigma.mp ho
            obtain ⟨hs', hx'⟩ := Finset.mem_sigma.mp ho'
            simp only [Prod.mk.injEq] at he' he''
            have e1 := D.pair i hi j hj hij _ (hS' hs) _ (hS' hs₀) _ hx _ hx₀ he'.1 he'.2
            have e2 := D.pair i hi j hj hij _ (hS' hs') _ (hS' hs₀) _ hx' _ hx₀ he''.1 he''.2
            exact Sigma.ext h (heq_of_eq (e1.trans e2.symm))
      _ ≤ D.L := D.mult _
  have h1 := Finset.card_le_mul_card_image O _ hfib
  have h2 := Finset.card_le_card himg
  rw [Finset.card_product] at h2
  rw [← hO]
  have hAi := D.card_A i hi
  have hAj := D.card_A j hj
  have hM0 : 0 ≤ D.M := by linarith [D.one_le_M]
  calc (O.card : ℝ) ≤ D.L * (O.image fun o => (o.2 i, o.2 j)).card := by exact_mod_cast h1
    _ ≤ D.L * ((D.A i).card * (D.A j).card) := by gcongr; exact_mod_cast h2
    _ ≤ D.L * (D.M * D.M) := by gcongr
    _ = D.L * D.M ^ 2 := by ring

/-! ### Blocks and difference covers (lem:sparse-count, blueprint lines 2611-2626) -/

/-- Occurrences with a common pair of labels in two distinct core roles have at most `L`
elements (pair determination and multiplicity). -/
theorem pair_fiber_le (O : Finset (ℤ × (Fin 4 → ℤ))) (hO : ∀ o ∈ O, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1)
    {i j : Fin 4} (hi : i ∈ D.core) (hj : j ∈ D.core) (hij : i ≠ j) (e : ℤ × ℤ) :
    (O.filter fun o => (o.2 i, o.2 j) = e).card ≤ D.L := by
  classical
  rcases (O.filter fun o => (o.2 i, o.2 j) = e).eq_empty_or_nonempty with h | ⟨o₀, ho₀⟩
  · rw [h]; exact Nat.zero_le _
  obtain ⟨ho₀O, he₀⟩ := Finset.mem_filter.mp ho₀
  obtain ⟨hs₀, hx₀⟩ := hO o₀ ho₀O
  calc (O.filter fun o => (o.2 i, o.2 j) = e).card
      ≤ (D.S.filter fun s => o₀.2 ∈ D.E s).card := by
        refine Finset.card_le_card_of_injOn (fun o => o.1) ?_ ?_
        · intro o ho
          obtain ⟨hoO, he'⟩ := Finset.mem_filter.mp ho
          obtain ⟨hs, hx⟩ := hO o hoO
          rw [← he₀] at he'
          simp only [Prod.mk.injEq] at he'
          have := D.pair i hi j hj hij _ hs _ hs₀ _ hx _ hx₀ he'.1 he'.2
          exact Finset.mem_filter.mpr ⟨hs, this ▸ hx⟩
        · intro o ho o' ho' h
          obtain ⟨hoO, he'⟩ := Finset.mem_filter.mp ho
          obtain ⟨ho'O, he''⟩ := Finset.mem_filter.mp ho'
          obtain ⟨hs, hx⟩ := hO o hoO
          obtain ⟨hs', hx'⟩ := hO o' ho'O
          rw [← he₀] at he' he''
          simp only [Prod.mk.injEq] at he' he''
          have e1 := D.pair i hi j hj hij _ hs _ hs₀ _ hx _ hx₀ he'.1 he'.2
          have e2 := D.pair i hi j hj hij _ hs' _ hs₀ _ hx' _ hx₀ he''.1 he''.2
          exact Prod.ext h (e1.trans e2.symm)
    _ ≤ D.L := D.mult _

theorem card_pow_four_le {n : ℕ} {M : ℝ} (h : (n : ℝ) ≤ M) :
    ((n * (n * (n * n)) : ℕ) : ℝ) ≤ M ^ 4 := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hM : 0 ≤ M := h0.trans h
  push_cast
  calc (n : ℝ) * (n * (n * n)) ≤ M * (M * (M * M)) := by gcongr
    _ = M ^ 4 := by ring

theorem cover_count_arith {P κ : ℕ} {M η : ℝ} (hη : 0 < η) (hM : 0 < M)
    (h : (P : ℝ) * κ ≤ M ^ 4) (hκ : η ^ 5 * M ^ 3 / 160000 ≤ (κ : ℝ)) :
    (P : ℝ) ≤ 160000 / η ^ 5 * M := by
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have h1 : (P : ℝ) * (η ^ 5 * M ^ 3 / 160000) ≤ M ^ 4 :=
    (mul_le_mul_of_nonneg_left hκ hP0).trans h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h2 : (P : ℝ) * η ^ 5 * M ^ 3 ≤ 160000 * M * M ^ 3 := by nlinarith
  exact le_of_mul_le_mul_right h2 (by positivity)

theorem abs_alt_four_le (a b c d : ℝ) : |a - b + c - d| ≤ |a| + |b| + |c| + |d| := by
  calc |a - b + c - d| ≤ |a - b + c| + |d| := abs_sub _ _
    _ ≤ |a - b| + |c| + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by gcongr; exact abs_sub _ _

theorem sum_three {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : Fin 4 → ℤ) :
    ∑ r ∈ ({i, j, k} : Finset (Fin 4)), f r = f i + f j + f k := by
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton]
  ring

/-- Blueprint lines 2618-2626 (one extraction step): if the occurrences with an uncovered
`i`-label have mass greater than `η L M²`, the four-step paths of the `(i, j)` projection,
coloured by the `k`-label, give a subset `B₀` of the uncovered labels with `|B₀| ≥ η M / 3`
whose difference set is covered by at most `160000 η^{-5} M` translates of `U(2)`. -/
theorem extract_cover_subset (O : Finset (ℤ × (Fin 4 → ℤ)))
    (hO : ∀ o ∈ O, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) {i j k l : Fin 4} (hi : i ∈ D.core)
    (hj : j ∈ D.core) (hk : k ∈ D.core) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hl : l ∉ ({i, j, k} : Finset (Fin 4))) {Rp : ℝ} (hRp : ∀ o ∈ O, D.R o.1 ≤ Rp) (N ε : ℕ)
    (hN : 24 * D.B ≤ N) (hε : 4 * D.ν * Rp ≤ ε) {η : ℝ} (hη : 0 < η) (Unc : Finset ℤ)
    (hUnc : Unc ⊆ D.A i)
    (hbig : η * D.L * D.M ^ 2 < ((O.filter fun o => o.2 i ∈ Unc).card : ℝ)) :
    ∃ B₀ ⊆ Unc, B₀.Nonempty ∧ η * D.M / 3 ≤ B₀.card ∧ ∃ P : Finset ℤ,
      (P.card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
        ∀ a ∈ B₀, ∀ b ∈ B₀, ∃ p ∈ P, a - b - p ∈ shiftBox D.ζ N ε 2 := by
  classical
  have hM := D.one_le_M
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast D.one_le_L
  set O' := O.filter fun o => o.2 i ∈ Unc
  have hO' : ∀ o ∈ O', o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 := fun o ho => hO o (Finset.mem_filter.mp ho).1
  set! Eg := O'.image fun o => (o.2 i, o.2 j)
  have hEsub : Eg ⊆ Unc ×ˢ D.A j := by
    intro e he
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hoO, hoU⟩ := Finset.mem_filter.mp ho
    obtain ⟨hs, hx⟩ := hO o hoO
    exact Finset.mem_product.mpr ⟨hoU, D.mem_A _ hs _ hx j hj⟩
  have hEcard : η * D.M ^ 2 ≤ Eg.card := by
    have h1 := Finset.card_le_mul_card_image (f := fun o => (o.2 i, o.2 j)) O' D.L
      (fun e _ => D.pair_fiber_le O' hO' hi hj hij e)
    have h1' : (O'.card : ℝ) ≤ D.L * Eg.card := by exact_mod_cast h1
    have : η * D.L * D.M ^ 2 ≤ D.L * Eg.card := hbig.le.trans h1'
    nlinarith only [hbig, h1']
  have hUM : (Unc.card : ℝ) ≤ D.M := (by exact_mod_cast Finset.card_le_card hUnc :
    (Unc.card : ℝ) ≤ (D.A i).card).trans (D.card_A i hi)
  obtain ⟨B₀, hB₀U, hB₀card, hpaths⟩ := many_four_paths Unc (D.A j) Eg hEsub
    (by linarith) hUM (D.card_A j hj) hη hEcard
  have hB₀ne : B₀.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < B₀.card := lt_of_lt_of_le (by positivity) hB₀card
    exact_mod_cast this
  refine ⟨B₀, hB₀U, hB₀ne, hB₀card, ?_⟩
  -- edge tuples and colours
  have hch : ∀ e ∈ Eg, ∃ o ∈ O', (o.2 i, o.2 j) = e := fun e he => Finset.mem_image.mp he
  choose! oc hoc hoce using hch
  set! col : ℤ × ℤ → ℤ := fun e => (oc e).2 k
  have hocS : ∀ e ∈ Eg, (oc e).1 ∈ D.S ∧ (oc e).2 ∈ D.E (oc e).1 := fun e he => hO' _ (hoc e he)
  have hoci : ∀ e ∈ Eg, (oc e).2 i = e.1 := fun e he => congrArg Prod.fst (hoce e he)
  have hocj : ∀ e ∈ Eg, (oc e).2 j = e.2 := fun e he => congrArg Prod.snd (hoce e he)
  have hpx : ∀ x y y', (x, y) ∈ Eg → (x, y') ∈ Eg → col (x, y) = col (x, y') → y = y' := by
    intro x y y' h h' hc
    have := D.pair i hi k hk hik _ (hocS _ h).1 _ (hocS _ h').1 _ (hocS _ h).2 _ (hocS _ h').2
      ((hoci _ h).trans (hoci _ h').symm) hc
    have e1 : (oc (x, y)).2 j = y := hocj _ h
    have e2 : (oc (x, y')).2 j = y' := hocj _ h'
    rw [← e1, ← e2, this]
  have hpy : ∀ x x' y, (x, y) ∈ Eg → (x', y) ∈ Eg → col (x, y) = col (x', y) → x = x' := by
    intro x x' y h h' hc
    have := D.pair j hj k hk hjk _ (hocS _ h).1 _ (hocS _ h').1 _ (hocS _ h).2 _ (hocS _ h').2
      ((hocj _ h).trans (hocj _ h').symm) hc
    have e1 : (oc (x, y)).2 i = x := hoci _ h
    have e2 : (oc (x', y)).2 i = x' := hoci _ h'
    rw [← e1, ← e2, this]
  -- the triple and its coefficients
  set T : Finset (Fin 4) := {i, j, k}
  have hT : T ⊆ D.core := by
    intro r hr
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have hT3 : T.card = 3 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
      Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  have hli : i ≠ l := fun h => hl (h ▸ Finset.mem_insert_self i _)
  have hlk : k ≠ l := fun h => hl (h ▸ Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self k)))
  obtain ⟨-, βi, hβi⟩ := roleCoeff_spec hli
  have hβ6 := (abs_cofactor_le hβi).1
  set! q : ℤ × ℤ × ℤ × ℤ → ℤ := fun c =>
    -βi * roleCoeff k l * ((c.1 - c.2.1 + c.2.2.1 - c.2.2.2) / 6)
  set! seq : ℤ → ℤ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ := fun a a' p =>
    (col (a, p.1), col (p.2.1, p.1), col (p.2.1, p.2.2), col (a', p.2.2))
  have hsix : ∀ e ∈ Eg, (6 : ℤ) ∣ col e := fun e he =>
    D.six_dvd _ (hocS e he).1 _ (hocS e he).2 k hk
  -- the path relation
  have hrel : ∀ a ∈ B₀, ∀ a' ∈ B₀, ∀ p ∈ bipFourPaths Unc (D.A j) Eg a a',
      a - a' - q (seq a a' p) ∈ shiftBox D.ζ N ε 1 := by
    intro a _ a' _ p hp
    obtain ⟨y₁, x, y₂⟩ := p
    simp only [bipFourPaths, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨-, e₁, e₂, e₃, e₄⟩ := hp
    have hann : ∀ e ∈ Eg, ∃ n : Fin D.d → ℤ, (∀ r, |(n r : ℝ)| ≤ D.B) ∧
        |((roleCoeff i l * (oc e).2 i + roleCoeff j l * (oc e).2 j +
          roleCoeff k l * (oc e).2 k + 36 * shiftDot n D.ζ : ℤ) : ℝ)| ≤ D.ν * Rp := by
      intro e he
      obtain ⟨n, hn, -, hρ⟩ := D.ann T hT hT3 l hl _ (hocS e he).1 _ (hocS e he).2
      refine ⟨n, hn, ?_⟩
      rw [sum_three hij hik hjk (fun r => roleCoeff r l * (oc e).2 r)] at hρ
      refine hρ.trans ?_
      have hν : 0 ≤ D.ν := by linarith [D.μ_pos, D.μ_le_ν]
      exact mul_le_mul_of_nonneg_left (hRp _ (hoc e he |> fun h => (Finset.mem_filter.mp h).1)) hν
    obtain ⟨n₁, hn₁, hρ₁⟩ := hann _ e₁
    obtain ⟨n₂, hn₂, hρ₂⟩ := hann _ e₂
    obtain ⟨n₃, hn₃, hρ₃⟩ := hann _ e₃
    obtain ⟨n₄, hn₄, hρ₄⟩ := hann _ e₄
    have a₁ : (oc (a, y₁)).2 i = a := hoci _ e₁
    have b₁ : (oc (a, y₁)).2 j = y₁ := hocj _ e₁
    have a₂ : (oc (x, y₁)).2 i = x := hoci _ e₂
    have b₂ : (oc (x, y₁)).2 j = y₁ := hocj _ e₂
    have a₃ : (oc (x, y₂)).2 i = x := hoci _ e₃
    have b₃ : (oc (x, y₂)).2 j = y₂ := hocj _ e₃
    have a₄ : (oc (a', y₂)).2 i = a' := hoci _ e₄
    have b₄ : (oc (a', y₂)).2 j = y₂ := hocj _ e₄
    rw [a₁, b₁] at hρ₁; rw [a₂, b₂] at hρ₂; rw [a₃, b₃] at hρ₃; rw [a₄, b₄] at hρ₄
    set c₁ := (oc (a, y₁)).2 k
    set c₂ := (oc (x, y₁)).2 k
    set c₃ := (oc (x, y₂)).2 k
    set c₄ := (oc (a', y₂)).2 k
    have hσ : (6 : ℤ) ∣ c₁ - c₂ + c₃ - c₄ :=
      ((((hsix _ e₁).sub (hsix _ e₂)).add (hsix _ e₃)).sub (hsix _ e₄))
    obtain ⟨σ', hσ'⟩ := hσ
    have hseq : seq a a' (y₁, x, y₂) = (c₁, c₂, c₃, c₄) := rfl
    rw [hseq]
    set! Nn := n₁ - n₂ + n₃ - n₄
    set! u := a - a' - q (c₁, c₂, c₃, c₄) + 6 * βi * shiftDot Nn D.ζ
    have hqv : q (c₁, c₂, c₃, c₄) = -βi * roleCoeff k l * σ' := by
      simp only [q]; rw [hσ', Int.mul_ediv_cancel_left _ (by norm_num : (6 : ℤ) ≠ 0)]
    have hNn : shiftDot Nn D.ζ = shiftDot n₁ D.ζ - shiftDot n₂ D.ζ + shiftDot n₃ D.ζ -
        shiftDot n₄ D.ζ := by
      simp only [Nn, sub_eq_add_neg, shiftDot_add, shiftDot_neg]
    have hu : roleCoeff i l * u =
        (roleCoeff i l * a + roleCoeff j l * y₁ + roleCoeff k l * c₁ + 36 * shiftDot n₁ D.ζ) -
        (roleCoeff i l * x + roleCoeff j l * y₁ + roleCoeff k l * c₂ + 36 * shiftDot n₂ D.ζ) +
        (roleCoeff i l * x + roleCoeff j l * y₂ + roleCoeff k l * c₃ + 36 * shiftDot n₃ D.ζ) -
        (roleCoeff i l * a' + roleCoeff j l * y₂ + roleCoeff k l * c₄ +
          36 * shiftDot n₄ D.ζ) := by
      simp only [u, hqv, hNn]
      have : roleCoeff i l * (6 * βi) = 36 := by
        rw [← mul_assoc, mul_comm _ 6, mul_assoc, hβi]; norm_num
      linear_combination (shiftDot n₁ D.ζ - shiftDot n₂ D.ζ + shiftDot n₃ D.ζ -
        shiftDot n₄ D.ζ) * this - roleCoeff k l * hσ' + (roleCoeff k l * σ') * hβi
    have hubound : |(u : ℝ)| ≤ ε := by
      have h1 : |((roleCoeff i l * u : ℤ) : ℝ)| ≤ 4 * (D.ν * Rp) := by
        rw [hu]; push_cast
        push_cast at hρ₁ hρ₂ hρ₃ hρ₄
        refine (abs_alt_four_le _ _ _ _).trans ?_
        linarith
      have hα1 : (1 : ℝ) ≤ |(roleCoeff i l : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (abs_cofactor_le hβi).2
      rw [Int.cast_mul, abs_mul] at h1
      nlinarith only [abs_nonneg (u : ℝ), hε, h1, hα1]
    have hNb : ∀ r, |((-βi) * Nn r : ℝ)| ≤ 24 * D.B := by
      intro r
      have hb6 : |(βi : ℝ)| ≤ 6 := by rw [← Int.cast_abs]; exact_mod_cast hβ6
      have hN4 : |(Nn r : ℝ)| ≤ 4 * D.B := by
        simp only [Nn, Pi.sub_apply, Pi.add_apply]; push_cast
        refine (abs_alt_four_le _ _ _ _).trans ?_
        linarith [hn₁ r, hn₂ r, hn₃ r, hn₄ r]
      rw [abs_mul, abs_neg]
      nlinarith only [abs_nonneg (Nn r : ℝ), abs_nonneg (βi : ℝ), hb6, hN4]
    refine mem_shiftBox.mpr ⟨(-βi) • Nn, fun r => ?_, u, ?_, ?_⟩
    · have := hNb r
      have h2 : |((-βi) * Nn r : ℝ)| ≤ (N : ℝ) := this.trans hN
      simp only [Pi.smul_apply, smul_eq_mul, one_mul]
      have : |(((-βi) * Nn r : ℤ) : ℝ)| ≤ ((N : ℕ) : ℝ) := by push_cast; exact h2
      rw [← Int.cast_abs] at this; exact_mod_cast this
    · have : |(u : ℝ)| ≤ ((ε : ℕ) : ℝ) := hubound
      rw [one_mul]; rw [← Int.cast_abs] at this; exact_mod_cast this
    · rw [shiftDot_smul]; simp only [u]; ring
  -- colour sequences
  set! W : ℤ → ℤ → Finset (ℤ × ℤ × ℤ × ℤ) := fun a a' =>
    (bipFourPaths Unc (D.A j) Eg a a').image (seq a a')
  set! κ : ℕ := ⌈η ^ 5 * D.M ^ 3 / 160000⌉₊
  have hκ : ∀ a ∈ B₀, ∀ a' ∈ B₀, κ ≤ (W a a').card := by
    intro a ha a' ha'
    rw [Finset.card_image_of_injOn (bipFourPaths_colors_injOn Unc (D.A j) Eg col hpx hpy a a')]
    exact Nat.ceil_le.mpr (hpaths a ha a' ha')
  set! Cs := D.A k ×ˢ D.A k ×ˢ D.A k ×ˢ D.A k
  have hWCs : ∀ a ∈ B₀, ∀ a' ∈ B₀, W a a' ⊆ Cs := by
    intro a _ a' _ c hc
    obtain ⟨⟨y₁, x, y₂⟩, hp, rfl⟩ := Finset.mem_image.mp hc
    simp only [bipFourPaths, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨-, e₁, e₂, e₃, e₄⟩ := hp
    have hA : ∀ e ∈ Eg, col e ∈ D.A k := fun e he =>
      D.mem_A _ (hocS e he).1 _ (hocS e he).2 k hk
    exact Finset.mem_product.mpr ⟨hA _ e₁, Finset.mem_product.mpr ⟨hA _ e₂,
      Finset.mem_product.mpr ⟨hA _ e₃, hA _ e₄⟩⟩⟩
  have hq' : ∀ a ∈ B₀, ∀ a' ∈ B₀, ∀ c ∈ W a a', a - a' - q c ∈ shiftBox D.ζ N ε 1 := by
    intro a ha a' ha' c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact hrel a ha a' ha' p hp
  have hU : ∀ u ∈ shiftBox D.ζ N ε 1, ∀ v ∈ shiftBox D.ζ N ε 1,
      u - v ∈ shiftBox D.ζ N ε 2 := by
    intro u hu v hv
    have := sub_mem_shiftBox hu hv
    rwa [show (1 : ℕ) + 1 = 2 from rfl] at this
  have hneg : ∀ u ∈ shiftBox D.ζ N ε 2, -u ∈ shiftBox D.ζ N ε 2 :=
    fun u hu => neg_mem_shiftBox hu
  obtain ⟨P, -, hPκ, hPcov⟩ := difference_cover_of_sequences B₀ Cs W hWCs hκ q
    (shiftBox D.ζ N ε 1) (shiftBox D.ζ N ε 2) hq' hU hneg (zero_mem_shiftBox _ _ _ _)
  refine ⟨P, ?_, fun a ha b hb => hPcov (a - b) (Finset.sub_mem_sub ha hb)⟩
  have hκR : η ^ 5 * D.M ^ 3 / 160000 ≤ (κ : ℝ) := Nat.le_ceil _
  have hCs : (Cs.card : ℝ) ≤ D.M ^ 4 := by
    have e : Cs.card = (D.A k).card * ((D.A k).card * ((D.A k).card * (D.A k).card)) := by
      simp only [Cs, Finset.card_product]
    rw [e]; exact card_pow_four_le (D.card_A k hk)
  have hPκR : (P.card : ℝ) * κ ≤ D.M ^ 4 := (by exact_mod_cast hPκ : (P.card : ℝ) * κ ≤
    Cs.card).trans hCs
  exact cover_count_arith hη (by linarith) hPκR hκR

/-- Blueprint lines 2618-2626 (iterated extraction): the incident `i`-labels of a family of
occurrences are covered, apart from occurrences of mass at most `η L M²`, by pairwise disjoint
subsets `B ⊆ A_i`, each with `|B| ≥ η M / 3` and with a difference cover by at most
`160000 η^{-5} M` translates of `U(2)` (`eq:two-cover-counts`); there are at most `3/η` of
them. -/
theorem cover_family (O : Finset (ℤ × (Fin 4 → ℤ)))
    (hO : ∀ o ∈ O, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) {i j k l : Fin 4} (hi : i ∈ D.core)
    (hj : j ∈ D.core) (hk : k ∈ D.core) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hl : l ∉ ({i, j, k} : Finset (Fin 4))) {Rp : ℝ} (hRp : ∀ o ∈ O, D.R o.1 ≤ Rp) (N ε : ℕ)
    (hN : 24 * D.B ≤ N) (hε : 4 * D.ν * Rp ≤ ε) {η : ℝ} (hη : 0 < η) :
    ∃ 𝓑 : Finset (Finset ℤ), (∀ B ∈ 𝓑, B ⊆ D.A i) ∧
      (∀ B ∈ 𝓑, ∀ B' ∈ 𝓑, B ≠ B' → Disjoint B B') ∧ (∀ B ∈ 𝓑, η * D.M / 3 ≤ B.card) ∧
      (∀ B ∈ 𝓑, ∃ P : Finset ℤ, (P.card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
        ∀ a ∈ B, ∀ b ∈ B, ∃ p ∈ P, a - b - p ∈ shiftBox D.ζ N ε 2) ∧
      ((O.filter fun o => ∀ B ∈ 𝓑, o.2 i ∉ B).card : ℝ) ≤ η * D.L * D.M ^ 2 := by
  classical
  have hM := D.one_le_M
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast D.one_le_L
  suffices h : ∀ n : ℕ, ∀ Unc : Finset ℤ, Unc.card ≤ n → Unc ⊆ D.A i →
      ∃ 𝓑 : Finset (Finset ℤ), (∀ B ∈ 𝓑, B ⊆ Unc) ∧
        (∀ B ∈ 𝓑, ∀ B' ∈ 𝓑, B ≠ B' → Disjoint B B') ∧ (∀ B ∈ 𝓑, η * D.M / 3 ≤ B.card) ∧
        (∀ B ∈ 𝓑, ∃ P : Finset ℤ, (P.card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
          ∀ a ∈ B, ∀ b ∈ B, ∃ p ∈ P, a - b - p ∈ shiftBox D.ζ N ε 2) ∧
        ((O.filter fun o => o.2 i ∈ Unc ∧ ∀ B ∈ 𝓑, o.2 i ∉ B).card : ℝ) ≤
          η * D.L * D.M ^ 2 by
    obtain ⟨𝓑, h1, h2, h3, h4, h5⟩ := h _ (D.A i) le_rfl subset_rfl
    refine ⟨𝓑, h1, h2, h3, h4, le_trans ?_ h5⟩
    refine Nat.cast_le.mpr (Finset.card_le_card fun o ho => ?_)
    obtain ⟨hoO, hB⟩ := Finset.mem_filter.mp ho
    obtain ⟨hs, hx⟩ := hO o hoO
    exact Finset.mem_filter.mpr ⟨hoO, D.mem_A _ hs _ hx i hi, hB⟩
  intro n
  induction n with
  | zero =>
    intro Unc hU _
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hU)]
    refine ⟨∅, by simp, by simp, by simp, by simp, ?_⟩
    rw [Finset.filter_eq_empty_iff.mpr (fun o _ => by simp)]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  | succ n ih =>
    intro Unc hU hUA
    by_cases hbig : η * D.L * D.M ^ 2 < ((O.filter fun o => o.2 i ∈ Unc).card : ℝ)
    · obtain ⟨B₀, hB₀U, hB₀ne, hB₀card, hB₀cov⟩ := D.extract_cover_subset O hO hi hj hk hij
        hik hjk hl hRp N ε hN hε hη Unc hUA hbig
      have hcard : (Unc \ B₀).card ≤ n := by
        rw [Finset.card_sdiff_of_subset hB₀U]
        have := hB₀ne.card_pos
        omega
      obtain ⟨𝓑, h1, h2, h3, h4, h5⟩ := ih (Unc \ B₀) hcard (Finset.sdiff_subset.trans hUA)
      have hB₀notin : B₀ ∉ 𝓑 := by
        intro h
        obtain ⟨x, hx⟩ := hB₀ne
        exact (Finset.mem_sdiff.mp (h1 B₀ h hx)).2 hx
      refine ⟨insert B₀ 𝓑, ?_, ?_, ?_, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hB₀U
        · exact (h1 B hB).trans Finset.sdiff_subset
      · intro B hB B' hB' hne
        rcases Finset.mem_insert.mp hB with hBx | hBm <;>
          rcases Finset.mem_insert.mp hB' with hB'x | hB'm
        · exact absurd (hBx.trans hB'x.symm) hne
        · rw [hBx]; exact Finset.disjoint_of_subset_right (h1 B' hB'm) Finset.disjoint_sdiff
        · rw [hB'x]; exact Finset.disjoint_of_subset_left (h1 B hBm) Finset.sdiff_disjoint
        · exact h2 B hBm B' hB'm hne
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hB₀card
        · exact h3 B hB
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hB₀cov
        · exact h4 B hB
      · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun o ho => ?_)) h5
        obtain ⟨hoO, hoU, hB⟩ := Finset.mem_filter.mp ho
        refine Finset.mem_filter.mpr ⟨hoO, Finset.mem_sdiff.mpr ⟨hoU, hB B₀
          (Finset.mem_insert_self _ _)⟩, fun B hB' => hB B (Finset.mem_insert_of_mem hB')⟩
    · push Not at hbig
      refine ⟨∅, by simp, by simp, by simp, by simp, le_trans ?_ hbig⟩
      exact Nat.cast_le.mpr (Finset.card_le_card fun o ho => by
        obtain ⟨hoO, hoU, -⟩ := Finset.mem_filter.mp ho
        exact Finset.mem_filter.mpr ⟨hoO, hoU⟩)

/-- Disjoint cover subsets of `A_i`, each of size at least `η M / 3`, number at most `3/η`. -/
theorem cover_family_card {𝓑 : Finset (Finset ℤ)} {i : Fin 4} (hi : i ∈ D.core)
    (h1 : ∀ B ∈ 𝓑, B ⊆ D.A i) (h2 : ∀ B ∈ 𝓑, ∀ B' ∈ 𝓑, B ≠ B' → Disjoint B B') {η : ℝ}
    (hη : 0 < η) (h3 : ∀ B ∈ 𝓑, η * D.M / 3 ≤ B.card) : (𝓑.card : ℝ) ≤ 3 / η := by
  classical
  have hM := D.one_le_M
  have hU : (𝓑.biUnion id).card = ∑ B ∈ 𝓑, B.card :=
    Finset.card_biUnion fun B hB B' hB' hne => h2 B hB B' hB' hne
  have hsub : 𝓑.biUnion id ⊆ D.A i := Finset.biUnion_subset.mpr fun B hB => h1 B hB
  have hle : (∑ B ∈ 𝓑, (B.card : ℝ)) ≤ D.M := by
    have := Finset.card_le_card hsub
    rw [hU] at this
    exact (by exact_mod_cast this : (∑ B ∈ 𝓑, (B.card : ℝ)) ≤ (D.A i).card).trans (D.card_A i hi)
  have : (𝓑.card : ℝ) * (η * D.M / 3) ≤ D.M := by
    calc (𝓑.card : ℝ) * (η * D.M / 3) = ∑ _B ∈ 𝓑, η * D.M / 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ B ∈ 𝓑, (B.card : ℝ) := Finset.sum_le_sum h3
      _ ≤ D.M := hle
  rw [le_div_iff₀ hη]
  have hM0 : 0 < D.M := by linarith
  nlinarith

end SparseCountData

section MassRanges
variable {α : Type*}

/-! ### Three mass ranges and separated middle scales (blueprint lines 2642-2646) -/

/-- The mass of scales at least `c`. -/
def upperMass (C : Finset (ℤ × α)) (c : ℤ) : ℕ := (C.filter fun o => c ≤ o.1).card

theorem upperMass_split (C : Finset (ℤ × α)) (c : ℤ) :
    upperMass C c = (C.filter fun o => o.1 = c).card + (C.filter fun o => c + 1 ≤ o.1).card := by
  classical
  unfold upperMass
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun o _ h h' => by omega)]
  congr 1; ext o; simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h2 with h | h
    · exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr ⟨h1, by omega⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2.ge⟩
    · exact ⟨h1, by omega⟩

/-- Above the largest scale with upper mass at least `θ`, the upper mass is below `θ`. -/
theorem upperMass_above_max (C : Finset (ℤ × α)) {θ : ℝ} (hθ : 0 < θ) (c : ℤ)
    (hc : ∀ s ∈ C.image Prod.fst, c < s → (upperMass C s : ℝ) < θ) :
    ((C.filter fun o => c + 1 ≤ o.1).card : ℝ) < θ := by
  classical
  set Up := (C.filter fun o => c + 1 ≤ o.1)
  rcases Up.eq_empty_or_nonempty with h | hne
  · rw [h]; simpa using hθ
  set s₀ := (Up.image Prod.fst).min' (hne.image _)
  have hs₀ : s₀ ∈ Up.image Prod.fst := Finset.min'_mem _ _
  obtain ⟨o₀, ho₀, hos⟩ := Finset.mem_image.mp hs₀
  obtain ⟨ho₀C, ho₀c⟩ := Finset.mem_filter.mp ho₀
  have heq : Up = C.filter fun o => s₀ ≤ o.1 := by
    ext o
    simp only [Up, Finset.mem_filter]
    constructor
    · rintro ⟨hoC, ho⟩
      exact ⟨hoC, Finset.min'_le _ _ (Finset.mem_image.mpr ⟨o, Finset.mem_filter.mpr ⟨hoC, ho⟩,
        rfl⟩)⟩
    · rintro ⟨hoC, ho⟩; exact ⟨hoC, by omega⟩
  rw [heq]
  exact hc s₀ (Finset.mem_image.mpr ⟨o₀, ho₀C, hos⟩) (by omega)

/-- Blueprint lines 2642-2643 (three mass ranges): if every scale carries mass at most `m₀` and
the total mass is at least `12 m₀`, there are cuts `c₂ < c₁` such that the first range (scales
`≥ c₁`) has at least a third of the mass and the middle (`c₂ ≤ s < c₁`) and last (`s < c₂`)
ranges at least a quarter each. -/
theorem mass_ranges (C : Finset (ℤ × α)) {m₀ : ℝ}
    (hm : ∀ s, ((C.filter fun o => o.1 = s).card : ℝ) ≤ m₀) (hC : 12 * m₀ ≤ C.card)
    (hCpos : 0 < C.card) :
    ∃ c₁ c₂ : ℤ, c₂ < c₁ ∧ (C.card : ℝ) / 3 ≤ (C.filter fun o => c₁ ≤ o.1).card ∧
      (C.card : ℝ) / 4 ≤ (C.filter fun o => c₂ ≤ o.1 ∧ o.1 < c₁).card ∧
      (C.card : ℝ) / 4 ≤ (C.filter fun o => o.1 < c₂).card := by
  classical
  have hCR : (0 : ℝ) < C.card := by exact_mod_cast hCpos
  set W := C.image Prod.fst
  have hWne : W.Nonempty := (Finset.card_pos.mp hCpos).image _
  have hmin : (upperMass C (W.min' hWne) : ℝ) = C.card := by
    unfold upperMass
    congr 2
    exact Finset.filter_true_of_mem fun o ho =>
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ ho)
  -- the largest scale with upper mass at least `θ`
  have hcut : ∀ θ : ℝ, 0 < θ → θ ≤ C.card → ∃ c ∈ W, θ ≤ upperMass C c ∧
      (upperMass C c : ℝ) < θ + m₀ ∧ ∀ s ∈ W, θ ≤ upperMass C s → s ≤ c := by
    intro θ hθ hθC
    set Set := W.filter fun s => θ ≤ (upperMass C s : ℝ)
    have hSne : Set.Nonempty :=
      ⟨W.min' hWne, Finset.mem_filter.mpr ⟨Finset.min'_mem _ _, by rw [hmin]; exact hθC⟩⟩
    set c := Set.max' hSne
    have hcS : c ∈ Set := Finset.max'_mem _ _
    obtain ⟨hcW, hcθ⟩ := Finset.mem_filter.mp hcS
    refine ⟨c, hcW, hcθ, ?_, fun s hs hθs => Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hs, hθs⟩)⟩
    have habove := upperMass_above_max C hθ c fun s hs hcs => by
      by_contra h
      push Not at h
      exact absurd (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hs, h⟩)) (not_le.mpr hcs)
    rw [upperMass_split]
    push_cast
    linarith [hm c]
  obtain ⟨c₁, hc₁W, hc₁θ, hc₁up, hc₁max⟩ := hcut (C.card / 3) (by positivity) (by linarith)
  obtain ⟨c₂, hc₂W, hc₂θ, hc₂up, -⟩ := hcut (2 * C.card / 3) (by positivity) (by linarith)
  have hc21 : c₂ < c₁ := by
    have hle : c₂ ≤ c₁ := hc₁max c₂ hc₂W (by linarith)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso; rw [h] at hc₂θ; linarith
  have hsplit : (C.filter fun o => c₂ ≤ o.1).card =
      (C.filter fun o => c₂ ≤ o.1 ∧ o.1 < c₁).card + (C.filter fun o => c₁ ≤ o.1).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun o _ h h' => by omega)]
    congr 1; ext o; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : o.1 < c₁
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨h1, by omega⟩
  have hsplit2 : C.card = (C.filter fun o => o.1 < c₂).card +
      (C.filter fun o => c₂ ≤ o.1).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun o _ h h' => by omega)]
    congr 1; ext o; simp only [Finset.mem_filter, Finset.mem_union]; constructor
    · intro h; by_cases h' : o.1 < c₂
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have e1 : ((C.filter fun o => c₂ ≤ o.1).card : ℝ) =
      (C.filter fun o => c₂ ≤ o.1 ∧ o.1 < c₁).card + (C.filter fun o => c₁ ≤ o.1).card := by
    exact_mod_cast hsplit
  have e2 : (C.card : ℝ) = (C.filter fun o => o.1 < c₂).card +
      (C.filter fun o => c₂ ≤ o.1).card := by exact_mod_cast hsplit2
  unfold upperMass at hc₁θ hc₁up hc₂θ hc₂up
  refine ⟨c₁, c₂, hc21, hc₁θ, ?_, ?_⟩ <;> linarith

/-- Blueprint lines 2645-2646 (separated middle scales): among scales above `s_F`, those at
least `g` above `s_F` lying in one residue class modulo `g` are pairwise at least `g` apart,
and there are at least `(|W| - g)/g` of them. -/
theorem residue_selection (Wm : Finset ℤ) (sF : ℤ) (hWm : ∀ s ∈ Wm, sF < s) {g : ℕ}
    (hg : 1 ≤ g) : ∃ V ⊆ Wm, (∀ v ∈ V, sF + g ≤ v) ∧ (∀ v ∈ V, ∀ v' ∈ V, v' < v → v' + g ≤ v) ∧
      (Wm.card : ℝ) ≤ g * V.card + g := by
  classical
  set Wm' := Wm.filter fun s => sF + g ≤ s
  have hlow : Wm.card ≤ Wm'.card + g := by
    have hsub : Wm.filter (fun s => ¬ (sF + g ≤ s)) ⊆ Finset.Ioo sF (sF + g) := by
      intro s hs
      obtain ⟨hsW, hs'⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_Ioo.mpr ⟨hWm s hsW, by omega⟩
    have h3 : (Wm.filter (fun s => ¬ (sF + g ≤ s))).card ≤ g := by
      have := Finset.card_le_card hsub
      rw [Int.card_Ioo] at this
      omega
    have h2 : Wm'.card + (Wm.filter (fun s => ¬ (sF + g ≤ s))).card = Wm.card :=
      Finset.card_filter_add_card_filter_not _
    omega
  have hgpos : (0 : ℤ) < g := by exact_mod_cast hg
  have hmaps : ∀ s ∈ Wm', s % (g : ℤ) ∈ Finset.Ico (0 : ℤ) g := fun s _ =>
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hgpos.ne', Int.emod_lt_of_pos _ hgpos⟩
  have hIco : (Finset.Ico (0 : ℤ) g).card = g := by simp
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨r, -, hr⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := fun s => s % (g : ℤ)) hmaps ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, hgpos⟩⟩
    (b := (Wm'.card : ℝ) / g) (by rw [hIco, nsmul_eq_mul]; field_simp; rfl)
  refine ⟨Wm'.filter fun s => s % (g : ℤ) = r, (Finset.filter_subset _ _).trans
    (Finset.filter_subset _ _), fun v hv => (Finset.mem_filter.mp
      (Finset.mem_filter.mp hv).1).2, fun v hv v' hv' hlt => ?_, ?_⟩
  · have h1 := (Finset.mem_filter.mp hv).2
    have h2 := (Finset.mem_filter.mp hv').2
    have hdvd : (g : ℤ) ∣ v - v' := Int.ModEq.dvd (h2.trans h1.symm)
    obtain ⟨c, hc⟩ := hdvd
    have hc1 : 1 ≤ c := by
      by_contra h
      push Not at h
      nlinarith only [hlt, hc, h]
    nlinarith
  · have h1 : (Wm.card : ℝ) ≤ Wm'.card + g := by exact_mod_cast hlow
    have h2 : (Wm'.card : ℝ) ≤ g * (Wm'.filter fun s => s % (g : ℤ) = r).card := by
      rw [div_le_iff₀ hgR] at hr; linarith
    linarith

end MassRanges

namespace SparseCountData
variable (D : SparseCountData)

/-- A fixed label in one core role has at most `L M` occurrences. -/
theorem label_fiber_le (O : Finset (ℤ × (Fin 4 → ℤ))) (hO : ∀ o ∈ O, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1)
    {r : Fin 4} (hr : r ∈ D.core) (a : ℤ) :
    ((O.filter fun o => o.2 r = a).card : ℝ) ≤ D.L * D.M := by
  classical
  obtain ⟨r', hr', -, -, hrr', -, -⟩ := D.exists_two_other hr
  set O' := O.filter fun o => o.2 r = a
  have hO' : ∀ o ∈ O', o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 := fun o ho => hO o (Finset.mem_filter.mp ho).1
  have h1 := Finset.card_le_mul_card_image (f := fun o => o.2 r') O' D.L (fun b _ => by
    have := D.pair_fiber_le O' hO' hr hr' hrr' (a, b)
    refine le_trans (Finset.card_le_card fun o ho => ?_) this
    obtain ⟨hoO', hob⟩ := Finset.mem_filter.mp ho
    exact Finset.mem_filter.mpr ⟨hoO', by rw [(Finset.mem_filter.mp hoO').2, hob]⟩)
  have h2 : (O'.image fun o => o.2 r') ⊆ D.A r' := by
    intro b hb
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hb
    exact D.mem_A _ (hO' o ho).1 _ (hO' o ho).2 r' hr'
  have h3 : ((O'.image fun o => o.2 r').card : ℝ) ≤ D.M :=
    (by exact_mod_cast Finset.card_le_card h2 : _ ≤ ((D.A r').card : ℝ)).trans (D.card_A r' hr')
  calc (O'.card : ℝ) ≤ D.L * (O'.image fun o => o.2 r').card := by exact_mod_cast h1
    _ ≤ D.L * D.M := by gcongr

/-- Occurrences with a common projection to three distinct core roles number at most `L`. -/
theorem proj_fiber_le (O : Finset (ℤ × (Fin 4 → ℤ))) (hO : ∀ o ∈ O, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1)
    (e : Fin 3 → Fin 4) (he : Function.Injective e) (heC : ∀ j, e j ∈ D.core)
    (f : Fin 3 → ℤ) : (O.filter fun o => (fun j => o.2 (e j)) = f).card ≤ D.L := by
  classical
  refine le_trans (Finset.card_le_card fun o ho => ?_)
    (D.pair_fiber_le O hO (heC 0) (heC 1) (he.ne (by decide)) (f 0, f 1))
  obtain ⟨hoO, hof⟩ := Finset.mem_filter.mp ho
  refine Finset.mem_filter.mpr ⟨hoO, ?_⟩
  rw [← hof]

end SparseCountData

/-- Blueprint lines 2696-2698 (the mass bound of one combination): from the slab count
`|V||F| ≤ (2K₁M/b₀)² b₀ (2K₁M/b₁)² b₁ (2K₁M/b₂)³` with anchor sizes `b_j ≥ ρM/(3L)`,
`|F| ≥ ρM²/(4L)`, `|V| ≥ ρ/(8gδ)` and `ρ ≤ L`, one gets `ρ¹⁰ ≤ 10⁶ δ g K₁⁷ L⁹`. -/
theorem combination_arith {ρ M L K₁ δ g V F P₀ P₁ P₂ b₀ b₁ b₂ : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hg : 1 ≤ g) (hK : 0 ≤ K₁)
    (hb₀ : ρ * M / (3 * L) ≤ b₀) (hb₁ : ρ * M / (3 * L) ≤ b₁) (hb₂ : ρ * M / (3 * L) ≤ b₂)
    (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hP₀K : P₀ ≤ K₁ * M) (hP₁K : P₁ ≤ K₁ * M) (hP₂K : P₂ ≤ K₁ * M)
    (hV : ρ / (8 * g * δ) ≤ V) (hF : ρ * M ^ 2 / (4 * L) ≤ F)
    (hcount : V * F ≤ ((2 * P₀ / b₀) ^ 2 * b₀) * ((2 * P₁ / b₁) ^ 2 * b₁) * (2 * P₂ / b₂) ^ 3)
    (hρL : ρ ≤ L) : ρ ^ 10 ≤ 10 ^ 6 * δ * g * K₁ ^ 7 * L ^ 9 := by
  have hc : 0 < ρ * M / (3 * L) := by positivity
  have hb₀p : 0 < b₀ := hc.trans_le hb₀
  have hb₁p : 0 < b₁ := hc.trans_le hb₁
  have hb₂p : 0 < b₂ := hc.trans_le hb₂
  -- upper bound of the count
  have e1 : (2 * P₀ / b₀) ^ 2 * b₀ = 4 * P₀ ^ 2 / b₀ := by field_simp; ring
  have e2 : (2 * P₁ / b₁) ^ 2 * b₁ = 4 * P₁ ^ 2 / b₁ := by field_simp; ring
  have u0 : 4 * P₀ ^ 2 / b₀ ≤ 4 * (K₁ * M) ^ 2 / (ρ * M / (3 * L)) := by
    gcongr
  have u1 : 4 * P₁ ^ 2 / b₁ ≤ 4 * (K₁ * M) ^ 2 / (ρ * M / (3 * L)) := by
    gcongr
  have u2 : (2 * P₂ / b₂) ^ 3 ≤ (2 * (K₁ * M) / (ρ * M / (3 * L))) ^ 3 := by
    gcongr
  have hup : V * F ≤ 4 * (K₁ * M) ^ 2 / (ρ * M / (3 * L)) * (4 * (K₁ * M) ^ 2 /
      (ρ * M / (3 * L))) * (2 * (K₁ * M) / (ρ * M / (3 * L))) ^ 3 := by
    rw [e1, e2] at hcount
    refine hcount.trans ?_
    have h0 : 0 ≤ 4 * P₀ ^ 2 / b₀ := by positivity
    have h1 : 0 ≤ 4 * P₁ ^ 2 / b₁ := by positivity
    have h2 : 0 ≤ (2 * P₂ / b₂) ^ 3 := by positivity
    gcongr
  have hlow : ρ / (8 * g * δ) * (ρ * M ^ 2 / (4 * L)) ≤ V * F := by
    have hVp : 0 ≤ V := le_trans (by positivity) hV
    exact mul_le_mul hV hF (by positivity) hVp
  have key := hlow.trans hup
  -- simplify: ρ² M²/(32 g δ L) ≤ 31104 K₁⁷ L⁵ M²/ρ⁵
  have hsimp : 4 * (K₁ * M) ^ 2 / (ρ * M / (3 * L)) * (4 * (K₁ * M) ^ 2 /
      (ρ * M / (3 * L))) * (2 * (K₁ * M) / (ρ * M / (3 * L))) ^ 3 =
      31104 * K₁ ^ 7 * L ^ 5 * M ^ 2 / ρ ^ 5 := by
    field_simp; ring
  rw [hsimp] at key
  have hl : ρ / (8 * g * δ) * (ρ * M ^ 2 / (4 * L)) = ρ ^ 2 * M ^ 2 / (32 * g * δ * L) := by
    field_simp; ring
  rw [hl, div_le_div_iff₀ (by positivity) (by positivity)] at key
  have h7 : ρ ^ 7 ≤ 995328 * δ * g * K₁ ^ 7 * L ^ 6 := by
    have hM2 : 0 < M ^ 2 := by positivity
    have : ρ ^ 7 * M ^ 2 ≤ 995328 * δ * g * K₁ ^ 7 * L ^ 6 * M ^ 2 := by nlinarith only [key]
    exact le_of_mul_le_mul_right this hM2
  have hρ3 : ρ ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hρ.le hρL 3
  calc ρ ^ 10 = ρ ^ 7 * ρ ^ 3 := by ring
    _ ≤ (995328 * δ * g * K₁ ^ 7 * L ^ 6) * L ^ 3 := by
        gcongr
    _ ≤ 10 ^ 6 * δ * g * K₁ ^ 7 * L ^ 9 := by
        have : 0 ≤ δ * g * K₁ ^ 7 * L ^ 9 := by positivity
        nlinarith only [this]

namespace SparseCountData
variable (D : SparseCountData)

theorem card_le_mul_card_image_real {β γ : Type*} [DecidableEq γ] (s : Finset β) (f : β → γ)
    (c : ℝ) (h : ∀ a ∈ s.image f, ((s.filter fun x => f x = a).card : ℝ) ≤ c) :
    (s.card : ℝ) ≤ c * (s.image f).card := by
  rw [Finset.card_eq_sum_card_image f s]
  push_cast
  calc ∑ a ∈ s.image f, ((s.filter fun x => f x = a).card : ℝ) ≤ ∑ _a ∈ s.image f, c :=
        Finset.sum_le_sum h
    _ = c * (s.image f).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The annular witnesses of `ann` for a triple enumerated by an injection `e`. -/
theorem ann_triple (e : Fin 3 → Fin 4) (he : Function.Injective e) (heC : ∀ j, e j ∈ D.core)
    {l : Fin 4} (hl : ∀ j, e j ≠ l) {s : ℤ} (hs : s ∈ D.S) {x : Fin 4 → ℤ} (hx : x ∈ D.E s) :
    ∃ n : Fin D.d → ℤ, (∀ r, |(n r : ℝ)| ≤ D.B) ∧
      D.μ * D.R s ≤ |(tripleResidual D.ζ (fun j => roleCoeff (e j) l) (fun j => x (e j)) n : ℝ)| ∧
      |(tripleResidual D.ζ (fun j => roleCoeff (e j) l) (fun j => x (e j)) n : ℝ)| ≤
        D.ν * D.R s := by
  classical
  set T := Finset.univ.image e
  have hT : T ⊆ D.core := by
    intro r hr; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hr; exact heC j
  have hT3 : T.card = 3 := by
    rw [Finset.card_image_of_injective _ he]; rfl
  have hlT : l ∉ T := by
    intro h; obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h; exact hl j hj
  obtain ⟨n, hn, h1, h2⟩ := D.ann T hT hT3 l hlT s hs x hx
  have hsum : ∑ r ∈ T, roleCoeff r l * x r = ∑ j, roleCoeff (e j) l * x (e j) :=
    Finset.sum_image fun a _ b _ h => he h
  refine ⟨n, hn, ?_, ?_⟩
  · unfold tripleResidual; rw [← hsum]; exact h1
  · unfold tripleResidual; rw [← hsum]; exact h2



end SparseCountData
end TrilinearHT.Auto
end
