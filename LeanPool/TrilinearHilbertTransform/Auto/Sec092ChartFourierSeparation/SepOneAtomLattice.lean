/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec092ChartFourierSeparation.SplitFourierExpansion

/-!
# Trilinear Hilbert transform: sep_one_atom_lattice
-/

@[expose] public section

section
open scoped FourierTransform
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform

open scoped Classical in
private def SepOneAtomLatticeHfsumStatement : Prop :=
  ∀ (d : ℕ)
    (χ : (Fin d → ℝ) → ℂ)
    (H : ℝ)
    (_ : ∀ (w : Fin d → ℝ), χ w ≠ (0 : ℂ) → ∀ (l : Fin d), |w l| ≤ H)
    (C : Matrix (Fin d) (Fin d) ℚ)
    (θ : Fin d → ℝ)
    (i : ℤ)
    (a : ℤ)
    (x : ℝ)
    (t : ℝ),
  let u : ℤ → Fin d → ℝ :=
    fun (j : ℤ) (l : Fin d) => θ l * (x + (↑j : ℝ) * t)
  let ut : Fin d → ℝ :=
    fun (l : Fin d) => θ l * t
  let Ki : ℕ :=
    ⌈H + (1 : ℝ) + |(↑(i - a) : ℝ)|⌉₊
  let ui : Fin d → ℝ :=
    u i
  let ua : Fin d → ℝ :=
    u a
  ∀ (_ : ui = ua + (↑(i - a) : ℝ) • ut),
  let f : (Fin d → ℤ) → ℂ :=
    fun (n : Fin d → ℤ) => χ (ui - fun (l : Fin d) => (↑(n l) : ℝ)) * (↑((𝐞 : ℝ →
      Circle) (chartMatrixPhase C ui (ui - fun (l : Fin d) => (↑(n l) : ℝ)))) : ℂ)
  ∀ (_ : f = fun (n : Fin d → ℤ) => χ (ui - fun (l : Fin d) => (↑(n l) : ℝ)) * (↑((𝐞 : ℝ →
      Circle) (chartMatrixPhase C ui (ui - fun (l : Fin d) => (↑(n l) : ℝ)))) : ℂ)),
  let Bn : Finset (Fin d → ℤ) :=
    chartLatticeBox H ui
  ∀ (_ : ∀ n ∉ Bn, f n = (0 : ℂ))
    (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (_ : ∀ (l : Fin d), |ua l - (↑(D.1 l) : ℝ)| ≤ (3 / 4 : ℝ))
    (_ : ∀ (l : Fin d), |ut l - (↑(D.2.2 l) : ℝ)| ≤ (3 / 4 : ℝ)),
  (∑ x ∈ slowValueBox d Ki, f fun (l : Fin d) => D.1 l + (i - a) * D.2.2 l + x l) = ∑
    n ∈ Bn, f n


open scoped Classical in
private def SepOneAtomLatticeStage1Statement : Prop :=
  ∀ (d : ℕ)
    (χ : (Fin d → ℝ) → ℂ)
    (H : ℝ)
    (_ : ∀ (w : Fin d → ℝ), χ w ≠ (0 : ℂ) → ∀ (l : Fin d), |w l| ≤ H)
    (ψ : ℝ → ℝ)
    (_ : ∀ (x : ℝ), |x| ≤ (1 : ℝ) → ψ x = (1 : ℝ))
    (_ : ∀ (x : ℝ), (2 : ℝ) ≤ |x| → ψ x = (0 : ℝ))
    (C : Matrix (Fin d) (Fin d) ℚ)
    (θ : Fin d → ℝ)
    (i : ℤ)
    (a : ℤ)
    (b : ℤ)
    (x : ℝ)
    (t : ℝ),
  let u : ℤ → Fin d → ℝ :=
    fun (j : ℤ) (l : Fin d) => θ l * (x + (↑j : ℝ) * t)
  let ut : Fin d → ℝ :=
    fun (l : Fin d) => θ l * t
  let Ki : ℕ :=
    ⌈H + (1 : ℝ) + |(↑(i - a) : ℝ)|⌉₊
  let Kb : ℕ :=
    ⌈(2 : ℝ) + |(↑(b - a) : ℝ)|⌉₊
  let ui : Fin d → ℝ :=
    u i
  let ua : Fin d → ℝ :=
    u a
  let ub : Fin d → ℝ :=
    u b
  ∀ (_ : ui = ua + (↑(i - a) : ℝ) • ut)
    (_ : ub = ua + (↑(b - a) : ℝ) • ut),
  let f : (Fin d → ℤ) → ℂ :=
    fun (n : Fin d → ℤ) => χ (ui - fun (l : Fin d) => (↑(n l) : ℝ)) * (↑((𝐞 : ℝ →
      Circle) (chartMatrixPhase C ui (ui - fun (l : Fin d) => (↑(n l) : ℝ)))) : ℂ)
  ∀ (_ : f = fun (n : Fin d → ℤ) => χ (ui - fun (l : Fin d) => (↑(n l) : ℝ)) * (↑((𝐞 : ℝ →
      Circle) (chartMatrixPhase C ui (ui - fun (l : Fin d) => (↑(n l) : ℝ)))) : ℂ)),
  let Bn : Finset (Fin d → ℤ) :=
    chartLatticeBox H ui
  ∀ (_ : ∀ n ∉ Bn, f n = (0 : ℂ)),
  let Ppro : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → ℂ :=
    fun (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) => sepPartition (ua - fun (l : Fin
      d) => (↑(D.1 l) : ℝ)) * sepPartition (ub - fun (l : Fin d) => (↑(D.2.1 l) : ℝ)) *
      sepPartition (ut - fun (l : Fin d) => (↑(D.2.2 l) : ℝ))
  ∀ (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (_ : sepPartition (ut - fun (l : Fin d) => (↑(D.2.2 l) : ℝ)) ≠ (0 : ℂ))
    (_ : ∀ (l : Fin d), |ua l - (↑(D.1 l) : ℝ)| ≤ (3 / 4 : ℝ))
    (_ : ∀ (l : Fin d), |ub l - (↑(D.2.1 l) : ℝ)| ≤ (3 / 4 : ℝ)),
  Ppro D * ∑ n ∈ Bn, f n = ∑ x ∈ slowValueBox d Ki, ∑ x_1 ∈ slowValueBox d Kb, Ppro D
    * ((f fun (l : Fin d) => D.1 l + (i - a) * D.2.2 l + x l) * tensorCutoff ψ (1 / 3
    : ℝ) fun (l : Fin d) => (↑(D.2.1 l - D.1 l - (b - a) * D.2.2 l - x_1 l) : ℝ))




private theorem sep_one_atom_lattice_hfsum : SepOneAtomLatticeHfsumStatement := by
  classical
  intro d χ H hχ C θ i a x t u ut Ki ui ua hrel_i f hf Bn hfBn D ba bt
  have hi' (l : Fin d) : ui l = ua l + ((i : ℝ) - a) * ut l := by
    have := congrFun hrel_i l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    push_cast at this
    linarith
  have hzero : ∀ x ∉ slowValueBox d Ki, f (fun l => D.1 l + (i - a) * D.2.2 l + x l) = 0 := by
    intro x hx
    by_contra h
    apply hx
    rw [mem_slowValueBox]
    intro l
    have hχn : χ (ui - fun l => ((D.1 l + (i - a) * D.2.2 l + x l : ℤ) : ℝ)) ≠ 0 := by
      intro h0; exact h (by simp only [hf]; rw [h0, zero_mul])
    have h1 := hχ _ hχn l
    simp only [Pi.sub_apply] at h1
    push_cast at h1
    have h2 : |((x l : ℤ) : ℝ)| ≤ H + 1 + |((i - a : ℤ) : ℝ)| := by
      have e : ((x l : ℤ) : ℝ) = ((ua l - D.1 l) + ((i : ℝ) - a) * (ut l - D.2.2 l)) -
          (ui l - (D.1 l + ((i : ℝ) - a) * D.2.2 l + x l)) := by rw [hi']; ring
      rw [e]
      have h3 := abs_sub ((ua l - D.1 l) + ((i : ℝ) - a) * (ut l - D.2.2 l))
        (ui l - (D.1 l + ((i : ℝ) - a) * D.2.2 l + x l))
      have h4 := abs_add_le (ua l - D.1 l) (((i : ℝ) - a) * (ut l - D.2.2 l))
      rw [abs_mul] at h4
      have h5 : |(i : ℝ) - a| * |ut l - D.2.2 l| ≤ |(i : ℝ) - a| * (3 / 4) :=
        mul_le_mul_of_nonneg_left (bt l) (abs_nonneg _)
      have h6 : |((i - a : ℤ) : ℝ)| = |(i : ℝ) - a| := by push_cast; rfl
      rw [h6]
      have h7 := abs_nonneg ((i : ℝ) - a)
      linarith [ba l]
    have h8 : H + 1 + |((i - a : ℤ) : ℝ)| ≤ Ki := Nat.le_ceil _
    exact_mod_cast h2.trans h8
  have e1 : (∑' x : Fin d → ℤ, f (fun l => D.1 l + (i - a) * D.2.2 l + x l)) =
      ∑ x ∈ slowValueBox d Ki, f (fun l => D.1 l + (i - a) * D.2.2 l + x l) :=
    tsum_eq_sum hzero
  have e2 : (∑' n : Fin d → ℤ, f n) = ∑ n ∈ Bn, f n := tsum_eq_sum hfBn
  rw [← e1, ← e2]
  exact (Equiv.addLeft (fun l => D.1 l + (i - a) * D.2.2 l)).tsum_eq f



private theorem sep_one_atom_lattice_stage_1 : SepOneAtomLatticeStage1Statement := by
  classical
  intro d χ H hχ ψ hψ1 hψ0 C θ i a b x t u ut Ki Kb ui ua ub hrel_i hrel_b f hf Bn hfBn Ppro D hPt
    ba bb
  have bt (l : Fin d) : |ut l - D.2.2 l| ≤ 3 / 4 := by
    simpa using sepPartition_ne_zero hPt l
  set! v : Fin d → ℤ := fun l => D.2.1 l - D.1 l - (b - a) * D.2.2 l with hv
  set! c : Fin d → ℤ := fun l => D.1 l + (i - a) * D.2.2 l with hc
  -- the equality cutoff selects exactly one carry
  have hvbox : v ∈ slowValueBox d Kb := by
    rw [mem_slowValueBox]
    intro l
    have hb' : ub l = ua l + ((b : ℝ) - a) * ut l := by
      have := congrFun hrel_b l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      push_cast at this
      linarith
    have hl : ((v l : ℤ) : ℝ) = (ua l - D.1 l) - (ub l - D.2.1 l) +
        ((b - a : ℤ) : ℝ) * (ut l - D.2.2 l) := by
      simp only [hv]; push_cast; rw [hb']; ring
    have h1 : |((v l : ℤ) : ℝ)| ≤ 2 + |((b - a : ℤ) : ℝ)| := by
      rw [hl]
      have := abs_add_le ((ua l - D.1 l) - (ub l - D.2.1 l)) (((b - a : ℤ) : ℝ) * (ut l - D.2.2 l))
      have h2 := abs_sub (ua l - D.1 l) (ub l - D.2.1 l)
      rw [abs_mul] at this
      have h3 : |((b - a : ℤ) : ℝ)| * |ut l - D.2.2 l| ≤ |((b - a : ℤ) : ℝ)| * (3 / 4) :=
        mul_le_mul_of_nonneg_left (bt l) (abs_nonneg _)
      have h4 := abs_nonneg ((b - a : ℤ) : ℝ)
      linarith [ba l, bb l]
    have h2 : (2 : ℝ) + |((b - a : ℤ) : ℝ)| ≤ Kb := Nat.le_ceil _
    exact_mod_cast h1.trans h2
  have hEsum : ∑ kb ∈ slowValueBox d Kb,
      tensorCutoff ψ (1 / 3)
        (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ)) = 1 := by
    have he (kb : Fin d → ℤ) : tensorCutoff ψ (1 / 3)
        (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ)) =
        if kb = v then 1 else 0 := by
      have hcast : (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ)) =
          fun l => (((v - kb) l : ℤ) : ℝ) := by
        funext l; simp [hv]
      rw [hcast, tensorCutoff_int hψ1 hψ0]
      by_cases h : kb = v
      · subst h; simp
      · simp [h, sub_ne_zero.mpr (Ne.symm h)]
    simp_rw [he]
    rw [Finset.sum_ite_eq' (slowValueBox d Kb) v (fun _ => (1 : ℂ))]
    simp [hvbox]
  have hfsum : ∑ x ∈ slowValueBox d Ki, f (fun l => D.1 l + (i - a) * D.2.2 l + x l) =
      ∑ n ∈ Bn, f n := by
    expose_names
    exact @sep_one_atom_lattice_hfsum d χ H hχ C θ i a x t hrel_i hf hfBn D ba bt
  calc Ppro D * ∑ n ∈ Bn, f n =
        Ppro D * (∑ x ∈ slowValueBox d Ki, f (fun l => D.1 l + (i - a) * D.2.2 l + x l)) *
          (∑ kb ∈ slowValueBox d Kb, tensorCutoff ψ (1 / 3)
            (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ))) := by
        rw [hfsum, hEsum, mul_one]
    _ = _ := by
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.mul_sum]


/-- Blueprint lem:separation, lines 1402–1404: the exact lattice identity for one
atom. After inserting lattice partitions for the slots `a, b` and for `t`, the
original index is recovered from its carry `k_i`, and the equality cutoff fixes the
carry `k_b`; only bounded carries occur. -/
theorem sep_one_atom_lattice {d : ℕ} (χ : (Fin d → ℝ) → ℂ) {H : ℝ}
    (hχ : ∀ w, χ w ≠ 0 → ∀ l, |w l| ≤ H) {ψ : ℝ → ℝ} (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (C : Matrix (Fin d) (Fin d) ℚ) (θ : Fin d → ℝ)
    (i a b : ℤ) (x t : ℝ) :
    let u := fun j : ℤ => fun l => θ l * (x + j * t)
    let ut : Fin d → ℝ := fun l => θ l * t
    let Ki := ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊
    let Kb := ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊
    (∑' n : Fin d → ℤ, χ (u i - fun l => (n l : ℝ)) *
        (Real.fourierChar (chartMatrixPhase C (u i) (u i - fun l => (n l : ℝ))) : ℂ)) =
      ∑ ki ∈ slowValueBox d Ki, ∑ kb ∈ slowValueBox d Kb,
        ∑' D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
          sepCoupledAmplitude χ ψ i a b ki kb (u a - fun l => (D.1 l : ℝ))
              (u b - fun l => (D.2.1 l : ℝ)) (ut - fun l => (D.2.2 l : ℝ)) *
            (Real.fourierChar (chartMatrixPhase C (u i)
              (u i - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ))) : ℂ) := by
  intro u ut Ki Kb
  classical
  set ui := u i with hui
  set ua := u a with hua
  set ub := u b with hub
  have hrel_i : ui = ua + ((i - a : ℤ) : ℝ) • ut := by
    funext l; simp [hui, hua, u, ut]; ring
  have hrel_b : ub = ua + ((b - a : ℤ) : ℝ) • ut := by
    funext l; simp [hub, hua, u, ut]; ring
  set f : (Fin d → ℤ) → ℂ := fun n => χ (ui - fun l => (n l : ℝ)) *
    (Real.fourierChar (chartMatrixPhase C ui (ui - fun l => (n l : ℝ))) : ℂ) with hf
  set Bn := chartLatticeBox H ui
  -- partitions restricted to boxes
  have hbox (z : Fin d → ℝ) (k : Fin d → ℤ) (hk : sepPartition (z - fun l => (k l : ℝ)) ≠ 0) :
      k ∈ chartLatticeBox 1 z :=
    mem_chartLatticeBox_of_bound (fun l => by
      have := sepPartition_ne_zero hk l
      simp only [Pi.sub_apply] at this
      linarith)
  have hP (z : Fin d → ℝ) :
      ∑ k ∈ chartLatticeBox 1 z, sepPartition (z - fun l => (k l : ℝ)) = 1 := by
    rw [← sepPartition_tsum z]
    exact (tsum_eq_sum (fun k hk => by by_contra h; exact hk (hbox z k h))).symm
  have hfBn : ∀ n ∉ Bn, f n = 0 := fun n hn => by
    by_contra h
    apply hn
    apply mem_chartLatticeBox_of_bound
    intro l
    have hχn : χ (ui - fun l => (n l : ℝ)) ≠ 0 := by
      intro h0; exact h (by simp [hf, h0])
    simpa using hχ _ hχn l
  set! B3 := chartLatticeBox 1 ua ×ˢ (chartLatticeBox 1 ub ×ˢ chartLatticeBox 1 ut)
  set! Ppro : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun D =>
    sepPartition (ua - fun l => (D.1 l : ℝ)) * sepPartition (ub - fun l => (D.2.1 l : ℝ)) *
      sepPartition (ut - fun l => (D.2.2 l : ℝ)) with hPpro
  have hPsum : ∑ D ∈ B3, Ppro D = 1 := by
    have e : ∑ D ∈ B3, Ppro D =
        (∑ da ∈ chartLatticeBox 1 ua, sepPartition (ua - fun l => (da l : ℝ))) *
          ((∑ db ∈ chartLatticeBox 1 ub, sepPartition (ub - fun l => (db l : ℝ))) *
            (∑ dd ∈ chartLatticeBox 1 ut, sepPartition (ut - fun l => (dd l : ℝ)))) := by
      simp only [B3, hPpro, Finset.sum_product]
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
      simp only [Finset.mul_sum, mul_assoc]
    rw [e, hP ua, hP ub, hP ut]; ring
  -- the left side
  have hL : (∑' n, f n) = ∑ D ∈ B3, Ppro D * ∑ n ∈ Bn, f n := by
    rw [tsum_eq_sum hfBn, ← Finset.sum_mul, hPsum, one_mul]
  rw [hL]
  -- vector identities
  have hvi (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) (ki : Fin d → ℤ) :
      (ua - fun l => (D.1 l : ℝ)) + ((i - a : ℤ) : ℝ) • (ut - fun l => (D.2.2 l : ℝ)) -
          (fun l => (ki l : ℝ)) =
        ui - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ) := by
    rw [hrel_i]; funext l; simp; ring
  have hvb (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) (kb : Fin d → ℤ) :
      (ua - fun l => (D.1 l : ℝ)) - (ub - fun l => (D.2.1 l : ℝ)) +
          ((b - a : ℤ) : ℝ) • (ut - fun l => (D.2.2 l : ℝ)) - (fun l => (kb l : ℝ)) =
        fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ) := by
    rw [hrel_b]; funext l; simp; ring
  -- the summand on the right
  have hterm (ki kb : Fin d → ℤ) (D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
      sepCoupledAmplitude χ ψ i a b ki kb (ua - fun l => (D.1 l : ℝ))
          (ub - fun l => (D.2.1 l : ℝ)) (ut - fun l => (D.2.2 l : ℝ)) *
        (Real.fourierChar (chartMatrixPhase C ui
          (ui - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ))) : ℂ) =
      Ppro D * (f (fun l => D.1 l + (i - a) * D.2.2 l + ki l) *
        tensorCutoff ψ (1 / 3)
          (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ))) := by
    simp only [sepCoupledAmplitude, hvi, hvb, hPpro, hf]
    ring
  have hRbox (ki kb : Fin d → ℤ) :
      (∑' D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
        sepCoupledAmplitude χ ψ i a b ki kb (ua - fun l => (D.1 l : ℝ))
            (ub - fun l => (D.2.1 l : ℝ)) (ut - fun l => (D.2.2 l : ℝ)) *
          (Real.fourierChar (chartMatrixPhase C ui
            (ui - fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ))) : ℂ)) =
      ∑ D ∈ B3, Ppro D * (f (fun l => D.1 l + (i - a) * D.2.2 l + ki l) *
        tensorCutoff ψ (1 / 3)
          (fun l => ((D.2.1 l - D.1 l - (b - a) * D.2.2 l - kb l : ℤ) : ℝ))) := by
    simp_rw [hterm]
    apply tsum_eq_sum
    intro D hD
    have hP0 : Ppro D = 0 := by
      by_contra h
      apply hD
      simp only [hPpro] at h
      have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
      have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
      have h3 := right_ne_zero_of_mul h
      exact Finset.mem_product.mpr ⟨hbox _ _ h1, Finset.mem_product.mpr ⟨hbox _ _ h2, hbox _ _ h3⟩⟩
    rw [hP0, zero_mul]
  simp_rw [hRbox]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := slowValueBox d Kb)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD3
  by_cases hP0 : Ppro D = 0
  · simp [hP0]
  have hPa : sepPartition (ua - fun l => (D.1 l : ℝ)) ≠ 0 := by
    intro h; apply hP0; simp only [hPpro, h, zero_mul]
  have hPb : sepPartition (ub - fun l => (D.2.1 l : ℝ)) ≠ 0 := by
    intro h; apply hP0; simp only [hPpro, h, mul_zero, zero_mul]
  have hPt : sepPartition (ut - fun l => (D.2.2 l : ℝ)) ≠ 0 := by
    intro h; apply hP0; simp only [hPpro, h, mul_zero]
  have ba (l : Fin d) : |ua l - D.1 l| ≤ 3 / 4 := by
    simpa using sepPartition_ne_zero hPa l
  have bb (l : Fin d) : |ub l - D.2.1 l| ≤ 3 / 4 := by
    simpa using sepPartition_ne_zero hPb l
  expose_names
  exact @sep_one_atom_lattice_stage_1 d χ H hχ ψ hψ1 hψ0 C θ i a b x t hrel_i hrel_b hf hfBn D hPt
    ba bb

/-! ### Fourier expansion of compactly supported smooth functions

A smooth function supported in the cube `[-R,R]ⁿ` is periodized with period `L ≥ 4R`
and rescaled to unit period. Inside a cutoff equal to one on the cube it is the
sum of its absolutely convergent Fourier series. Used in lem:separation, line 1407. -/

/-- The unit-rescaled `L`-periodization `x ↦ Σⱼ F(L(x + j))`. -/
noncomputable def cubePeriodization {n : ℕ} (F : (Fin n → ℝ) → ℂ) (L : ℝ)
    (x : Fin n → ℝ) : ℂ :=
  ∑' j : Fin n → ℤ, F (L • (x + fun l => (j l : ℝ)))

theorem cubePeriodization_periodic {n : ℕ} (F : (Fin n → ℝ) → ℂ) (L : ℝ)
    (x : Fin n → ℝ) (k : Fin n → ℤ) :
    cubePeriodization F L (x + fun l => (k l : ℝ)) = cubePeriodization F L x := by
  unfold cubePeriodization
  conv_rhs => rw [← (Equiv.addRight k).tsum_eq]
  apply tsum_congr
  intro j
  congr 2
  funext l
  simp only [Pi.add_apply, Equiv.coe_addRight, Int.cast_add]
  ring

/-- Locally the periodization is a finite sum. -/
theorem cubePeriodization_local {n : ℕ} (F : (Fin n → ℝ) → ℂ) {R L : ℝ} (hL : 0 < L)
    (hRL : 4 * R ≤ L) (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R) (x₀ y : Fin n → ℝ)
    (hy : dist y x₀ < 1 / 4) :
    cubePeriodization F L y =
      ∑ j ∈ chartLatticeBox (1 / 2) (-x₀), F (L • (y + fun l => (j l : ℝ))) := by
  unfold cubePeriodization
  apply tsum_eq_sum
  intro j hj
  by_contra h
  apply hj
  apply mem_chartLatticeBox_of_bound
  intro l
  have h1 := hsupp _ h l
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul, abs_of_pos hL] at h1
  have h2 : |y l + j l| ≤ 1 / 4 := by
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hL
    linarith
  have h3 : |y l - x₀ l| < 1 / 4 := by
    have := (dist_le_pi_dist y x₀ l).trans_lt hy
    rwa [Real.dist_eq] at this
  calc |(-x₀) l - j l| = |(y l - x₀ l) - (y l + j l)| := by congr 1; simp; ring
    _ ≤ |y l - x₀ l| + |y l + j l| := abs_sub _ _
    _ ≤ 1 / 2 := by linarith

theorem cubePeriodization_eventuallyEq {n : ℕ} (F : (Fin n → ℝ) → ℂ) {R L : ℝ} (hL : 0 < L)
    (hRL : 4 * R ≤ L) (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R) (x₀ : Fin n → ℝ) :
    cubePeriodization F L =ᶠ[nhds x₀]
      fun y => ∑ j ∈ chartLatticeBox (1 / 2) (-x₀), F (L • (y + fun l => (j l : ℝ))) := by
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  exact cubePeriodization_local F hL hRL hsupp x₀ y hy

theorem cubePeriodization_smooth {n : ℕ} {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {R L : ℝ} (hL : 0 < L) (hRL : 4 * R ≤ L) (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R) :
    ContDiff ℝ (⊤ : ℕ∞) (cubePeriodization F L) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  refine ContDiffAt.congr_of_eventuallyEq ?_ (cubePeriodization_eventuallyEq F hL hRL hsupp x₀)
  apply ContDiff.contDiffAt
  apply ContDiff.sum; intro j _
  exact hF.comp ((contDiff_id.add contDiff_const).const_smul L)

theorem cubePeriodization_iteratedFDeriv_le {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R L : ℝ} (hL : 0 < L) (hRL : 4 * R ≤ L)
    (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R) (m : ℕ) {A : ℝ}
    (hA : ∀ w, ‖iteratedFDeriv ℝ m F w‖ ≤ A) (x₀ : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (cubePeriodization F L) x₀‖ ≤ 4 ^ n * (L ^ m * A) := by
  have hev := cubePeriodization_eventuallyEq F hL hRL hsupp x₀
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev m).eq_of_nhds]
  have hs (j : Fin n → ℤ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => F (L • (y + fun l => (j l : ℝ)))) :=
    hF.comp ((contDiff_id.add contDiff_const).const_smul L)
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => ((hs j).of_le (by simp)).contDiffAt)]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hterm (j : Fin n → ℤ) :
      ‖iteratedFDeriv ℝ m (fun y => F (L • (y + fun l => (j l : ℝ)))) x₀‖ ≤ L ^ m * A := by
    let T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := L • ContinuousLinearMap.id ℝ _
    have hT : ‖T‖ ≤ L := by
      calc ‖T‖ ≤ ‖L‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ :=
            norm_smul_le L (ContinuousLinearMap.id ℝ (Fin n → ℝ))
        _ ≤ L * 1 := by
            rw [Real.norm_eq_abs, abs_of_pos hL]
            exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hL.le
        _ = L := mul_one L
    have he : (fun y => F (L • (y + fun l => (j l : ℝ)))) =
        (fun z => F (z + L • fun l => (j l : ℝ))) ∘ T := by
      funext y; simp [T, smul_add]
    have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun z => F (z + L • fun l => (j l : ℝ))) :=
      hF.comp (contDiff_id.add contDiff_const)
    rw [he, T.iteratedFDeriv_comp_right hfc x₀ (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    rw [iteratedFDeriv_comp_add_right' m]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc _ ≤ A * ‖T‖ ^ m := mul_le_mul_of_nonneg_right (hA _) (by positivity)
      _ ≤ A * L ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hT m) hA0
      _ = L ^ m * A := mul_comm _ _
  calc _ ≤ ∑ j ∈ chartLatticeBox (1 / 2) (-x₀),
        ‖iteratedFDeriv ℝ m (fun y => F (L • (y + fun l => (j l : ℝ)))) x₀‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ chartLatticeBox (1 / 2) (-x₀), L ^ m * A := Finset.sum_le_sum fun j _ => hterm j
    _ = ((chartLatticeBox (1 / 2) (-x₀)).card : ℝ) * (L ^ m * A) := by simp
    _ ≤ 4 ^ n * (L ^ m * A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := chartLatticeBox_card_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (-x₀)
        norm_num at this ⊢
        exact this

theorem cubePeriodization_eq {n : ℕ} (F : (Fin n → ℝ) → ℂ) {R L : ℝ} (hR : 0 < R)
    (hL : 0 < L) (hRL : 4 * R ≤ L) (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R)
    (w : Fin n → ℝ) (hw : ∀ l, |w l| ≤ 2 * R) :
    cubePeriodization F L (fun l => w l / L) = F w := by
  unfold cubePeriodization
  rw [tsum_eq_single 0]
  · congr 1; funext l; simp; field_simp
  · intro j hj
    obtain ⟨l, hl⟩ : ∃ l, j l ≠ 0 := by
      by_contra h; push Not at h; exact hj (funext h)
    by_contra h
    have h1 := hsupp _ h l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
    have e : L * (w l / L + j l) = w l + L * j l := by field_simp
    rw [e] at h1
    have hj1 : (1 : ℝ) ≤ |(j l : ℝ)| := by exact_mod_cast Int.one_le_abs hl
    have h2 : L ≤ |L * j l| := by
      rw [abs_mul, abs_of_pos hL]; nlinarith
    have h3 := abs_sub_abs_le_abs_sub (L * j l) (-w l)
    rw [abs_neg, sub_neg_eq_add, add_comm] at h3
    linarith [hw l]

/-- Blueprint lem:separation, line 1407: a smooth function supported in `[-R,R]ⁿ`
equals `Σ_p c_p Φ(w) e(p·w/L)` inside any cutoff `Φ` that is one on `[-R,R]ⁿ` and
vanishes outside `[-2R,2R]ⁿ`, for `L ≥ 4R`. The coefficients are those of the
unit-rescaled periodization, with derivative-controlled decay. -/
theorem compact_cutoff_fourier_expansion {n m : ℕ} (hn : 1 ≤ n) (hm : n < m)
    {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hRL : 4 * R ≤ L) (hsupp : ∀ w, F w ≠ 0 → ∀ l, |w l| ≤ R)
    {Φ : (Fin n → ℝ) → ℂ} (hΦ1 : ∀ w, (∀ l, |w l| ≤ R) → Φ w = 1)
    (hΦ0 : ∀ w, Φ w ≠ 0 → ∀ l, |w l| ≤ 2 * R) {A₀ A : ℝ}
    (hA₀ : ∀ w, ‖F w‖ ≤ A₀) (hA : ∀ w, ‖iteratedFDeriv ℝ m F w‖ ≤ A) :
    (∀ w, HasSum (fun p => periodicFourierCoeff (cubePeriodization F L) p *
        (Φ w * (Real.fourierChar (∑ l, (p l : ℝ) * (w l / L)) : ℂ))) (F w)) ∧
      Summable (fun p => ‖periodicFourierCoeff (cubePeriodization F L) p‖) ∧
      (∀ p, p ≠ 0 → ‖periodicFourierCoeff (cubePeriodization F L) p‖ ≤
        4 ^ n * (L ^ m * A) * (Real.sqrt n / (2 * Real.pi * frequencyLength p)) ^ m) ∧
      (∀ p, ‖periodicFourierCoeff (cubePeriodization F L) p‖ ≤ 4 ^ n * A₀) := by
  have hg := cubePeriodization_smooth hF hL hRL hsupp
  have hA0' : ∀ w, ‖iteratedFDeriv ℝ 0 F w‖ ≤ A₀ := fun w => by
    rw [norm_iteratedFDeriv_zero]; exact hA₀ w
  have hB (x : Fin n → ℝ) : ‖cubePeriodization F L x‖ ≤ 4 ^ n * A₀ := by
    have h := cubePeriodization_iteratedFDeriv_le hF hL hRL hsupp 0 hA0' x
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := periodic_fourier_expansion_of_fderiv hn hm
    (cubePeriodization F L) hg (cubePeriodization_periodic F L)
    (cubePeriodization_iteratedFDeriv_le hF hL hRL hsupp m hA) hB
  refine ⟨fun w => ?_, h2, h3, h4⟩
  have hFw : F w = Φ w * cubePeriodization F L (fun l => w l / L) := by
    by_cases hΦ : Φ w = 0
    · rw [hΦ, zero_mul]
      by_contra h
      have h1 := hΦ1 w (hsupp w h)
      rw [hΦ] at h1
      exact zero_ne_one h1
    · rw [cubePeriodization_eq F hR hL hRL hsupp w (hΦ0 w hΦ)]
      by_cases hF0 : F w = 0
      · rw [hF0, mul_zero]
      · rw [hΦ1 w (hsupp w hF0), one_mul]
  rw [hFw]
  have := (h1 (fun l => w l / L)).mul_left (Φ w)
  convert this using 1
  funext p
  ring

/-- A modulated plateau cutoff `w ↦ Φ(w) e(p·w/L)`, the factor amplitudes of the
product-cutoff expansion in lem:separation, line 1407. -/
noncomputable def modulatedCutoff {d : ℕ} (ψ : ℝ → ℝ) (r L : ℝ) (p : Fin d → ℤ)
    (w : Fin d → ℝ) : ℂ :=
  tensorCutoff ψ r w * (Real.fourierChar (∑ l, (p l : ℝ) * (w l / L)) : ℂ)

theorem modulatedCutoff_smooth {d : ℕ} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (r L : ℝ) (p : Fin d → ℤ) : ContDiff ℝ (⊤ : ℕ∞) (modulatedCutoff ψ r L p) := by
  unfold modulatedCutoff
  exact (tensorCutoff_smooth hψ r).mul (chart_fourierChar_smooth.comp (by fun_prop))

theorem tensorCutoff_hasCompactSupport {d : ℕ} {ψ : ℝ → ℝ}
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (tensorCutoff (d := d) ψ r) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := fun _ : Fin d => -2 * r)
    (b := fun _ => 2 * r))
  intro w hw
  by_contra h
  apply hw
  constructor
  · intro l
    have := tensorCutoff_ne_zero_bound hψ0 hr h l
    have := (abs_lt.mp this).1
    linarith
  · intro l
    have := tensorCutoff_ne_zero_bound hψ0 hr h l
    have := (abs_lt.mp this).2
    linarith

theorem modulatedCutoff_hasCompactSupport {d : ℕ} {ψ : ℝ → ℝ}
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) {r : ℝ} (hr : 0 < r) (L : ℝ) (p : Fin d → ℤ) :
    HasCompactSupport (modulatedCutoff ψ r L p) :=
  (tensorCutoff_hasCompactSupport hψ0 hr).mul_right

/-- A one-variable chart with given horizontal vector, phases, rational matrix
and smooth compact amplitude. -/
noncomputable def mkQuadraticChart {d : ℕ} (θ : Fin d → ℝ) (lam β : ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (G : (Fin d → ℝ) → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) : QuadraticChartData d where
  horizontal := θ
  quadratic := lam
  linear := β
  matrix := C
  amplitude := G
  smooth := hG
  compact := hGc

theorem mkQuadraticChart_atom {d : ℕ} (θ : Fin d → ℝ) (lam β : ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (G : (Fin d → ℝ) → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (y : ℝ) :
    quadraticChartAtom (mkQuadraticChart θ lam β C G hG hGc) y =
      (Real.fourierChar (lam * y ^ 2 + β * y) : ℂ) *
        ∑' n : Fin d → ℤ, G ((fun l => θ l * y) - fun l => (n l : ℝ)) *
          (Real.fourierChar (chartMatrixPhase C (fun l => θ l * y)
            ((fun l => θ l * y) - fun l => (n l : ℝ))) : ℂ) := by
  rfl

theorem chartMatrixPhase_scale_matrix {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (q : ℚ)
    (u w : Fin d → ℝ) :
    chartMatrixPhase (q • C) u w = (q : ℝ) * chartMatrixPhase C u w := by
  simp only [chartMatrixPhase, Matrix.smul_apply, smul_eq_mul, Rat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro m _
  ring

theorem chartMatrixPhase_line {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (θ : Fin d → ℝ)
    (y : ℝ) (v : Fin d → ℝ) :
    chartMatrixPhase C (fun l => θ l * y) ((fun l => θ l * y) - v) =
      y ^ 2 * chartMatrixPhase C θ θ - y * chartMatrixPhase C θ v := by
  simp only [chartMatrixPhase, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro m _
  ring

theorem chartMatrixPhase_int_comb {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (θ : Fin d → ℝ)
    (c₁ c₂ c₃ : ℤ) (v₁ v₂ v₃ : Fin d → ℤ) :
    chartMatrixPhase C θ (fun l => ((c₁ * v₁ l + c₂ * v₂ l + c₃ * v₃ l : ℤ) : ℝ)) =
      c₁ * chartMatrixPhase C θ (fun l => (v₁ l : ℝ)) +
        c₂ * chartMatrixPhase C θ (fun l => (v₂ l : ℝ)) +
        c₃ * chartMatrixPhase C θ (fun l => (v₃ l : ℝ)) := by
  simp only [chartMatrixPhase, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro m _
  push_cast
  ring

/-- Blueprint lem:separation, line 1405: on the constraint `d_b = d_a + (b-a)d + k_b`,
the full phase of the original atom splits exactly into the phases of the three
factor charts: matrices `-α_a C`, `-α_b C`, `S C`, quadratic coefficients
`-α_a λ`, `-α_b λ`, `S λ`, and linear phases carrying the integer carries. -/
theorem separation_phase_split {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (θ : Fin d → ℝ)
    (lam β : ℝ) (i a b : ℤ) (hab : a ≠ b) (x t : ℝ) (da db dd ki kb : Fin d → ℤ)
    (hdb : db = fun l => da l + (b - a) * dd l + kb l) :
    let αa : ℚ := (i - b) / (b - a)
    let αb : ℚ := (a - i) / (b - a)
    let S : ℚ := (i - a) * (i - b)
    let u := fun j : ℤ => fun l => θ l * (x + j * t)
    let ut : Fin d → ℝ := fun l => θ l * t
    let n : Fin d → ℤ := fun l => da l + (i - a) * dd l + ki l
    let Bk := chartMatrixPhase C θ (fun l => (ki l : ℝ))
    let Bkb := chartMatrixPhase C θ (fun l => (kb l : ℝ))
    lam * (x + i * t) ^ 2 + β * (x + i * t) +
        chartMatrixPhase C (u i) (u i - fun l => (n l : ℝ)) =
      ((-(αa : ℝ) * lam) * (x + a * t) ^ 2 + (-(αa : ℝ) * β + αa * Bk) * (x + a * t) +
          chartMatrixPhase (-αa • C) (u a) (u a - fun l => (da l : ℝ))) +
        ((-(αb : ℝ) * lam) * (x + b * t) ^ 2 +
            (-(αb : ℝ) * β + αb * Bk - αb * Bkb) * (x + b * t) +
          chartMatrixPhase (-αb • C) (u b) (u b - fun l => (db l : ℝ))) +
        (((S : ℝ) * lam) * t ^ 2 + 0 * t +
          chartMatrixPhase (S • C) ut (ut - fun l => (dd l : ℝ))) := by
  intro αa αb S u ut n Bk Bkb
  have hba : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hab))
  have hαa : ((αa : ℚ) : ℝ) = (i - b) / (b - a) := by simp [αa]
  have hαb : ((αb : ℚ) : ℝ) = (a - i) / (b - a) := by simp [αb]
  have hS : ((S : ℚ) : ℝ) = (i - a) * (i - b) := by simp [S]
  subst hdb
  have hn : chartMatrixPhase C θ (fun l => (n l : ℝ)) =
      chartMatrixPhase C θ (fun l => (da l : ℝ)) +
        ((i : ℝ) - a) * chartMatrixPhase C θ (fun l => (dd l : ℝ)) + Bk := by
    have h := chartMatrixPhase_int_comb C θ 1 (i - a) 1 da dd ki
    simp only [one_mul, Int.cast_one] at h
    push_cast at h
    simp only [n, Bk]; push_cast; exact h
  have hdb' : chartMatrixPhase C θ (fun l => ((da l + (b - a) * dd l + kb l : ℤ) : ℝ)) =
      chartMatrixPhase C θ (fun l => (da l : ℝ)) +
        ((b : ℝ) - a) * chartMatrixPhase C θ (fun l => (dd l : ℝ)) + Bkb := by
    have h := chartMatrixPhase_int_comb C θ 1 (b - a) 1 da dd kb
    simp only [one_mul, Int.cast_one] at h
    push_cast at h
    simp only [Bkb]; push_cast; exact h
  have hut : ut = fun l => θ l * t := rfl
  simp only [u, hut, chartMatrixPhase_scale_matrix, chartMatrixPhase_line, hn, hdb',
    Rat.cast_neg]
  rw [hαa, hαb, hS]
  field_simp
  ring

/-- Three blocks of coordinates as one vector of length `d + d + d`. -/
def tripleVec {d : ℕ} {α : Type*} (u v w : Fin d → α) : Fin (d + d + d) → α :=
  Fin.append (Fin.append u v) w

/-- First coordinate block of a vector divided into three equal blocks. -/
def tripleFst {d : ℕ} {α : Type*} (z : Fin (d + d + d) → α) : Fin d → α :=
  fun l => z (Fin.castAdd d (Fin.castAdd d l))

/-- Middle coordinate block of a vector divided into three equal blocks. -/
def tripleSnd {d : ℕ} {α : Type*} (z : Fin (d + d + d) → α) : Fin d → α :=
  fun l => z (Fin.castAdd d (Fin.natAdd d l))

/-- Last coordinate block of a vector divided into three equal blocks. -/
def tripleThd {d : ℕ} {α : Type*} (z : Fin (d + d + d) → α) : Fin d → α :=
  fun l => z (Fin.natAdd (d + d) l)

@[simp] theorem tripleFst_tripleVec {d : ℕ} {α : Type*} (u v w : Fin d → α) :
    tripleFst (tripleVec u v w) = u := by
  funext l; simp only [tripleFst, tripleVec, Fin.append_left]

@[simp] theorem tripleSnd_tripleVec {d : ℕ} {α : Type*} (u v w : Fin d → α) :
    tripleSnd (tripleVec u v w) = v := by
  funext l; simp only [tripleSnd, tripleVec, Fin.append_left, Fin.append_right]

@[simp] theorem tripleThd_tripleVec {d : ℕ} {α : Type*} (u v w : Fin d → α) :
    tripleThd (tripleVec u v w) = w := by
  funext l; simp only [tripleThd, tripleVec, Fin.append_right]

theorem sum_tripleVec {d : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (d + d + d) → M) :
    ∑ l, f l = ∑ l, f (Fin.castAdd d (Fin.castAdd d l)) +
      ∑ l, f (Fin.castAdd d (Fin.natAdd d l)) + ∑ l, f (Fin.natAdd (d + d) l) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]

theorem prod_tripleVec {d : ℕ} {M : Type*} [CommMonoid M] (f : Fin (d + d + d) → M) :
    ∏ l, f l = (∏ l, f (Fin.castAdd d (Fin.castAdd d l))) *
      (∏ l, f (Fin.castAdd d (Fin.natAdd d l))) * ∏ l, f (Fin.natAdd (d + d) l) := by
  rw [Fin.prod_univ_add, Fin.prod_univ_add]

/-- A product cutoff with a character factors over the three blocks. -/
theorem modulated_tripleVec {d : ℕ} (ψ : ℝ → ℝ) (r L : ℝ) (p : Fin (d + d + d) → ℤ)
    (u v w : Fin d → ℝ) :
    tensorCutoff ψ r (tripleVec u v w) *
        (Real.fourierChar (∑ l, (p l : ℝ) * (tripleVec u v w l / L)) : ℂ) =
      modulatedCutoff ψ r L (tripleFst p) u * modulatedCutoff ψ r L (tripleSnd p) v *
        modulatedCutoff ψ r L (tripleThd p) w := by
  unfold modulatedCutoff tensorCutoff
  rw [prod_tripleVec, sum_tripleVec, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    Circle.coe_mul, Circle.coe_mul]
  simp only [tripleVec, Fin.append_left, Fin.append_right, tripleFst, tripleSnd, tripleThd]
  ring

/-- Compactly supported smooth functions have bounded derivatives of each order. -/
theorem exists_iteratedFDeriv_bound {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) (m : ℕ) :
    ∃ A, ∀ w, ‖iteratedFDeriv ℝ m F w‖ ≤ A := by
  have hcont : Continuous (fun w => ‖iteratedFDeriv ℝ m F w‖) :=
    (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hcs : HasCompactSupport (fun w => ‖iteratedFDeriv ℝ m F w‖) :=
    (hc.iteratedFDeriv m).norm
  obtain ⟨A, hA⟩ := hcont.bddAbove_range_of_hasCompactSupport hcs
  exact ⟨A, fun w => hA ⟨w, rfl⟩⟩

/-- The coupled amplitude of lem:separation as a function on `ℝ^(d+d+d)`. -/
noncomputable def sepCoupledVec {d : ℕ} (χ : (Fin d → ℝ) → ℂ) (ψ : ℝ → ℝ) (i a b : ℤ)
    (ki kb : Fin d → ℤ) (v : Fin (d + d + d) → ℝ) : ℂ :=
  sepCoupledAmplitude χ ψ i a b ki kb (tripleFst v) (tripleSnd v) (tripleThd v)

theorem sepPartition_smooth {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (sepPartition (d := d)) :=
  chartCoordinateProduct_smooth (contDiff_infty.mpr gevreyPartition_contDiff)

theorem tripleFst_contDiff {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (tripleFst (d := d) (α := ℝ)) := by
  apply contDiff_pi.mpr; intro l; exact contDiff_apply ℝ (fun _ => ℝ) _

theorem tripleSnd_contDiff {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (tripleSnd (d := d) (α := ℝ)) := by
  apply contDiff_pi.mpr; intro l; exact contDiff_apply ℝ (fun _ => ℝ) _

theorem tripleThd_contDiff {d : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (tripleThd (d := d) (α := ℝ)) := by
  apply contDiff_pi.mpr; intro l; exact contDiff_apply ℝ (fun _ => ℝ) _

theorem sepCoupledVec_smooth {d : ℕ} {χ : (Fin d → ℝ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i a b : ℤ) (ki kb : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (sepCoupledVec χ ψ i a b ki kb) := by
  have h1 := tripleFst_contDiff (d := d)
  have h2 := tripleSnd_contDiff (d := d)
  have h3 := tripleThd_contDiff (d := d)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (d + d + d) → ℝ =>
      χ (tripleFst v + ((i - a : ℤ) : ℝ) • tripleThd v - fun l => (ki l : ℝ))) :=
    hχ.comp ((h1.add (h3.const_smul _)).sub contDiff_const)
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (d + d + d) → ℝ =>
      tensorCutoff ψ (1 / 3) (tripleFst v - tripleSnd v + ((b - a : ℤ) : ℝ) • tripleThd v -
        fun l => (kb l : ℝ))) :=
    (tensorCutoff_smooth hψ _).comp (((h1.sub h2).add (h3.const_smul _)).sub
      contDiff_const)
  have hP1 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (d + d + d) → ℝ => sepPartition (tripleFst v)) :=
    sepPartition_smooth.comp h1
  have hP2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (d + d + d) → ℝ => sepPartition (tripleSnd v)) :=
    sepPartition_smooth.comp h2
  have hP3 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (d + d + d) → ℝ => sepPartition (tripleThd v)) :=
    sepPartition_smooth.comp h3
  exact (((hA.mul hE).mul hP1).mul hP2).mul hP3

theorem sepCoupledVec_support {d : ℕ} {χ : (Fin d → ℝ) → ℂ} {ψ : ℝ → ℝ} {i a b : ℤ}
    {ki kb : Fin d → ℤ} {v : Fin (d + d + d) → ℝ} (hv : sepCoupledVec χ ψ i a b ki kb v ≠ 0)
    (l : Fin (d + d + d)) : |v l| ≤ 3 / 4 := by
  unfold sepCoupledVec sepCoupledAmplitude at hv
  have ha := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hv))
  have hb := right_ne_zero_of_mul (left_ne_zero_of_mul hv)
  have ht := right_ne_zero_of_mul hv
  refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l
  · refine Fin.addCases (fun l'' => ?_) (fun l'' => ?_) l'
    · exact sepPartition_ne_zero ha l''
    · exact sepPartition_ne_zero hb l''
  · exact sepPartition_ne_zero ht l'

/-- The Fourier coefficients of the coupled amplitude (unit-rescaled, period 3). -/
noncomputable def sepCoeff {d : ℕ} (χ : (Fin d → ℝ) → ℂ) (ψ : ℝ → ℝ) (i a b : ℤ)
    (ki kb : Fin d → ℤ) (p : Fin (d + d + d) → ℤ) : ℂ :=
  periodicFourierCoeff (cubePeriodization (sepCoupledVec χ ψ i a b ki kb) 3) p

section SepCharts
variable {d : ℕ} (A : QuadraticChartData d) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
  (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (i a b : ℤ)

/-- The slot-`a` factor chart of lem:separation (matrix `-α_a C`). -/
noncomputable def sepChartA (ki pa : Fin d → ℤ) : QuadraticChartData d :=
  mkQuadraticChart A.horizontal (-(((i - b) / (b - a) : ℚ) : ℝ) * A.quadratic)
    (-(((i - b) / (b - a) : ℚ) : ℝ) * A.linear +
      (((i - b) / (b - a) : ℚ) : ℝ) * chartMatrixPhase A.matrix A.horizontal
        (fun l => (ki l : ℝ)))
    (-((i - b) / (b - a) : ℚ) • A.matrix) (modulatedCutoff ψ (3 / 4) 3 pa)
    (modulatedCutoff_smooth hψ _ _ _) (modulatedCutoff_hasCompactSupport hψ0 (by norm_num) _ _)

/-- The slot-`b` factor chart of lem:separation (matrix `-α_b C`). -/
noncomputable def sepChartB (ki kb pb : Fin d → ℤ) : QuadraticChartData d :=
  mkQuadraticChart A.horizontal (-(((a - i) / (b - a) : ℚ) : ℝ) * A.quadratic)
    (-(((a - i) / (b - a) : ℚ) : ℝ) * A.linear +
      (((a - i) / (b - a) : ℚ) : ℝ) * chartMatrixPhase A.matrix A.horizontal
        (fun l => (ki l : ℝ)) -
      (((a - i) / (b - a) : ℚ) : ℝ) * chartMatrixPhase A.matrix A.horizontal
        (fun l => (kb l : ℝ)))
    (-((a - i) / (b - a) : ℚ) • A.matrix) (modulatedCutoff ψ (3 / 4) 3 pb)
    (modulatedCutoff_smooth hψ _ _ _) (modulatedCutoff_hasCompactSupport hψ0 (by norm_num) _ _)

/-- The time factor chart of lem:separation (matrix `S C`, `S = (i-a)(i-b)`). -/
noncomputable def sepChartT (pt : Fin d → ℤ) : QuadraticChartData d :=
  mkQuadraticChart A.horizontal ((((i - a) * (i - b) : ℚ) : ℝ) * A.quadratic) 0
    (((i - a) * (i - b) : ℚ) • A.matrix) (modulatedCutoff ψ (3 / 4) 3 pt)
    (modulatedCutoff_smooth hψ _ _ _) (modulatedCutoff_hasCompactSupport hψ0 (by norm_num) _ _)

end SepCharts

theorem triple_sum_factor {α β γ : Type*} (c : ℂ) (s₁ : Finset α) (s₂ : Finset β)
    (s₃ : Finset γ) (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) :
    c * (∑ x ∈ s₁, f x) * (∑ y ∈ s₂, g y) * (∑ z ∈ s₃, h z) =
      ∑ x ∈ s₁, ∑ y ∈ s₂, ∑ z ∈ s₃, c * (f x * g y * h z) := by
  rw [mul_assoc, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-- The contribution of one carry pair `(k_i, k_b)` to the separated atom. -/
noncomputable def sepFamilyValue {d : ℕ} (A : QuadraticChartData d) (ψ : ℝ → ℝ) (i a b : ℤ)
    (x t : ℝ) (ki kb : Fin d → ℤ) : ℂ :=
  (Real.fourierChar (A.quadratic * (x + i * t) ^ 2 + A.linear * (x + i * t)) : ℂ) *
    ∑' D : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
      sepCoupledAmplitude A.amplitude ψ i a b ki kb
          ((fun l => A.horizontal l * (x + a * t)) - fun l => (D.1 l : ℝ))
          ((fun l => A.horizontal l * (x + b * t)) - fun l => (D.2.1 l : ℝ))
          ((fun l => A.horizontal l * t) - fun l => (D.2.2 l : ℝ)) *
        (Real.fourierChar (chartMatrixPhase A.matrix (fun l => A.horizontal l * (x + i * t))
          ((fun l => A.horizontal l * (x + i * t)) -
            fun l => ((D.1 l + (i - a) * D.2.2 l + ki l : ℤ) : ℝ))) : ℂ)



end TrilinearHT.Auto
end
