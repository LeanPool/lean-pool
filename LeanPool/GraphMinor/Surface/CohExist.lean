/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CohCount

/-!
# Each set of values on the labels comes from a class

Let `V` be a choice of values on the labels with total sum zero along the word `ew a b c` and with
zero values on the free
sides. On each side, take the sum `Sm` at the start of the side on the first half and the sum at its
end on the second
half. This function has constant jumps on pasted sides, so `exists_cocycle` gives a local cocycle
(`exists_class`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y} {A : Type} [AddCommGroup A]

open Classical in
/-- The value on the point of the side `p` at the distance `u` from its start. -/
noncomputable def gx (a b c : ℕ) (V : ℕ → A) (p : ℕ) (u : ℝ) : A :=
  Sm a b c V (st a b c p) + if ofs (sgn a b c p) u < 1 / 2 then 0 else V (lab a b c p)

theorem gx_zero (V : ℕ → A) (p : ℕ) : gx a b c V p 0 = Sm a b c V p := by
  unfold gx st
  by_cases h : sgn a b c p
  · simp [h, ofs]
  · simp only [h, Bool.false_eq_true, ite_false, ofs]
    rw [ite_eq_right (by norm_num), Sm_succ, lv, ite_eq_right h]
    abel

theorem gx_one (V : ℕ → A) (p : ℕ) : gx a b c V p 1 = Sm a b c V (p + 1) := by
  unfold gx st
  by_cases h : sgn a b c p
  · simp only [h, ite_true, ofs]
    rw [ite_eq_right (by norm_num), Sm_succ, lv, ite_eq_left h]
  · simp [h, ofs]

theorem gx_congr (V : ℕ → A) (hV : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0) {p p' : ℕ} {u u' : ℝ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hp' : p' < 4 * a + 2 * b + 3 * c + 2) (hu : u ∈ Icc
      (0 : ℝ) 1)
    (hu' : u' ∈ Icc (0 : ℝ) 1) (he : per (4 * a + 2 * b + 3 * c + 2) (p + u) = per
      (4 * a + 2 * b + 3 * c + 2) (p' + u')) :
    gx a b c V p u = gx a b c V p' u' := by
  set n := 4 * a + 2 * b + 3 * c + 2 with hn
  by_cases h1 : u ∈ Ioo (0 : ℝ) 1
  · obtain ⟨rfl, rfl⟩ := side_unique hp hp' h1 hu' he
    rfl
  by_cases h2 : u' ∈ Ioo (0 : ℝ) 1
  · obtain ⟨rfl, rfl⟩ := side_unique hp' hp h2 hu he.symm
    rfl
  have hend : ∀ v ∈ Icc (0 : ℝ) 1, v ∉ Ioo (0 : ℝ) 1 → v = 0 ∨ v = 1 := fun v hv hv' => by
    by_contra hc
    push Not at hc
    exact hv' ⟨lt_of_le_of_ne hv.1 (Ne.symm hc.1), lt_of_le_of_ne hv.2 hc.2⟩
  have key : ∀ (q : ℕ) (v : ℝ), v = 0 ∨ v = 1 → ∃ j : ℕ, (j : ℝ) = q + v ∧ j ≤ q + 1 ∧
      gx a b c V q v = Sm a b c V j := by
    rintro q v (rfl | rfl)
    · exact ⟨q, by simp, by omega, gx_zero V q⟩
    · exact ⟨q + 1, by simp, le_rfl, gx_one V q⟩
  obtain ⟨j, hj, hj1, hj2⟩ := key p u (hend u hu h1)
  obtain ⟨j', hj', hj1', hj2'⟩ := key p' u' (hend u' hu' h2)
  rw [hj2, hj2']
  rw [← hj, ← hj'] at he
  obtain ⟨m, hm⟩ := per_eq (show 0 < n by omega) he
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm' : (j : ℤ) = j' + m * n := by exact_mod_cast hm
  have hjn : (j : ℤ) ≤ n := by exact_mod_cast (show j ≤ n by omega)
  have hjn' : (j' : ℤ) ≤ n := by exact_mod_cast (show j' ≤ n by omega)
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hj0' : (0 : ℤ) ≤ j' := by positivity
  have hmb : m = 0 ∨ m = 1 ∨ m = -1 := by
    have h3 : m < 2 := by
      by_contra hc
      have : 2 * (n : ℤ) ≤ m * n := by nlinarith
      omega
    have h4 : -2 < m := by
      by_contra hc
      have : m * (n : ℤ) ≤ -2 * n := by nlinarith
      omega
    omega
  have hS0 : Sm a b c V 0 = 0 := by simp [Sm]
  rcases hmb with rfl | rfl | rfl
  · have : j = j' := by omega
    rw [this]
  · have h3 : j = n := by omega
    have h4 : j' = 0 := by omega
    rw [h3, h4, hV, hS0]
  · have h3 : j = 0 := by omega
    have h4 : j' = n := by omega
    rw [h3, h4, hV, hS0]

open Classical in
/-- The function on the polygon. -/
noncomputable def gz (a b c : ℕ) (V : ℕ → A) (z : ℂ) : A :=
  if h : ∃ x : ℕ × ℝ, x.1 < 4 * a + 2 * b + 3 * c + 2 ∧ x.2 ∈ Icc (0 : ℝ) 1 ∧
      per (4 * a + 2 * b + 3 * c + 2) (x.1 + x.2) = z then gx a b c V h.choose.1 h.choose.2 else 0

theorem gz_per (V : ℕ → A) (hV : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0) {p : ℕ} {u : ℝ}
    (hp : p < 4 * a + 2 * b + 3 * c + 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    gz a b c V (per (4 * a + 2 * b + 3 * c + 2) (p + u)) = gx a b c V p u := by
  have hex : ∃ x : ℕ × ℝ, x.1 < 4 * a + 2 * b + 3 * c + 2 ∧ x.2 ∈ Icc (0 : ℝ) 1 ∧
      per (4 * a + 2 * b + 3 * c + 2) (x.1 + x.2) = per (4 * a + 2 * b + 3 * c + 2) (p + u)
        := ⟨(p, u), hp, hu, rfl⟩
  rw [gz, dite_eq_left hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact gx_congr V hV h1 hp h2 hu h3

theorem ofs_flp' (e e' : Bool) (u : ℝ) : ofs e' (flp e e' u) = ofs e u := by
  rw [← ofs_flp, ofs_ofs]

theorem sideConst_gz (V : ℕ → A) (hV : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0) :
    SideConst (sW (ew a b c)) (fun x => gz a b c V x.2) := by
  intro i p j q k e e' h1 h2 _
  obtain ⟨rfl, h4⟩ := sW_get h1
  obtain ⟨rfl, h5⟩ := sW_get h2
  obtain ⟨hp, hl, rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h4
  obtain ⟨hq, hl', rfl⟩ := (ew_get_iff _ _ _ _ _ _).mp h5
  refine ⟨Sm a b c V (st a b c q) - Sm a b c V (st a b c p), fun u hu => ?_⟩
  simp only [spt_ew]
  rw [gz_per V hV hp hu, gz_per V hV hq (flp_mem hu), gx, gx, ofs_flp', hl, hl']
  abel

/-- Values on the labels with total sum zero and with zero values on the free sides come from a
class. -/
theorem exists_class [T2Space Y] [Finite A] (hf : Presents (sW (ew a b c)) f) (V : ℕ → A)
    (hV : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0) (h2 : ∀ i < c, V (2 * a + b + 2 * i + 1)
      = 0) :
    ∃ (φ : Y → Y → A) (g : ℂ → A), IsCoc φ ∧ BdTriv φ ∧ IsPrim φ (pmap f) g ∧
      ∀ k ≤ 2 * a + b + 2 * c, lval a b c g k = V k := by
  have h0 : sW (ew a b c) 0 ≠ [] := (ew_mem_dsk a b c).1
  obtain ⟨φ, h3, h4, h5⟩ := exists_cocycle (g := fun x => gz a b c V x.2) (finW_sW _)
    (isPaired_ew a b c) hf
    (sideConst_gz V hV) h0
  refine ⟨φ, gz a b c V, h3, h5 ?_, h4, fun k hk => ?_⟩
  · intro i p hp hfr
    have hi : i = 0 := by
      by_contra hi
      simp [sW, hi, nW] at hp
    subst hi
    rw [sW_zero, ew_length] at hp
    obtain ⟨l, hl, rfl⟩ := (twin_eq_iff hp).mp (twin_of_free hp hfr)
    refine ⟨Sm a b c V (st a b c (4 * a + 2 * b + 3 * l + 1)), fun u hu => ?_⟩
    simp only [spt_ew]
    rw [gz_per V hV hp hu, gx, lab_t hl (by omega : 1 < 3)]
    rw [show 1 % 2 = 1 from rfl, h2 l hl]
    simp
  · have hr := rep_lt hk
    have h6 : ∀ t : ℝ, t = 0 ∨ t = 1 → gz a b c V (per (4 * a + 2 * b + 3 * c + 2)
      (rep a b c k + ofs (sgn a b c (rep a b c k)) t)) =
        gx a b c V (rep a b c k) (ofs (sgn a b c (rep a b c k)) t) := fun t ht => gz_per V hV hr
          (ofs_mem' ht)
    have h7 := h6 0 (.inl rfl)
    have h8 := h6 1 (.inr rfl)
    rw [per_st] at h7
    rw [per_en] at h8
    rw [lval, volt, h7, h8, gx, gx, lab_rep hk]
    cases sgn a b c (rep a b c k) <;> norm_num [ofs]

end GraphMinor.Surface
