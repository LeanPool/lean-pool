/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
public import LeanPool.MovingSofa.Development.Geometry.Foundations.CapAreaCertificate
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Development.Geometry.Foundations.NicheAreaCertificate
/-!
# Moving sofa: related mathematical developments

* `Gerver.Foundations.Development001`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Gerver.AreaCertificate`.
* `Gerver.Area.TrigEnclosure`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Exact rational certificate for the Gerver cap and niche areas

The shared numerical prerequisite defines the integer data for the rational area bounds of
Gerver's sofa: integer interval arithmetic at scale `M = 10 ^ 30`, certified enclosures of
the twenty-two direct parameters and of `π`, interval sine and cosine by the Taylor
recurrence, the grid of rotation angles, the five phase formulas, the support-contact fan
of the cap and the rectangle cover of the niche.

The cap and niche certificate modules check the numerical bounds in blocks. The
Boolean lemmas `capOK_true` and `nicheOK_true` reuse those bounds.
`AreaCertificateInputs` describes how to regenerate the subtotals.
-/

/-! ### Integer interval arithmetic at scale `10 ^ 30`

The kernel accelerates `Int` arithmetic but not `Rat` arithmetic, so the whole finite
calculation is carried out on pairs of integers denoting the interval `[lo / M, hi / M]`.
-/

@[expose] public section

namespace MovingSofa.GerverAreaCert

namespace SI

/-! #### Real semantics and soundness -/

/-- `z` denotes the real interval `[z.lo / M, z.hi / M]`. -/
def Contains (z : SI) (x : ℝ) : Prop :=
  (z.lo : ℝ) ≤ (M : ℝ) * x ∧ (M : ℝ) * x ≤ (z.hi : ℝ)

/-- `imin` is `min`. -/
theorem imin_eq_min (a b : ℤ) : imin a b = min a b := by
  simp only [imin, min_def]

/-- `imax` is `max`. -/
theorem imax_eq_max (a b : ℤ) : imax a b = max a b := by
  rcases le_total a b with h | h
  · simp [imax, h]
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp [imax]
    · simp [imax, not_le.mpr hlt, max_eq_left h]

/-- The scale is positive. -/
theorem Mpos : (0 : ℝ) < (M : ℝ) := by
  have : (M : ℤ) = 10 ^ 30 := rfl
  rw [this]
  norm_num

private theorem mul_ediv_le (p : ℤ) {b : ℤ} (hb : 0 < b) : b * (p / b) ≤ p := by
  have h := Int.mul_ediv_add_emod p b
  have h2 : 0 ≤ p % b := Int.emod_nonneg p hb.ne'
  linarith

private theorem le_mul_neg_ediv (p : ℤ) {b : ℤ} (hb : 0 < b) : p ≤ b * -((-p) / b) := by
  have h := mul_ediv_le (-p) hb
  rw [mul_neg]
  linarith

/-- Integer floor division rounds down in the reals. -/
theorem ediv_le_of_le {p : ℤ} {b : ℤ} (hb : 0 < b) {r : ℝ} (h : (p : ℝ) ≤ (b : ℝ) * r) :
    ((p / b : ℤ) : ℝ) ≤ r := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 : ((b : ℝ)) * ((p / b : ℤ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast mul_ediv_le p hb
  have := h1.trans h
  exact le_of_mul_le_mul_left this hbR

/-- Integer ceiling division rounds up in the reals. -/
theorem le_neg_ediv_of_le {p : ℤ} {b : ℤ} (hb : 0 < b) {r : ℝ} (h : (b : ℝ) * r ≤ (p : ℝ)) :
    r ≤ ((-((-p) / b) : ℤ) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1 : (p : ℝ) ≤ (b : ℝ) * ((-((-p) / b) : ℤ) : ℝ) := by
    exact_mod_cast le_mul_neg_ediv p hb
  exact le_of_mul_le_mul_left (h.trans h1) hbR

private theorem min_mul_le_mul {l h u v : ℝ} (hl : l ≤ u) (hu : u ≤ h) :
    min (l * v) (h * v) ≤ u * v := by
  rcases le_total 0 v with hv | hv
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

private theorem mul_le_max_mul {l h u v : ℝ} (hl : l ≤ u) (hu : u ≤ h) :
    u * v ≤ max (l * v) (h * v) := by
  rcases le_total 0 v with hv | hv
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

private theorem min_four_le_mul {l₁ h₁ l₂ h₂ u v : ℝ}
    (h1 : l₁ ≤ u) (h2 : u ≤ h₁) (h3 : l₂ ≤ v) (h4 : v ≤ h₂) :
    min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * v := by
  have hA : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ min (l₁ * l₂) (h₁ * l₂) :=
    le_min ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  have hB : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ min (l₁ * h₂) (h₁ * h₂) :=
    le_min ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
  have h5 : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * l₂ :=
    hA.trans (min_mul_le_mul h1 h2)
  have h6 : min (min (l₁ * l₂) (l₁ * h₂)) (min (h₁ * l₂) (h₁ * h₂)) ≤ u * h₂ :=
    hB.trans (min_mul_le_mul h1 h2)
  have h7 : min (u * l₂) (u * h₂) ≤ u * v := by
    simpa [mul_comm] using min_mul_le_mul (l := l₂) (h := h₂) (u := v) (v := u) h3 h4
  exact (le_min h5 h6).trans h7

private theorem mul_le_max_four {l₁ h₁ l₂ h₂ u v : ℝ}
    (h1 : l₁ ≤ u) (h2 : u ≤ h₁) (h3 : l₂ ≤ v) (h4 : v ≤ h₂) :
    u * v ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) := by
  have hA : max (l₁ * l₂) (h₁ * l₂) ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) :=
    max_le ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have hB : max (l₁ * h₂) (h₁ * h₂) ≤ max (max (l₁ * l₂) (l₁ * h₂)) (max (h₁ * l₂) (h₁ * h₂)) :=
    max_le ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  have h7 : u * v ≤ max (u * l₂) (u * h₂) := by
    simpa [mul_comm] using mul_le_max_mul (l := l₂) (h := h₂) (u := v) (v := u) h3 h4
  exact h7.trans (max_le ((mul_le_max_mul h1 h2).trans hA) ((mul_le_max_mul h1 h2).trans hB))

/-- Interval addition is sound. -/
theorem contains_add {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (add x y) (a + b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩ <;> push_cast [add] <;> nlinarith [Mpos]

/-- Interval negation is sound. -/
theorem contains_neg {x : SI} {a : ℝ} (hx : Contains x a) : Contains (neg x) (-a) := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨?_, ?_⟩ <;> push_cast [neg] <;> nlinarith [Mpos]

/-- Interval subtraction is sound. -/
theorem contains_sub {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (sub x y) (a - b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩ <;> push_cast [sub] <;> nlinarith [Mpos]

/-- Interval multiplication is sound. -/
theorem contains_mul {x y : SI} {a b : ℝ} (hx : Contains x a) (hy : Contains y b) :
    Contains (mul x y) (a * b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hM := Mpos
  have hprod : (M : ℝ) * ((M : ℝ) * (a * b)) = ((M : ℝ) * a) * ((M : ℝ) * b) := by ring
  refine ⟨?_, ?_⟩
  · simp only [mul, imin_eq_min, imax_eq_max]
    refine ediv_le_of_le (b := M) (by exact_mod_cast hM) ?_
    push_cast
    rw [hprod]
    exact min_four_le_mul hx1 hx2 hy1 hy2
  · simp only [mul, imin_eq_min, imax_eq_max]
    refine le_neg_ediv_of_le (b := M) (by exact_mod_cast hM) ?_
    push_cast
    rw [hprod]
    exact mul_le_max_four hx1 hx2 hy1 hy2

/-- Interval division by a positive integer is sound. -/
theorem contains_divn {x : SI} {a : ℝ} {b : ℤ} (hb : 0 < b) (hx : Contains x a) :
    Contains (divn x b) (a / (b : ℝ)) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : (b : ℝ) * ((M : ℝ) * (a / (b : ℝ))) = (M : ℝ) * a := by
    field_simp
  refine ⟨ediv_le_of_le hb ?_, le_neg_ediv_of_le hb ?_⟩
  · rw [hkey]; exact hx1
  · rw [hkey]; exact hx2

/-- Interval multiplication by an integer is sound. -/
theorem contains_imul {x : SI} {a : ℝ} (k : ℤ) (hx : Contains x a) :
    Contains (imul k x) ((k : ℝ) * a) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hkey : (M : ℝ) * ((k : ℝ) * a) = (k : ℝ) * ((M : ℝ) * a) := by ring
  refine ⟨?_, ?_⟩ <;> simp only [imul, imin_eq_min, imax_eq_max] <;> push_cast <;> rw [hkey]
  · simpa [mul_comm] using min_mul_le_mul (l := (x.lo : ℝ)) (h := (x.hi : ℝ))
      (u := (M : ℝ) * a) (v := (k : ℝ)) hx1 hx2
  · simpa [mul_comm] using mul_le_max_mul (l := (x.lo : ℝ)) (h := (x.hi : ℝ))
      (u := (M : ℝ) * a) (v := (k : ℝ)) hx1 hx2

/-- The outward enclosure of a rational is sound. -/
theorem contains_ratI {a b : ℤ} (hb : 0 < b) : Contains (ratI a b) ((a : ℝ) / (b : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : (b : ℝ) * ((M : ℝ) * ((a : ℝ) / (b : ℝ))) = ((a * M : ℤ) : ℝ) := by
    push_cast
    field_simp
  refine ⟨ediv_le_of_le hb ?_, le_neg_ediv_of_le hb ?_⟩
  · rw [hkey]
  · rw [hkey]

/-- `zero` encloses `0`. -/
theorem contains_zero : Contains zero 0 := by
  constructor <;> simp [zero]

/-- `one` encloses `1`. -/
theorem contains_one : Contains one 1 := by
  constructor <;> simp [one]

/-- A left fold of exact interval additions over an initial segment encloses the
corresponding real sum. -/
theorem contains_foldl_range {f : ℕ → SI} {g : ℕ → ℝ} (n : ℕ)
    (hfg : ∀ i < n, Contains (f i) (g i)) :
    Contains ((List.range n).foldl (fun acc i => add acc (f i)) zero)
      (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa using contains_zero
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    exact contains_add (ih fun i hi => hfg i (by omega)) (hfg n (by omega))

/-- A left fold of integer additions over an initial segment is the corresponding sum. -/
theorem foldl_range_int (f : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]; simp

end SI

open SI

/-! #### The parameter enclosures are the certified box rows -/

private theorem le_M_mul {c n : ℤ} {d : ℕ} (hd : 0 < (d : ℤ)) (hc : c * (d : ℤ) = n * M)
    {x : ℝ} (h : (n : ℝ) / (d : ℝ) ≤ x) : (c : ℝ) ≤ (M : ℝ) * x := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcR : (c : ℝ) * (d : ℝ) = (n : ℝ) * (M : ℝ) := by exact_mod_cast hc
  rw [div_le_iff₀ hdR] at h
  nlinarith [SI.Mpos, h, hcR]

private theorem M_mul_le {c n : ℤ} {d : ℕ} (hd : 0 < (d : ℤ)) (hc : c * (d : ℤ) = n * M)
    {x : ℝ} (h : x ≤ (n : ℝ) / (d : ℝ)) : (M : ℝ) * x ≤ (c : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcR : (c : ℝ) * (d : ℝ) = (n : ℝ) * (M : ℝ) := by exact_mod_cast hc
  rw [le_div_iff₀ hdR] at h
  nlinarith [SI.Mpos, h, hcR]

/-- Every one of the twenty-two integer enclosures contains the corresponding certified
Gerver parameter. -/
theorem contains_params :
      SI.Contains k11Z GerverSofa.PartB.params.k11 ∧
      SI.Contains k12Z GerverSofa.PartB.params.k12 ∧
      SI.Contains k21Z GerverSofa.PartB.params.k21 ∧
      SI.Contains k22Z GerverSofa.PartB.params.k22 ∧
      SI.Contains k31Z GerverSofa.PartB.params.k31 ∧
      SI.Contains k32Z GerverSofa.PartB.params.k32 ∧
      SI.Contains k41Z GerverSofa.PartB.params.k41 ∧
      SI.Contains k42Z GerverSofa.PartB.params.k42 ∧
      SI.Contains k51Z GerverSofa.PartB.params.k51 ∧
      SI.Contains k52Z GerverSofa.PartB.params.k52 ∧
      SI.Contains a1Z GerverSofa.PartB.params.a1 ∧
      SI.Contains a2Z GerverSofa.PartB.params.a2 ∧
      SI.Contains b1Z GerverSofa.PartB.params.b1 ∧
      SI.Contains b2Z GerverSofa.PartB.params.b2 ∧
      SI.Contains c1Z GerverSofa.PartB.params.c1 ∧
      SI.Contains c2Z GerverSofa.PartB.params.c2 ∧
      SI.Contains d1Z GerverSofa.PartB.params.d1 ∧
      SI.Contains d2Z GerverSofa.PartB.params.d2 ∧
      SI.Contains e1Z GerverSofa.PartB.params.e1 ∧
      SI.Contains e2Z GerverSofa.PartB.params.e2 ∧
      SI.Contains phiZ GerverSofa.PartB.params.phi ∧
      SI.Contains thetaZ GerverSofa.PartB.params.theta := by
  have hbox := GerverSofa.PartB.params_mem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨hk11lo, hk11hi, hk12lo, hk12hi, hk21lo, hk21hi, hk22lo, hk22hi, hk31lo, hk31hi,
      hk32lo, hk32hi, hk41lo, hk41hi, hk42lo, hk42hi, hk51lo, hk51hi, hk52lo, hk52hi,
      ha1lo, ha1hi, ha2lo, ha2hi, hb1lo, hb1hi, hb2lo, hb2hi, hc1lo, hc1hi, hc2lo, hc2hi,
      hd1lo, hd1hi, hd2lo, hd2hi, he1lo, he1hi, he2lo, he2hi, hphilo, hphihi, hthetalo,
      hthetahi⟩ := hbox
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k11Z]) hk11lo,
    M_mul_le (by norm_num) (by norm_num [M, k11Z]) hk11hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k12Z]) hk12lo,
    M_mul_le (by norm_num) (by norm_num [M, k12Z]) hk12hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k21Z]) hk21lo,
    M_mul_le (by norm_num) (by norm_num [M, k21Z]) hk21hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k22Z]) hk22lo,
    M_mul_le (by norm_num) (by norm_num [M, k22Z]) hk22hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k31Z]) hk31lo,
    M_mul_le (by norm_num) (by norm_num [M, k31Z]) hk31hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k32Z]) hk32lo,
    M_mul_le (by norm_num) (by norm_num [M, k32Z]) hk32hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k41Z]) hk41lo,
    M_mul_le (by norm_num) (by norm_num [M, k41Z]) hk41hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k42Z]) hk42lo,
    M_mul_le (by norm_num) (by norm_num [M, k42Z]) hk42hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k51Z]) hk51lo,
    M_mul_le (by norm_num) (by norm_num [M, k51Z]) hk51hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, k52Z]) hk52lo,
    M_mul_le (by norm_num) (by norm_num [M, k52Z]) hk52hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, a1Z]) ha1lo,
    M_mul_le (by norm_num) (by norm_num [M, a1Z]) ha1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, a2Z]) ha2lo,
    M_mul_le (by norm_num) (by norm_num [M, a2Z]) ha2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, b1Z]) hb1lo,
    M_mul_le (by norm_num) (by norm_num [M, b1Z]) hb1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, b2Z]) hb2lo,
    M_mul_le (by norm_num) (by norm_num [M, b2Z]) hb2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, c1Z]) hc1lo,
    M_mul_le (by norm_num) (by norm_num [M, c1Z]) hc1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, c2Z]) hc2lo,
    M_mul_le (by norm_num) (by norm_num [M, c2Z]) hc2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, d1Z]) hd1lo,
    M_mul_le (by norm_num) (by norm_num [M, d1Z]) hd1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, d2Z]) hd2lo,
    M_mul_le (by norm_num) (by norm_num [M, d2Z]) hd2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, e1Z]) he1lo,
    M_mul_le (by norm_num) (by norm_num [M, e1Z]) he1hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, e2Z]) he2lo,
    M_mul_le (by norm_num) (by norm_num [M, e2Z]) he2hi⟩, ?_⟩
  refine ⟨⟨le_M_mul (by norm_num) (by norm_num [M, phiZ]) hphilo,
    M_mul_le (by norm_num) (by norm_num [M, phiZ]) hphihi⟩, ?_⟩
  exact ⟨le_M_mul (by norm_num) (by norm_num [M, thetaZ]) hthetalo,
    M_mul_le (by norm_num) (by norm_num [M, thetaZ]) hthetahi⟩

/-- The integer enclosure of `π`. -/
theorem contains_piZ : SI.Contains piZ Real.pi := by
  obtain ⟨h1, h2⟩ := GerverSofa.ExactReplay.piI_contains_pi
  have hM := SI.Mpos
  refine ⟨?_, ?_⟩
  · have hnum : ((piZ.lo : ℤ) : ℝ) ≤ (M : ℝ) * ((GerverSofa.ExactReplay.piI.lo : ℚ) : ℝ) := by
      norm_num [piZ, M, GerverSofa.ExactReplay.piI, GerverSofa.ExactReplay.q]
    nlinarith [h1]
  · have hnum : (M : ℝ) * ((GerverSofa.ExactReplay.piI.hi : ℚ) : ℝ) ≤ ((piZ.hi : ℤ) : ℝ) := by
      norm_num [piZ, M, GerverSofa.ExactReplay.piI, GerverSofa.ExactReplay.q]
    nlinarith [h2]

/-- The integer enclosure of `π / 2`. -/
theorem contains_piHalfZ : SI.Contains piHalfZ (Real.pi / 2) := by
  change SI.Contains (SI.divn piZ 2) (Real.pi / 2)
  simpa using SI.contains_divn (b := 2) (by norm_num) contains_piZ

/-- The Boolean niche check follows from the staged integer bound. -/
theorem nicheOK_true : nicheOK = true := by
  unfold nicheOK
  exact decide_eq_true niche_bound_checked

/-- The Boolean cap check follows from the staged integer bound. -/
theorem capOK_true : capOK = true := by
  unfold capOK
  exact decide_eq_true cap_bound_checked

end MovingSofa.GerverAreaCert

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Interval enclosures of the sine and cosine at scale `M`

The certificate evaluates the sine and the cosine by the interval Taylor recurrence
`GerverAreaCert.trigIter`, truncated at degree 41 and 40 and widened by one unit at scale
`M = 10 ^ 30`.  `trigZ_sound` is the soundness statement of that evaluator on `[0, 2]`: the
recurrence encloses the signed Taylor terms and their partial sums (`contains_trigIter`),
the alternating brackets of `Real.sin` and `Real.cos` control the truncation error by the
first omitted term, and `2 ^ 41 * 10 ^ 30 ≤ 41!` and `2 ^ 40 * 10 ^ 30 ≤ 40!` justify the
one-unit widening.
-/

/-! ### Sine and cosine enclosures -/

@[expose] public section

namespace MovingSofa

open GerverAreaCert

/-- The integer term recurrence encloses the signed Taylor terms and their partial
sums.  Pure interval arithmetic: an induction on `n` using the `SI` soundness lemmas. -/
theorem contains_trigIter {z t : SI} {x : ℝ} (hz : SI.Contains z (x * x))
    (ht : SI.Contains t x) (n : ℕ) :
    SI.Contains (trigIter z t n).1
        ((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.1
        ((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.1
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) ∧
      SI.Contains (trigIter z t n).2.2.2
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  induction n with
  | zero =>
    refine ⟨by simpa [trigIter] using ht, by simpa [trigIter] using SI.contains_one,
      by simpa [trigIter] using ht, ?_⟩
    simpa [trigIter] using SI.contains_one
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hfac1 : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfac2 : (Nat.factorial (2 * n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hd1 : (0 : ℤ) < (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) := by positivity
    have hd2 : (0 : ℤ) < (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) := by positivity
    have hd1' : ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd1
      exact ne_of_gt this
    have hd2' : ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hd2
      exact ne_of_gt this
    have e1 : (Nat.factorial (2 * (n + 1) + 1) : ℝ) =
        (Nat.factorial (2 * n + 1) : ℝ) * ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have e2 : (Nat.factorial (2 * (n + 1)) : ℝ) =
        (Nat.factorial (2 * n) : ℝ) * ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ) := by
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have v1 : -((((-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) * (x * x)) /
          ((((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
      rw [e1, show x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * (x * x) by ring]
      field_simp
      ring
    have v2 : -((((-1 : ℝ) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * (x * x)) /
          ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ) : ℝ)) =
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ) := by
      rw [e2, show x ^ (2 * (n + 1)) = x ^ (2 * n) * (x * x) by ring]
      field_simp
      ring
    have hs : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).1 z) (((2 * n + 2) * (2 * n + 3) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1) + 1) /
          (Nat.factorial (2 * (n + 1) + 1) : ℝ)) := by
      rw [← v1]
      exact SI.contains_neg (SI.contains_divn hd1 (SI.contains_mul ih1 hz))
    have hc : SI.Contains
        (SI.neg (SI.divn (SI.mul (trigIter z t n).2.1 z) (((2 * n + 1) * (2 * n + 2) : ℕ) : ℤ)))
        ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / (Nat.factorial (2 * (n + 1)) : ℝ)) := by
      rw [← v2]
      exact SI.contains_neg (SI.contains_divn hd2 (SI.contains_mul ih2 hz))
    refine ⟨hs, hc, ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih3 hs
    · rw [Finset.sum_range_succ]
      exact SI.contains_add ih4 hc

/-- The degree-41 sine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem sin_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) -
        1 / (M : ℝ) ≤ Real.sin x ∧
      Real.sin x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.sin_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
        + x ^ 41 / (Nat.factorial 41 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 41 / (Nat.factorial 41 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 41 / (Nat.factorial 41 : ℝ) ≤ (2 : ℝ) ^ 41 / (Nat.factorial 41 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- The degree-40 cosine Taylor polynomial overshoots by at most `1 / M` on `[0, 2]`. -/
private theorem cos_taylor_bracket {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) -
        1 / (M : ℝ) ≤ Real.cos x ∧
      Real.cos x ≤ ∑ k ∈ Finset.range 21,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
  obtain ⟨hlow, hhigh⟩ := Real.cos_mem_Icc_taylor_sums 10 hx0 (by push_cast; nlinarith)
  simp only [show (2 * 10 + 1 : ℕ) = 21 from rfl, show (2 * 10 : ℕ) = 20 from rfl] at hlow hhigh
  refine ⟨?_, hhigh⟩
  have hsplit : (∑ k ∈ Finset.range 21,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      = (∑ k ∈ Finset.range 20,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
        + x ^ 40 / (Nat.factorial 40 : ℝ) := by
    rw [show (21 : ℕ) = 20 + 1 from rfl, Finset.sum_range_succ]
    norm_num
  have htail : x ^ 40 / (Nat.factorial 40 : ℝ) ≤ 1 / (M : ℝ) := by
    have hMv : ((M : ℤ) : ℝ) = 10 ^ 30 := by norm_num [M]
    rw [hMv]
    calc x ^ 40 / (Nat.factorial 40 : ℝ) ≤ (2 : ℝ) ^ 40 / (Nat.factorial 40 : ℝ) := by gcongr
      _ ≤ 1 / 10 ^ 30 := by norm_num [Nat.factorial]
  rw [hsplit]
  linarith

/-- Soundness of the executable sine/cosine enclosure on `[0, 2]`. -/
theorem trigZ_sound {t : SI} {x : ℝ} (ht : SI.Contains t x) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    SI.Contains (trigZ t).1 (Real.sin x) ∧ SI.Contains (trigZ t).2 (Real.cos x) := by
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hMinv : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  have hwiden : ∀ (S : SI) (y v : ℝ), SI.Contains S v → v - 1 / (M : ℝ) ≤ y → y ≤ v →
      SI.Contains (⟨S.lo - 1, S.hi + 1⟩ : SI) y := by
    intro S y v hS h1 h2
    obtain ⟨ha, hb⟩ := hS
    have hlow : (M : ℝ) * v - 1 ≤ (M : ℝ) * y := by
      have h := mul_le_mul_of_nonneg_left h1 hM.le
      nlinarith [hMinv]
    have hhigh : (M : ℝ) * y ≤ (M : ℝ) * v := mul_le_mul_of_nonneg_left h2 hM.le
    refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have h20 : (20 : ℕ) + 1 = 21 := by norm_num
  have hz : SI.Contains (SI.mul t t) (x * x) := SI.contains_mul ht ht
  obtain ⟨-, -, hS, hC⟩ := contains_trigIter hz ht 20
  rw [h20] at hS hC
  obtain ⟨hs1, hs2⟩ := sin_taylor_bracket hx0 hx2
  obtain ⟨hc1, hc2⟩ := cos_taylor_bracket hx0 hx2
  exact ⟨hwiden _ (Real.sin x) _ hS hs1 hs2, hwiden _ (Real.cos x) _ hC hc1 hc2⟩

end MovingSofa

end

end

end

end

end
