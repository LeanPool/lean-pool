/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Derivation
public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# The trace-form differential of a Mumford datum

The pullback of the standard regular differentials along a family of Mumford data, in a form
that needs no trace and no separability.  For a datum `(u, v)` over a ring carrying a
derivation `d` — in the applications, `d/dx` on the function field, and `∂/∂Y_k` on the
two-variable power series ring where the formal group law lives — set

`traceDiff d u s k = -topCoeffMod u (X^k · u_dot · s)`,

where `u_dot` differentiates the *coefficients* of `u` (`Derivation.dotDer`) and `s` is a
Bézout cofactor inverting `2v` modulo `u`, which the Cantor pipeline already carries as a
certificate.  Classically this is `∑ᵢ xᵢ^k·D(xᵢ)/(2yᵢ)` summed over the points of the divisor,
i.e. the pullback of `x^k dx/(2y)`.

## Main statements

* `ChabautyColeman.traceDiff_eq_zero_of_dotDer_eq_zero`: a datum with constant coefficients has
  vanishing trace-form differential.
* `ChabautyColeman.traceDiff_mul`: **additivity under Cantor composition**, with *no*
  coprimality hypothesis on the two `u`-parts — the doubling case `u₁ = u₂`, which the formal
  group law construction needs, is covered.
* `ChabautyColeman.traceDiff_reduce_of_dvd_dotDer`: **invariance under Cantor reduction**, on
  a curve of odd degree `2g+1` and for `k < g`, and *across a singular reduction step*: the
  input datum `(u·B, v)` may contain Weierstrass points, provided they sit in a `d`-constant
  monic factor `B` with `B ∣ v_dot` — then no Bézout certificate modulo `u·B` exists, but the
  value of the reduced datum still equals that of the moving part `(u, v)`. This is what
  crosses the centre pair block of a Weierstrass-centred pipeline.
* `ChabautyColeman.traceDiff_reduce`: its case `B = 1`, the ordinary reduction step.
  `ChabautyColeman.traceDiff_reduce_of_dvd_dotDer_of_natDegree_lt` and
  `ChabautyColeman.traceDiff_reduce_of_natDegree_lt` are the versions over any commutative
  ring, with the degree side condition as a hypothesis.
* `ChabautyColeman.traceDiff_congr`: the value does not depend on the choice of cofactor, so
  the certificate may be changed freely along a chain.
* `ChabautyColeman.traceDiff_eq_sum`: in chart coordinates the differential is the linear form
  `∑_j C_kj·D(ζ_j)` in the derivatives of the coordinates, with `C` the Hankel matrix
  `ChabautyColeman.traceMat`.
* `ChabautyColeman.traceDiff_pair`: the value on a **moving pair block**, `α^k·D(α)/(2v(α))` —
  the pullback of `x^k dx/(2y)` at the moving point.
* `ChabautyColeman.traceDiff_single`: the same for a **single moving point** with degree-one
  `u`-part — the block of the infinity-centred configuration `[P - ∞] + τ`.

## Implementation notes

Indices are `0`-based: `k = 0, …, g-1` corresponds to the differentials `x^k dx/(2y)`.

The coefficient description of the functional is not merely a convenience.  The trace form
`Tr(p/u')` requires `u'` to be invertible modulo `u`, i.e. `u` squarefree, and the pipeline's
own compositions produce non-squarefree `u`-parts; `Polynomial.topCoeffMod` is defined
regardless.  It does require `u` monic, which Mumford `u`-parts always are.

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Pair

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- For a modulus with two prescribed roots, the functional is the divided difference: this is
Lagrange interpolation in the only case the pair blocks need. -/
theorem sub_mul_topCoeffMod_pair (a b : R) (p : R[X]) :
    (a - b) * topCoeffMod ((X - C a) * (X - C b)) p = p.eval a - p.eval b := by
  have hum : ((X - C a) * (X - C b)).Monic := (monic_X_sub_C a).mul (monic_X_sub_C b)
  have hdeg : ((X - C a) * (X - C b)).natDegree = 2 := by
    rw [(monic_X_sub_C a).natDegree_mul (monic_X_sub_C b), natDegree_X_sub_C, natDegree_X_sub_C]
  -- evaluation at a root sees only the remainder, which is linear
  have hev (z : R) (hz : ((X - C a) * (X - C b)).eval z = 0) :
      p.eval z = (p %ₘ ((X - C a) * (X - C b))).eval z := by
    nth_rw 1 [← modByMonic_add_div p ((X - C a) * (X - C b))]
    simp [hz]
  have hlin : p %ₘ ((X - C a) * (X - C b))
      = C ((p %ₘ ((X - C a) * (X - C b))).coeff 1)
        * X + C ((p %ₘ ((X - C a) * (X - C b))).coeff 0) := by
    refine eq_X_add_C_of_degree_le_one ?_
    have h := degree_modByMonic_lt p hum
    rw [degree_eq_natDegree hum.ne_zero, hdeg] at h
    exact Order.le_of_lt_succ (mod_cast h)
  rw [topCoeffMod, hdeg, hev a (by simp), hev b (by simp)]
  conv_rhs => rw [hlin]
  simp only [eval_add, eval_mul, eval_C, eval_X, show (2 : ℕ) - 1 = 1 from rfl]
  ring

end Pair


variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]

variable (d : Derivation S A A)

/-- **The trace-form differential** of a Mumford datum, in the coefficient form.

`traceDiff d u s k` is `-λ_u(X^k · u_dot · s)`, where `u_dot` differentiates the coefficients of `u`
and `s` is a Bézout cofactor inverting `2v` modulo `u` — the certificate the Cantor pipeline
already carries. Classically it is `∑ᵢ xᵢ^k · D(xᵢ)/(2yᵢ)` over the points of the divisor, i.e.
the pullback of the `(k+1)`-st standard regular differential `x^k dx/(2y)`; the coefficient
description needs neither the trace form nor separability of `u`, and — unlike the trace form —
is defined even when `u` is not squarefree, which the Cantor pipeline's own compositions
produce. Indices are `0`-based: `k = 0, …, g-1`. -/
noncomputable def traceDiff (u s : A[X]) (k : ℕ) : A :=
  -topCoeffMod u (X ^ k * d.dotDer u * s)

/-- **(T4) A datum with constant coefficients has vanishing trace-form differential.** -/
theorem traceDiff_eq_zero_of_dotDer_eq_zero {u : A[X]} (hu : ∀ i, d (u.coeff i) = 0) (s : A[X])
    (k : ℕ) :
    traceDiff d u s k = 0 := by
  rw [traceDiff, d.dotDer_eq_zero_of_coeff hu, mul_zero, zero_mul, topCoeffMod_zero, neg_zero]


section Chart

variable {u u₀ : A[X]} {n : ℕ} {ζ : Fin n → A}

/-- The matrix of the trace-form differential in chart coordinates: a Hankel matrix, since
`i` and `j` enter only through `i + j`. -/
noncomputable def traceMat (u s : A[X]) (i j : ℕ) : A := -topCoeffMod u (X ^ (i + j) * s)

theorem traceMat_map {B : Type*} [CommRing B] [Nontrivial B] (φ : A →+* B)
    (hu : u.Monic) (s : A[X]) (i j : ℕ) :
    traceMat (u.map φ) (s.map φ) i j = φ (traceMat u s i j) := by
  rw [traceMat, traceMat, map_neg, ← topCoeffMod_map φ hu, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X]

/-- **The trace-form differential in chart coordinates.** For a datum whose `u`-part is a
center with constant coefficients perturbed by the chart coordinates `ζ`, the differential is
the linear form `∑_j C_kj·D(ζ_j)` in their derivatives, the form in which the trace identities
on the residue disks use it (`LeanPool.HyperellipticCurves.Log.Trace.TraceKz`). -/
theorem traceDiff_eq_sum (hu₀ : ∀ i, d (u₀.coeff i) = 0)
    (hu : u = u₀ + ∑ j : Fin n, C (ζ j) * X ^ (j : ℕ)) (s : A[X]) (k : ℕ) :
    traceDiff d u s k = ∑ j : Fin n, traceMat u s k j * d (ζ j) := by
  have hdot : d.dotDer u = ∑ j : Fin n, C (d (ζ j)) * X ^ (j : ℕ) := by
    rw [hu, map_add, d.dotDer_eq_zero_of_coeff hu₀, zero_add, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Derivation.dotDer_C_mul_X_pow d (ζ j) j
  rw [traceDiff, hdot, Finset.mul_sum, Finset.sum_mul, topCoeffMod_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show X ^ k * (C (d (ζ j)) * X ^ (j : ℕ)) * s = C (d (ζ j)) * (X ^ (k + j) * s) by
    ring, topCoeffMod_C_mul, traceMat]
  ring

end Chart

variable {u u₁ u₂ v v₁ v₂ v₃ c₁ c₂ c₃ s s₁ s₂ s₃ : A[X]}

/-- Two Bézout cofactors inverting `2v` agree modulo `u` as soon as the `v`s do: the inverse
of a unit is unique. This is what lets the composed certificate `s₃` be replaced by the block
certificates `s₁`, `s₂` inside the functional. -/
theorem dvd_sub_of_bezout (hs₁ : c₁ * u₁ + s₁ * (2 * v₁) = 1)
    (hs₃ : c₃ * (u₁ * u₂) + s₃ * (2 * v₃) = 1) (h₁ : u₁ ∣ v₃ - v₁) :
    u₁ ∣ s₃ - s₁ := by
  obtain ⟨a, ha⟩ := h₁
  exact ⟨s₃ * c₁ - s₁ * c₃ * u₂ - 2 * s₁ * s₃ * a,
    by linear_combination -s₃ * hs₁ + s₁ * hs₃ - 2 * s₁ * s₃ * ha⟩

/-- A Bézout cofactor for `2v` modulo `u` serves for every `w` congruent to `v` modulo `u`:
the cofactor itself is unchanged, only its companion moves. -/
theorem exists_bezout_of_dvd_sub (hs₁ : c₁ * u₁ + s₁ * (2 * v₁) = 1) (h : u₁ ∣ v₁ - v₂) :
    ∃ c, c * u₁ + s₁ * (2 * v₂) = 1 := by
  obtain ⟨t, ht⟩ := h
  exact ⟨c₁ + 2 * s₁ * t, by linear_combination hs₁ - 2 * s₁ * ht⟩

/-- The certificate of a *reduced* datum inverts `2v` for the original `v` too: reduction
flips the sign of the `v`-part, and `-1` is a unit. -/
theorem isCoprime_two_mul_of_dvd_add (hs₁ : c₁ * u₁ + s₁ * (2 * v₁) = 1) (h : u₁ ∣ v₁ + v₂) :
    IsCoprime u₁ (2 * v₂) := by
  obtain ⟨c, hc⟩ := exists_bezout_of_dvd_sub hs₁ (v₂ := -v₂) (by simpa using h)
  exact ⟨c, -s₁, by linear_combination hc⟩

/-- An inverse of `2v` modulo `u` is unique modulo `u`. -/
theorem dvd_sub_of_bezout_of_bezout (hs₁ : c₁ * u + s₁ * (2 * v) = 1)
    (hs₂ : c₂ * u + s₂ * (2 * v) = 1) : u ∣ s₁ - s₂ :=
  dvd_sub_of_bezout (u₂ := 1) (v₃ := v) (c₃ := c₁) hs₂ (by linear_combination hs₁) (by simp)

/-- The trace-form differential does not depend on the choice of Bézout cofactor: the
functional only sees `u`-residues. -/
theorem traceDiff_congr (hu : u.Monic) (hs₁ : c₁ * u + s₁ * (2 * v) = 1)
    (hs₂ : c₂ * u + s₂ * (2 * v) = 1) (k : ℕ) : traceDiff d u s₁ k = traceDiff d u s₂ k :=
  congrArg Neg.neg (topCoeffMod_congr hu
    (by rw [← mul_sub]; exact (dvd_sub_of_bezout_of_bezout hs₁ hs₂).mul_left _))

/-- Nor does the trace matrix. -/
theorem traceMat_congr (hu : u.Monic) (hs₁ : c₁ * u + s₁ * (2 * v) = 1)
    (hs₂ : c₂ * u + s₂ * (2 * v) = 1) (i j : ℕ) : traceMat u s₁ i j = traceMat u s₂ i j :=
  congrArg Neg.neg (topCoeffMod_congr hu
    (by rw [← mul_sub]; exact (dvd_sub_of_bezout_of_bezout hs₁ hs₂).mul_left _))

section Nontrivial

variable [Nontrivial A]

/-- **(T1) The trace-form differential is additive under Cantor composition.** No coprimality
of `u₁`, `u₂` is required — the localization lemma `topCoeffMod_mul_monic` allows `u₂ = u₁` —
which is what the doubling case needs. -/
theorem traceDiff_mul (hu₁ : u₁.Monic) (hu₂ : u₂.Monic)
    (hs₁ : c₁ * u₁ + s₁ * (2 * v₁) = 1) (hs₂ : c₂ * u₂ + s₂ * (2 * v₂) = 1)
    (hs₃ : c₃ * (u₁ * u₂) + s₃ * (2 * v₃) = 1)
    (h₁ : u₁ ∣ v₃ - v₁) (h₂ : u₂ ∣ v₃ - v₂) (k : ℕ) :
    traceDiff d (u₁ * u₂) s₃ k = traceDiff d u₁ s₁ k + traceDiff d u₂ s₂ k := by
  have hdot : d.dotDer (u₁ * u₂) = d.dotDer u₁ * u₂ + u₁ * d.dotDer u₂ := d.dotDer_mul u₁ u₂
  -- the composed certificate may be replaced by the block certificates
  have hd₁ : u₁ ∣ X ^ k * d.dotDer u₁ * s₃ - X ^ k * d.dotDer u₁ * s₁ := by
    rw [← mul_sub]
    exact (dvd_sub_of_bezout hs₁ hs₃ h₁).mul_left _
  have hd₂ : u₂ ∣ X ^ k * d.dotDer u₂ * s₃ - X ^ k * d.dotDer u₂ * s₂ := by
    rw [← mul_sub]
    exact (dvd_sub_of_bezout hs₂
      (show c₃ * (u₂ * u₁) + s₃ * (2 * v₃) = 1 by linear_combination hs₃) h₂).mul_left _
  rw [traceDiff, traceDiff, traceDiff, hdot, ← neg_add]
  congr 1
  rw [show X ^ k * (d.dotDer u₁ * u₂ + u₁ * d.dotDer u₂) * s₃
      = X ^ k * d.dotDer u₁ * s₃ * u₂ + X ^ k * d.dotDer u₂ * s₃ * u₁ by ring,
    topCoeffMod_add, topCoeffMod_mul_monic hu₁ hu₂,
    mul_comm u₁ u₂, topCoeffMod_mul_monic hu₂ hu₁,
    topCoeffMod_congr hu₁ hd₁, topCoeffMod_congr hu₂ hd₂]

/-- **(T1′) The trace-form differential of a split datum is the sum over its points**: for a datum
whose support splits into linear factors, the trace-form differential is the sum of the per-point
ones, each taken at a certificate for a `v`-value congruent to the datum's at that point. Iterates
`ChabautyColeman.traceDiff_mul`, so repeated points are allowed. This aggregates the moving points
in the invariance identity of the trace form along the fold pipeline
(`ChabautyColeman.sum_traceMat_ftauFoldPipe`). -/
theorem traceDiff_prod {ι : Type*} {t : ι → A} {sn : Finset ι} {v cu su : A[X]}
    {c sf vf : ι → A[X]}
    (hsu : cu * (∏ i ∈ sn, (X - C (t i))) + su * (2 * v) = 1)
    (hs : ∀ i ∈ sn, c i * (X - C (t i)) + sf i * (2 * vf i) = 1)
    (hdvd : ∀ i ∈ sn, (X - C (t i)) ∣ v - vf i) (k : ℕ) :
    traceDiff d (∏ i ∈ sn, (X - C (t i))) su k
      = ∑ i ∈ sn, traceDiff d (X - C (t i)) (sf i) k := by
  classical
  induction sn using Finset.induction_on generalizing cu with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact traceDiff_eq_zero_of_dotDer_eq_zero d
      (fun i ↦ by simp [coeff_one, apply_ite]) su k
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at hsu
    have hsu' : cu * (X - C (t a)) * (∏ i ∈ s, (X - C (t i))) + su * (2 * v) = 1 := by
      linear_combination hsu
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      traceDiff_mul d (monic_X_sub_C (t a))
        (monic_prod_of_monic s _ fun i _ ↦ monic_X_sub_C (t i))
        (hs a (Finset.mem_insert_self a s)) hsu'
        hsu (hdvd a (Finset.mem_insert_self a s)) (by simp) k,
      ih hsu'
        (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hdvd i (Finset.mem_insert_of_mem hi)]

variable {u' v' f s' cu1 cu2 : A[X]} {c cw : A} {g k : ℕ}

/-- **(T2′) Cantor reduction of a datum with a `d`-constant factor.** For an input datum
`(u·B, v)` whose factor `B` is `d`-constant and divides `v_dot`, the trace-form differential of
the reduced datum equals that of the moving part `(u, v)` alone: a Bézout certificate is
needed only modulo `u`, so the input datum may contain Weierstrass points — as long as they
sit in the constant factor `B`. This crosses the reduction step that is genuinely singular
for `ChabautyColeman.traceDiff_reduce_of_natDegree_lt`, e.g. at a centre pair block through a
Weierstrass point: there `v` and `f` share a root of `B`, so no certificate inverts `2v`
modulo `u·B` — but `B ∣ v_dot` (the constant points do not move) compensates exactly. -/
theorem traceDiff_reduce_of_dvd_dotDer_of_natDegree_lt {B : A[X]} (hu : u.Monic) (hB : B.Monic)
    (hu' : u'.Monic) (hc : c * cw = 1) (hR : u * B * u' = C c * (v ^ 2 - f))
    (hf : ∀ i, d (f.coeff i) = 0) (hBd : ∀ i, d (B.coeff i) = 0)
    (hvB : B ∣ d.dotDer v)
    (hs : cu1 * u + s * (2 * v) = 1) (hs' : cu2 * u' + s' * (2 * v') = 1)
    (hv' : u' ∣ v' + v)
    (hdeg : (X ^ k * C c * d.dotDer v).natDegree + 1 < (u * B * u').natDegree) :
    traceDiff d u' s' k = traceDiff d u s k := by
  have hRm : (u * B * u').Monic := (hu.mul hB).mul hu'
  -- a cofactor modulo `u * u'` exists: `2v` is invertible modulo each factor
  have hcopA : IsCoprime u (2 * v) := ⟨cu1, s, hs⟩
  obtain ⟨cB, Bz, hBz⟩ := hcopA.mul_left (isCoprime_two_mul_of_dvd_add hs' hv')
  -- the block certificates agree with the common one, up to the sign on the reduced side
  have hsB : u ∣ s - Bz := dvd_sub_comm.mp (dvd_sub_of_bezout hs hBz (by simp))
  have hs'B : u' ∣ s' + Bz := by
    have h : u' ∣ -Bz - s' :=
      dvd_sub_of_bezout (u₁ := u') (u₂ := u) (v₁ := v') (v₃ := -v) (c₁ := cu2) (s₁ := s')
        (c₃ := cB) (s₃ := -Bz) hs' (by linear_combination hBz)
        (by rwa [dvd_sub_comm, sub_neg_eq_add])
    rwa [dvd_sub_comm, sub_neg_eq_add] at h
  -- transport both sides to the common modulus `u * B * u'`
  have e₁ : topCoeffMod u (X ^ k * d.dotDer u * s)
      = topCoeffMod (u * B * u') (X ^ k * d.dotDer u * Bz * (B * u')) := by
    conv_rhs => rw [mul_assoc u B u', topCoeffMod_mul_monic hu (hB.mul hu')]
    refine topCoeffMod_congr hu ?_
    obtain ⟨t, ht⟩ := hsB
    exact ⟨X ^ k * d.dotDer u * t, by linear_combination (X ^ k * d.dotDer u) * ht⟩
  have e₂ : topCoeffMod u' (X ^ k * d.dotDer u' * s')
      = topCoeffMod (u * B * u') (-(X ^ k * d.dotDer u' * Bz * (u * B))) := by
    rw [mul_comm (u * B) u', ← topCoeffMod_mul_monic hu' (hu.mul hB)]
    refine topCoeffMod_congr (hu'.mul (hu.mul hB)) ?_
    obtain ⟨t, ht⟩ := hs'B
    exact ⟨X ^ k * d.dotDer u' * t, by
      linear_combination (X ^ k * d.dotDer u' * (u * B)) * ht⟩
  -- the two terms are the Leibniz derivative of `(u·B)·u'`, which is `2v·v_dot` modulo it
  have hdotAB : d.dotDer (u * B) = d.dotDer u * B := by
    rw [d.dotDer_mul, d.dotDer_eq_zero_of_coeff hBd]
    ring
  have hdotR : d.dotDer (u * B * u') = C (d c) * (v ^ 2 - f) + C c * (2 * v * d.dotDer v) := by
    have hv2 : d.dotDer (v ^ 2 - f) = 2 * v * d.dotDer v := by
      rw [map_sub, d.dotDer_eq_zero_of_coeff hf, sub_zero, d.dotDer_sq]
    rw [hR, d.dotDer_mul, hv2, Derivation.dotDer_C]
  have hvf : v ^ 2 - f = C cw * (u * B * u') := by
    rw [hR, ← mul_assoc, ← C_mul, mul_comm cw c, hc, C_1, one_mul]
  have key : topCoeffMod (u * B * u')
      (X ^ k * d.dotDer u * Bz * (B * u') + X ^ k * d.dotDer u' * Bz * (u * B)) = 0 := by
    rw [topCoeffMod_congr hRm (q := X ^ k * C c * d.dotDer v) ?_]
    · exact topCoeffMod_eq_zero_of_natDegree_lt hRm hdeg
    obtain ⟨t, ht⟩ := hvB
    refine ⟨X ^ k * Bz * C (d c) * C cw - X ^ k * C c * t * cB, ?_⟩
    have hleib : d.dotDer (u * B) * u' + u * B * d.dotDer u' = d.dotDer (u * B * u') :=
      (d.dotDer_mul (u * B) u').symm
    linear_combination -(X ^ k * Bz * u') * hdotAB + (X ^ k * Bz) * hleib
      + (X ^ k * Bz) * hdotR + (X ^ k * Bz * C (d c)) * hvf
      + (X ^ k * C c * d.dotDer v) * hBz - (X ^ k * C c * (cB * (u * u'))) * ht
  have hadd := topCoeffMod_add (u := u * B * u') (X ^ k * d.dotDer u * Bz * (B * u'))
    (X ^ k * d.dotDer u' * Bz * (u * B))
  rw [traceDiff, traceDiff, e₁, e₂, topCoeffMod_neg]
  linear_combination key - hadd

/-- **(T2) The trace-form differential is unchanged by Cantor reduction**: the case of
`ChabautyColeman.traceDiff_reduce_of_dvd_dotDer_of_natDegree_lt` with no constant factor,
`B = 1`.

The degree hypothesis is *tight* rather than slack: with `deg v ≤ g` one has `deg(v²-f) =
2g+1`, and with `deg v ≥ g+1` — which is what the pipeline's own reduction steps produce — one
has `deg(v²-f) = 2·deg v`; in both cases it holds with equality at the extreme `k`, and fails
one step further. -/
theorem traceDiff_reduce_of_natDegree_lt (hu : u.Monic) (hu' : u'.Monic)
    (hc : c * cw = 1) (hR : u * u' = C c * (v ^ 2 - f))
    (hf : ∀ i, d (f.coeff i) = 0)
    (hs : cu1 * u + s * (2 * v) = 1) (hs' : cu2 * u' + s' * (2 * v') = 1)
    (hv' : u' ∣ v' + v)
    (hdeg : (X ^ k * C c * d.dotDer v).natDegree + 1 < (u * u').natDegree) :
    traceDiff d u' s' k = traceDiff d u s k :=
  traceDiff_reduce_of_dvd_dotDer_of_natDegree_lt d hu monic_one hu' hc (by rwa [mul_one]) hf
    (fun i ↦ by simp [coeff_one, apply_ite]) (one_dvd _) hs hs' hv' (by rwa [mul_one])

variable {α β : A} {cu : A[X]}

/-- **(T3) The moving pair block.** For the datum of a pair of points whose second point is
constant, the trace-form differential is `α^k·D(α)/(2·v(α))` — the pullback of the standard
regular differential `x^k dx/(2y)` at the moving point, the constant point contributing
nothing.  Stated in the division-free form. -/
theorem traceDiff_pair (hβ : d β = 0) (hαβ : IsUnit (α - β))
    (hs : cu * ((X - C α) * (X - C β)) + s * (2 * v) = 1) (k : ℕ) :
    2 * v.eval α * traceDiff d ((X - C α) * (X - C β)) s k = α ^ k * d α := by
  -- the coefficientwise derivative of the pair modulus
  have hdot : d.dotDer ((X - C α) * (X - C β)) = -(C (d α) * (X - C β)) := by
    rw [d.dotDer_mul]
    simp only [map_sub, Derivation.dotDer_X, Derivation.dotDer_C, hβ, map_zero, sub_zero,
      zero_sub]
    ring
  -- the certificate at the moving point inverts `2·v(α)`
  have hsα : s.eval α * (2 * v.eval α) = 1 := by simpa using congrArg (Polynomial.eval α) hs
  refine hαβ.mul_left_cancel ?_
  have hkey := sub_mul_topCoeffMod_pair α β (X ^ k * -(C (d α) * (X - C β)) * s)
  simp only [eval_mul, eval_pow, eval_X, eval_neg, eval_C, eval_sub, sub_self, mul_zero,
    zero_mul, neg_zero, sub_zero] at hkey
  rw [traceDiff, hdot]
  linear_combination -(2 * v.eval α) * hkey + (α ^ k * d α * (α - β)) * hsα

/-- **(T3′) The single moving point.** For the degree-one datum `(X - α, v)` of one moving
point, the trace-form differential is `α^k·D(α)/(2·v(α))` — the pullback of `x^k dx/(2y)` at
the point. The block of the infinity-centred configuration `[P - ∞] + τ`. -/
theorem traceDiff_single (hs : cu * (X - C α) + s * (2 * v) = 1) (k : ℕ) :
    2 * v.eval α * traceDiff d (X - C α) s k = α ^ k * d α := by
  have hdot : d.dotDer (X - C α) = -C (d α) := by
    rw [map_sub, Derivation.dotDer_X, Derivation.dotDer_C]
    ring
  have hsα : s.eval α * (2 * v.eval α) = 1 := by simpa using congrArg (Polynomial.eval α) hs
  have htop : topCoeffMod (X - C α) (X ^ k * -C (d α) * s)
      = (X ^ k * -C (d α) * s).eval α := by
    rw [topCoeffMod, modByMonic_X_sub_C_eq_C_eval, natDegree_X_sub_C, Nat.sub_self, coeff_C,
      ite_eq_left rfl]
  rw [traceDiff, hdot, htop]
  simp only [eval_mul, eval_pow, eval_X, eval_neg, eval_C]
  linear_combination (α ^ k * d α) * hsα

end Nontrivial

section Domain

variable [Nontrivial A] [NoZeroDivisors A] {u u' v v' f s s' cu1 cu2 : A[X]}
  {c cw : A} {g k : ℕ}

/-- **(T2′) with the degree side condition discharged**, on a curve `y² = f` of odd degree
`2g+1` and in the regular range `k < g`. -/
theorem traceDiff_reduce_of_dvd_dotDer {B : A[X]} (hu : u.Monic) (hB : B.Monic)
    (hu' : u'.Monic) (hc : c * cw = 1) (hR : u * B * u' = C c * (v ^ 2 - f))
    (hfc : ∀ i, d (f.coeff i) = 0) (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hBd : ∀ i, d (B.coeff i) = 0) (hvB : B ∣ d.dotDer v)
    (hs : cu1 * u + s * (2 * v) = 1) (hs' : cu2 * u' + s' * (2 * v') = 1)
    (hv' : u' ∣ v' + v) :
    traceDiff d u' s' k = traceDiff d u s k := by
  refine traceDiff_reduce_of_dvd_dotDer_of_natDegree_lt d hu hB hu' hc hR hfc hBd hvB hs hs'
    hv' ?_
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hle : (X ^ k * C c * d.dotDer v).natDegree ≤ k + v.natDegree := by
    refine natDegree_mul_le.trans ?_
    lia [(natDegree_mul_le.trans (by simp) : (X ^ k * C c : A[X]).natDegree ≤ k),
      d.natDegree_dotDer_le v]
  rw [hR, natDegree_C_mul hc0, natDegree_sq_sub_of_odd ⟨g, hf⟩, hf]
  lia

/-- **(T2) The trace-form differential is unchanged by Cantor reduction**, on a curve
`y² = f` of odd degree `2g+1` and in the range `k < g` where the differentials `x^k dx/(2y)`
are regular — the case `B = 1` of `ChabautyColeman.traceDiff_reduce_of_dvd_dotDer`. There the
degree side condition is automatic — and only just: it holds with equality at `k = g - 1`,
whether the datum has `deg v ≤ g` (then `deg(v² - f) = 2g+1`) or `deg v > g` (then
`deg(v² - f) = 2 deg v`), the two cases the pipeline actually produces. -/
theorem traceDiff_reduce (hu : u.Monic) (hu' : u'.Monic)
    (hc : c * cw = 1) (hR : u * u' = C c * (v ^ 2 - f)) (hfc : ∀ i, d (f.coeff i) = 0)
    (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hs : cu1 * u + s * (2 * v) = 1) (hs' : cu2 * u' + s' * (2 * v') = 1)
    (hv' : u' ∣ v' + v) :
    traceDiff d u' s' k = traceDiff d u s k :=
  traceDiff_reduce_of_dvd_dotDer d hu monic_one hu' hc (by rwa [mul_one]) hfc hf hk
    (fun i ↦ by simp [coeff_one, apply_ite]) (one_dvd _) hs hs' hv'

end Domain

end ChabautyColeman

end
