/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# Nonlocal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The far-field leg of `l.localize.lambdas.for.regularity`

ABK26, §4.1.  This module renders the proof abbreviation `𝒳_k(z)` and the
display `e.localize.lambdas.for.regularity.nonlocal`

```
max_{z ∈ 3^{n−2}ℤ^d ∩ (□_m ∖ □_n)} 𝒳_{n−2}(z) · 𝟙_{𝒢₀(m)} ≤ 3^{γ(m−n)/4}
```

over the proved Section 4 support carriers (`Section4/Support/Events.lean`).
The display is, as the source says, *nothing but* the defining inequality of
`𝒢₀(m)` read at the single index `k = n` and rearranged, and that is exactly
what the proofs below do: a `le_iSup` at `k = n`, a `le_iSup` at the lattice
point, and one division by the positive weight `3^{−γ(m−n)/4}`.

## The index conversion (versus)

`𝒢₀`'s own bracket is `σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; a_{k−2})`, while the
proof's abbreviation is `𝒳_k(z) = (σ_{k−1} λ_{γ,2}^{-1}(z+□_k; a_k) −
C_cg)_+`.  It is discharged here, once, by `cgExcess_sub_two` — an equality of
the two readings at the *same* proved observable `Support.lambdaAnnulusAtom`.

## Range of `n`

The source states the display for the `n` of the enclosing supremum, i.e. for
every `n ≤ m`, while `𝒢₀`'s own supremum ranges over `k ≤ m−1`.  Both cases are
covered below: at `n ≤ m−1` the bound is the rearranged `𝒢₀` inequality, and at
`n = m` the index set `3^{m−2}ℤ^d ∩ (□_m ∖ □_m)` is empty, so the left side is
`0`.  No hypothesis beyond `n ≤ m` is used.

## References

* ABK26, `l.localize.lambdas.for.regularity`; the abbreviation `𝒳_k`; the
  display.
* `d.good.event.for.lambda`, (`𝒢₀`).
-/

namespace Algsuperdiff.Section4.Provider.Localize

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The proof's abbreviation `𝒳_k(z)` -/

/-- **The coarse-grained ellipticity excess `𝒳_k(z)`**:

```
𝒳_k(z) := ( σ_{k−1} λ_{γ,2}^{-1}(z+□_k; a_k) − C_{(e.cg.ellip.lower)} )_+ .
```

The cube translate is realized, as everywhere in Section 4, by translating the
*sample* rather than the cube, and `(·)_+` is `max · 0`. -/
def cgExcess (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  max ((Annealed.sigmaBar M (k - 1) : ℝ) *
      Observable.cutoffLowerEllipticityInvLiteral M k k M.gamma
        Support.coarseEllipticityExponentTwo
        (Cutoff.translateCutoffSample z omega) - Ccg) 0

theorem cgExcess_nonneg (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ cgExcess M Ccg k z omega :=
  le_max_right _ _

/-- **The index conversion `𝒳_{k−2}(z) = ` the `𝒢₀` bracket at `k`.**  The
manuscript's two readings of the same quantity (versus) are equal at the proved
observable; the source never writes this out. -/
theorem cgExcess_sub_two (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) :
    cgExcess M Ccg (k - 2) z omega =
      max ((Annealed.sigmaBar M (k - 3) : ℝ) *
        Support.lambdaAnnulusAtom M k z omega - Ccg) 0 := by
  have h : k - 2 - 1 = k - 3 := by ring
  simp only [cgExcess, Support.lambdaAnnulusAtom, h]

/-! ## 2. The weight of `𝒢₀` and its reciprocal -/

/-- The shell weight `3^{−γ(m−n)/4}` carried by `𝒢₀`'s supremum. -/
private theorem rpow_weight_inv (M : ABKModel d) (m n : ℤ) :
    (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)))⁻¹ =
      Real.rpow (3 : ℝ) ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) := by
  show ((3 : ℝ) ^ (-(1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)))⁻¹ =
    (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))
  rw [show -(1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ) =
        -((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) from by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), inv_inv]

private theorem rpow_weight_pos (M : ABKModel d) (m n : ℤ) :
    (0 : ℝ) < Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-! ## 3. The rearranged `𝒢₀` inequality -/

/-- The `k`-term of `𝒢₀`'s supremum is at most `1`, for every admissible `k`.
This is the single `le_iSup` the source's `Observe that` performs. -/
private theorem eventG0_term_le_one (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG0 M Ccg m)
    (k : {k : ℤ // k ≤ m - 1}) :
    ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
        ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
          ENNReal.ofReal
            ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                Support.lambdaAnnulusAtom M k.1
                  (Support.triadicLatticePoint (k.1 - 2) v.1) omega - Ccg) ≤ 1 :=
  le_trans (le_iSup (fun k : {k : ℤ // k ≤ m - 1} =>
    ENNReal.ofReal
        (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
      ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
        ENNReal.ofReal
          ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
              Support.lambdaAnnulusAtom M k.1
                (Support.triadicLatticePoint (k.1 - 2) v.1) omega - Ccg)) k) homega

/-- **`e.localize.lambdas.for.regularity.nonlocal`, per lattice point.**

On `𝒢₀(m)`, every centre `z = 3^{n−2}v` of the annulus `□_m ∖ □_n` satisfies
`𝒳_{n−2}(z) ≤ 3^{γ(m−n)/4}`.  No constant: the right side is the bare power. -/
theorem cgExcess_le_of_mem_eventG0 (M : ABKModel d) (Ccg : ℝ) {m n : ℤ}
    (hn : n ≤ m - 1) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG0 M Ccg m)
    (v : ↥(Support.latticeAnnulusSet d (n - 2) m n)) :
    cgExcess M Ccg (n - 2) (Support.triadicLatticePoint (n - 2) v.1) omega ≤
      Real.rpow (3 : ℝ) ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) := by
  set w : ℝ := Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))
    with hw
  have hwpos : 0 < w := rpow_weight_pos M m n
  set X : ℝ :=
    (Annealed.sigmaBar M (n - 3) : ℝ) *
        Support.lambdaAnnulusAtom M n
          (Support.triadicLatticePoint (n - 2) v.1) omega - Ccg with hX
  -- the two `le_iSup` steps
  have hterm := eventG0_term_le_one M Ccg m homega ⟨n, hn⟩
  have hpoint : ENNReal.ofReal w * ENNReal.ofReal X ≤ 1 := by
    refine le_trans (mul_le_mul_right ?_ _) hterm
    exact le_iSup (fun v : ↥(Support.latticeAnnulusSet d (n - 2) m n) =>
      ENNReal.ofReal
        ((Annealed.sigmaBar M (n - 3) : ℝ) *
            Support.lambdaAnnulusAtom M n
              (Support.triadicLatticePoint (n - 2) v.1) omega - Ccg)) v
  -- back to the reals
  have hreal : w * X ≤ 1 := by
    rw [← ENNReal.ofReal_mul hwpos.le] at hpoint
    exact ENNReal.ofReal_le_one.mp hpoint
  have hXle : X ≤ w⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hwpos.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hwpos), one_mul, mul_one] at h
  rw [cgExcess_sub_two, ← hX, ← rpow_weight_inv M m n, ← hw]
  exact max_le hXle (inv_nonneg.mpr hwpos.le)

/-! ## 4. The display, at the lattice supremum and with the indicator -/

end

end Algsuperdiff.Section4.Provider.Localize
