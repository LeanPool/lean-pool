/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module
public import Mathlib.Tactic
public import LeanPool.SalemTheorem.PdtPisotLadder
public import LeanPool.SalemTheorem.PdtSalemCircle
public import LeanPool.SalemTheorem.PdtSalemArith
public import LeanPool.SalemTheorem.PdtSalemMinus
public import LeanPool.SalemTheorem.PdtSalemEndgame
public import LeanPool.SalemTheorem.PdtSalemQuadUnit

/-!
# SalemPisot — Salem's theorem for Pisot numbers, and the two
constructions with their family roots exposed

The bridge from a Pisot number to the Pisot-pattern data of its minimal
polynomial; Salem's theorem stated for Pisot numbers (every Pisot number
is a limit of Salem numbers from both sides); and the two constructions
of the proof modules with the index `m` and the family
polynomial kept in the conclusion.

A Pisot number is a real algebraic integer `α > 1` all of whose other
complex conjugates lie strictly inside the unit circle; it is spelled
here as `1 < α`, `IsIntegral ℤ α`, and
`∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ α → ‖z‖ < 1`.

* `pattern_of_simple_root`: a monic integer polynomial with a simple
  complex root `α` (root multiplicity exactly one) whose other complex
  roots lie strictly inside the unit circle carries the Pisot-pattern
  data — the multiset `inside` of its other roots is interior and
  conjugation-closed, and the complex image factors as
  `(X − α)·∏ (X − z)`, the product over `inside`.  The conjugation
  closure comes from the integer coefficients (`Splits.roots_map`
  against the cast triangle), the factorization from
  `Splits.eq_prod_roots_of_monic` and `Multiset.cons_erase`.
* `pattern_of_pisot`: the minimal polynomial over `ℤ` of a Pisot number
  carries the pattern data.  Ingredients: the Gauss step
  `minpoly ℚ α = (minpoly ℤ α).map ℚ` (`ℤ` is integrally closed), the
  separability of the irreducible `minpoly ℚ α` in characteristic zero
  (so `α` is a simple root of its complex image), and the identification
  of the complex roots with `(minpoly ℚ α).aroots ℂ`.
* `salem_theorem`: **Salem's theorem** for Pisot numbers — for every
  `ε > 0` there is a Salem number in `(α − ε, α)` and one in
  `(α, α + ε)` — by transport through `salem_theorem_full`.
* `salem_construction_two_sided`: the assembly
  `PdtSalemEndgame.salem_construction_two_sided`, keeping the index and the
  root equation — under the Pisot pattern and `P(1/α) ≠ 0`, with
  `e = ±1` the sign of `P(1/α)`, some `X^m·P + e·P.reverse` (`m ≥ 2`)
  has a Salem root in `(α − ε, α)` and some `X^m·P − e·P.reverse`
  (`m ≥ 2`) one in `(α, α + ε)`; the halves `exists_salem_below_root`
  and `exists_salem_above_root` are the ladder lemmas of
  `PdtSalemEndgame` with the root kept.
* `salem_quadratic_unit`: `PdtSalemQuadUnit.salem_two_sided_quad_unit`
  with the index and the root equation retained, the family spelled
  as `(X² − rX + 1)(X^{2m} + 1) ± X^{m+1}` (`m ≥ 1`).
-/

public section

namespace PDT
namespace SalemPisot

noncomputable section
open Polynomial

/-! ### The pattern data from a simple dominant root -/

/-- **The Pisot-pattern data from a simple root.**  For a monic integer
polynomial whose complex image has `α` as a root of multiplicity exactly
one and every other complex root strictly inside the unit circle, the
multiset `inside = roots.erase α` satisfies the three pattern
hypotheses: strict interiority, conjugation closure, and the
factorization `Pz = SalemCircle.P α inside`. -/
theorem pattern_of_simple_root (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (hsimple : Polynomial.rootMultiplicity ((alpha : ℂ)) (Pz.map (Int.castRingHom ℂ)) = 1)
    (hsmall : ∀ z : ℂ, (Pz.map (Int.castRingHom ℂ)).eval z = 0 → z ≠ ((alpha : ℂ)) → ‖z‖ < 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside := by
  classical
  set pC : Polynomial ℂ := Pz.map (Int.castRingHom ℂ) with hpC
  have hCmonic : pC.Monic := hmonic.map _
  have hCne : pC ≠ 0 := hCmonic.ne_zero
  have hsplits : pC.Splits := IsAlgClosed.splits pC
  have hroot : pC.eval ((alpha : ℂ)) = 0 := by
    have h1 : 0 < Polynomial.rootMultiplicity ((alpha : ℂ)) pC := by
      rw [hsimple]; exact one_pos
    exact (Polynomial.rootMultiplicity_pos hCne).mp h1
  have hmem : ((alpha : ℂ)) ∈ pC.roots := Polynomial.mem_roots'.mpr ⟨hCne, hroot⟩
  have hcount : pC.roots.count ((alpha : ℂ)) = 1 := by
    rw [Polynomial.count_roots]; exact hsimple
  have hnotin : ((alpha : ℂ)) ∉ pC.roots.erase ((alpha : ℂ)) := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, hcount]
  refine ⟨pC.roots.erase ((alpha : ℂ)), ?_, ?_, ?_⟩
  · -- strict interiority
    intro z hz
    have hzmem : z ∈ pC.roots := Multiset.mem_of_mem_erase hz
    have hzroot : pC.eval z = 0 := (Polynomial.mem_roots'.mp hzmem).2
    have hzne : z ≠ ((alpha : ℂ)) := fun h => hnotin (h ▸ hz)
    exact hsmall z hzroot hzne
  · -- conjugation closure
    have hmapconj : pC.map (starRingEnd ℂ) = pC := by
      rw [hpC, Polynomial.map_map,
        show (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from
          RingHom.ext_int _ _]
    have hroots_conj : pC.roots.map (starRingEnd ℂ) = pC.roots := by
      have h1 := hsplits.roots_map (starRingEnd ℂ)
      rw [hmapconj] at h1
      exact h1.symm
    rw [Multiset.map_erase _ (starRingEnd ℂ).injective, hroots_conj,
      Complex.conj_ofReal]
  · -- the factorization
    have hfac : pC = (pC.roots.map fun a => X - Polynomial.C a).prod :=
      hsplits.eq_prod_roots_of_monic hCmonic
    have hcons : ((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ)) = pC.roots :=
      Multiset.cons_erase hmem
    calc pC = (pC.roots.map fun a => X - Polynomial.C a).prod := hfac
      _ = ((((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ))).map
            fun a => X - Polynomial.C a).prod := by rw [hcons]
      _ = (X - Polynomial.C ((alpha : ℂ)))
          * ((pC.roots.erase ((alpha : ℂ))).map fun a => X - Polynomial.C a).prod := by
          rw [Multiset.map_cons, Multiset.prod_cons]
      _ = SalemCircle.P alpha (pC.roots.erase ((alpha : ℂ))) := rfl

/-! ### The pattern data of a Pisot number's minimal polynomial -/

/-- **The minimal polynomial of a Pisot number carries the pattern.**
For a real algebraic integer `α` every other complex root of whose
minimal polynomial over `ℚ` lies strictly inside the unit circle,
`minpoly ℤ α` (monic) has the Pisot-pattern data: its complex image is
`(X − α)·∏ (X − z)` over an interior, conjugation-closed multiset.  The
Gauss step identifies `minpoly ℚ α` with the rational image of
`minpoly ℤ α`; irreducibility gives separability in characteristic
zero, so `α` is a simple root of the complex image. -/
theorem pattern_of_pisot (alpha : ℝ) (hint : IsIntegral ℤ alpha)
    (hsmall : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      (minpoly ℤ alpha).map (Int.castRingHom ℂ) = SalemCircle.P alpha inside := by
  classical
  have hQint : IsIntegral ℚ alpha := hint.tower_top
  -- the Gauss step: `ℤ` is integrally closed
  have hmz : minpoly ℚ alpha = (minpoly ℤ alpha).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  -- the complex image of `minpoly ℤ α` is the complex image of `minpoly ℚ α`
  have hmapC : (minpoly ℤ alpha).map (Int.castRingHom ℂ)
      = (minpoly ℚ alpha).map (algebraMap ℚ ℂ) := by
    rw [hmz, Polynomial.map_map,
      show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from
        RingHom.ext_int _ _]
  have hmonicC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Monic :=
    (minpoly.monic hQint).map _
  have hCne : (minpoly ℚ alpha).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  -- separability in characteristic zero: the complex roots are distinct
  have hsepC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Separable :=
    (minpoly.irreducible hQint).separable.map
  have hnodup : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  -- `α` is a root of the complex image
  have hroot : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).eval ((alpha : ℂ)) = 0 := by
    rw [← SalemArith.aeval_eq_eval_map, SalemArith.aeval_ofReal, minpoly.aeval,
      Complex.ofReal_zero]
  have hmem : ((alpha : ℂ)) ∈ ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots :=
    Polynomial.mem_roots'.mpr ⟨hCne, hroot⟩
  have hsimple : Polynomial.rootMultiplicity ((alpha : ℂ))
      ((minpoly ℤ alpha).map (Int.castRingHom ℂ)) = 1 := by
    rw [hmapC, ← Polynomial.count_roots]
    exact Multiset.count_eq_one_of_mem hnodup hmem
  -- every other complex root is an element of `aroots`, hence interior
  have hsmall' : ∀ z : ℂ, ((minpoly ℤ alpha).map (Int.castRingHom ℂ)).eval z = 0 →
      z ≠ ((alpha : ℂ)) → ‖z‖ < 1 := by
    intro z hz hzne
    rw [hmapC] at hz
    have hzmem : z ∈ (minpoly ℚ alpha).aroots ℂ := by
      rw [Polynomial.aroots_def]
      exact Polynomial.mem_roots'.mpr ⟨hCne, hz⟩
    exact hsmall z hzmem hzne
  exact pattern_of_simple_root (minpoly ℤ alpha) (minpoly.monic hint) alpha hsimple hsmall'

/-! ### Salem's theorem for Pisot numbers -/

/-- **Salem's theorem.**  Every Pisot number `α` — a real algebraic
integer `α > 1` whose other complex conjugates lie strictly inside the
unit circle — is a limit of Salem numbers from both sides: for every
`ε > 0` there is a Salem number in `(α − ε, α)` and one in
`(α, α + ε)`.  Transported through `salem_theorem_full` along the
pattern data of `minpoly ℤ α`. -/
theorem salem_theorem (alpha : ℝ) (halpha : 1 < alpha) (hint : IsIntegral ℤ alpha)
    (hsmall : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps) := by
  obtain ⟨inside, hin, hconj, hfacC⟩ := pattern_of_pisot alpha hint hsmall
  exact SalemQuadUnit.salem_theorem_full (minpoly ℤ alpha) (minpoly.monic hint)
    alpha halpha inside hin hconj hfacC eps heps

/-! ### The constructions with their family roots exposed

The lower-level modules retain the family witnesses. Their traditional two-sided
statements discard those witnesses, and this module re-exports the stronger interfaces. -/

export SalemEndgame (exists_salem_below_root)

export SalemEndgame (exists_salem_above_root)

export SalemEndgame (eval_signed_family eval_signed_family_sub salem_construction_two_sided)

export SalemQuadUnit (salem_quadratic_unit)

end

end SalemPisot
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
