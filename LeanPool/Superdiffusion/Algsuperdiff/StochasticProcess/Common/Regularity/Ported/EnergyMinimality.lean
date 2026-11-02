/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier

/-!
# EnergyMinimality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dirichlet energy minimality of the weakly harmonic replacement

The corrector `v₁` of the boundary datum split is the weakly harmonic function on
the window `W` carrying the trace of the datum deviation `Φ = h − ℓ_h`.  Pricing
it in `L²` (`OneStepL2`) needs its Dirichlet energy, and the only handle on that
is the defining orthogonality of `IsUnitWeaklyHarmonicOn` — `∫_W ∇v₁ · ∇φ = 0`
for every `φ ∈ H¹₀(W)` — read at the admissible test function `φ = v₁ − Φ`.

The whole content is one expansion:

```text
  0 ≤ ∫_W |∇v₁ − ∇Φ|²
    = ∫_W |∇v₁|² − 2 ∫_W ∇v₁·∇Φ + ∫_W |∇Φ|²
    = ∫_W |∇v₁|² − 2 ∫_W |∇v₁|²  + ∫_W |∇Φ|²        (orthogonality)
    = ∫_W |∇Φ|² − ∫_W |∇v₁|² ,
```

the middle step because `∫_W ∇v₁·∇Φ = ∫_W ∇v₁·∇v₁ − ∫_W ∇v₁·∇(v₁ − Φ)` and the
second summand vanishes.  No positivity of a quadratic form, no Cauchy–Schwarz:
the test function `v₁ − Φ` is *exactly* the one that makes the discriminant
argument collapse to the single evaluation `t = 1`.

The hypothesis is stated against the `H¹₀` **witness** `rho` rather than against
`MemH10 W (v₁ − Φ)`, because `MemH10` pins only the value representative and the
energy is a statement about gradients;
`Corrector.exists_unitWeaklyHarmonicOn_of_datum` builds its corrector as
`Φ + rho.toH1Function`, so the gradient identity below is available at its
construction site by `H1Function.add_grad`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory
open HCPolySupport (Vec H1Function H10Function MemVectorL2 vecDot)


noncomputable section

variable {d : ℕ}

/-! ### Pointwise algebra of `vecDot` -/

theorem vecDot_self_nonneg (p : Vec d) : 0 ≤ vecDot p p := by
  classical
  change (0 : ℝ) ≤ ∑ i : Fin d, p i * p i
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)

theorem vecDot_sub_right (a b c : Vec d) :
    vecDot a (b - c) = vecDot a b - vecDot a c := by
  classical
  change (∑ i : Fin d, a i * (b i - c i))
    = (∑ i : Fin d, a i * b i) - ∑ i : Fin d, a i * c i
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_sub_self_expand (a b : Vec d) :
    vecDot (a - b) (a - b) = vecDot a a - 2 * vecDot a b + vecDot b b := by
  classical
  change (∑ i : Fin d, (a i - b i) * (a i - b i))
    = (∑ i : Fin d, a i * a i) - 2 * (∑ i : Fin d, a i * b i) + ∑ i : Fin d, b i * b i
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The three integrability slots -/

private theorem integrableOn_vecDot {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    IntegrableOn (fun y => vecDot (F y) (G y)) W volume :=
  HCPolySupport.integrableOn_vecDot_of_memVectorL2 hF hG

/-! ### Energy minimality -/

/-- **The weakly harmonic replacement minimizes the Dirichlet energy in its own
`H¹₀` class.**

If `w` is weakly harmonic on `W` and `w - Phi` is realized by the `H¹₀(W)`
witness `rho` — that is, `∇w = ∇Phi + ∇rho` pointwise — then

```text
  ∫_W |∇w|² ≤ ∫_W |∇Phi|² .
```
-/
theorem integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn {W : Set (Vec d)}
    {w Phi : H1Function W} (hw : IsUnitWeaklyHarmonicOn W w) (rho : H10Function W)
    (hgrad : ∀ y, w.grad y = Phi.grad y + rho.toH1Function.grad y) :
    ∫ y in W, vecDot (w.grad y) (w.grad y) ∂volume
      ≤ ∫ y in W, vecDot (Phi.grad y) (Phi.grad y) ∂volume := by
  have hwL2 : MemVectorL2 W w.grad := w.grad_memVectorL2
  have hPL2 : MemVectorL2 W Phi.grad := Phi.grad_memVectorL2
  have hI1 : Integrable (fun y => vecDot (w.grad y) (w.grad y)) (volume.restrict W) :=
    integrableOn_vecDot hwL2 hwL2
  have hI2 : Integrable (fun y => vecDot (w.grad y) (Phi.grad y)) (volume.restrict W) :=
    integrableOn_vecDot hwL2 hPL2
  have hI3 : Integrable (fun y => vecDot (Phi.grad y) (Phi.grad y)) (volume.restrict W) :=
    integrableOn_vecDot hPL2 hPL2
  -- the pointwise identity `∇rho = ∇w - ∇Phi`
  have hr : ∀ y, rho.toH1Function.grad y = w.grad y - Phi.grad y := by
    intro y
    rw [hgrad y]
    abel
  -- orthogonality at the admissible test function `rho`
  have hz : ∫ y in W, vecDot (w.grad y) (rho.toH1Function.grad y) ∂volume = 0 := hw rho
  have hsplit : ∫ y in W, vecDot (w.grad y) (rho.toH1Function.grad y) ∂volume
      = (∫ y in W, vecDot (w.grad y) (w.grad y) ∂volume)
        - ∫ y in W, vecDot (w.grad y) (Phi.grad y) ∂volume := by
    have hfun : (fun y => vecDot (w.grad y) (rho.toH1Function.grad y))
        = fun y => vecDot (w.grad y) (w.grad y) - vecDot (w.grad y) (Phi.grad y) := by
      funext y
      rw [hr y, vecDot_sub_right]
    rw [hfun, integral_sub hI1 hI2]
  have hcross : ∫ y in W, vecDot (w.grad y) (Phi.grad y) ∂volume
      = ∫ y in W, vecDot (w.grad y) (w.grad y) ∂volume := by
    rw [hz] at hsplit
    linarith only [hsplit]
  -- the nonnegative square of the difference
  have hnn : (0 : ℝ) ≤ ∫ y in W, vecDot (rho.toH1Function.grad y)
      (rho.toH1Function.grad y) ∂volume :=
    integral_nonneg fun y => vecDot_self_nonneg _
  have hexp : ∫ y in W, vecDot (rho.toH1Function.grad y) (rho.toH1Function.grad y) ∂volume
      = (∫ y in W, vecDot (w.grad y) (w.grad y) ∂volume)
        - 2 * ∫ y in W, vecDot (w.grad y) (Phi.grad y) ∂volume
        + ∫ y in W, vecDot (Phi.grad y) (Phi.grad y) ∂volume := by
    have hfun : (fun y => vecDot (rho.toH1Function.grad y) (rho.toH1Function.grad y))
        = fun y => (vecDot (w.grad y) (w.grad y)
            - 2 * vecDot (w.grad y) (Phi.grad y)) + vecDot (Phi.grad y) (Phi.grad y) := by
      funext y
      rw [hr y, vecDot_sub_self_expand]
    have hI2' : Integrable (fun y => 2 * vecDot (w.grad y) (Phi.grad y))
        (volume.restrict W) := hI2.const_mul 2
    have hI12 : Integrable (fun y => vecDot (w.grad y) (w.grad y)
        - 2 * vecDot (w.grad y) (Phi.grad y)) (volume.restrict W) := hI1.sub hI2'
    rw [hfun, integral_add hI12 hI3, integral_sub hI1 hI2', integral_const_mul]
  linarith only [hnn, hexp, hcross]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
