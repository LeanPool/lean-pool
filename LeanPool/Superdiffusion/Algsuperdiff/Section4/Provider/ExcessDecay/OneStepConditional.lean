/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepGoodScales

/-!
# OneStepConditional

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `l.excess.decay.good.scales`, conditionally on the harmonic-approximation anchor

The one-step excess-decay contraction is assembled here from

* everything proved in `OneStepWindows` / `OneStepCompetitor` / `OneStepTriangle`
  / `OneStepAssembly` / `OneStepGoodScales`, and
* exactly **one** derived-result hypothesis, `hharm`, which is the conclusion of
  the harmonic-approximation anchor
  `Algsuperdiff.Frozen.Section4.harmonic_approximation_good_scales`, transcribed
  as a `Prop` at the instance this proof needs.

## The instance `hharm` is transcribed at

The general clause is instantiated at

```text
  d := d ,  M := M ,  s := s ,  L := L ,  m := m ,  n := n - 2 ,
  x := wellPlacedCentre x m (n-2) ,  z := z ,  u := u ,  h := h ,  g := g ,
  v := v ,  w := u - v
```

i.e. at the *window choice* `y := wellPlacedCentre x m (n-2)` proved admissible
in `OneStepWindows.image_add_wellPlacedCentre_subset_windowChoice`.  Every
index is therefore written here **exactly as the anchor prints it after that
substitution** — the good-event index is `n - 2 + 3`, not the arithmetically
equal `n + 1`, and the replacement window is `(y + ·) '' □_{n-2}`.

The right-hand side is carried as a single universally quantified `B : ℝ≥0∞`
with `B ≠ ⊤`, so that instantiating `B` at the anchor's own four-term
right-hand side turns `hharm` into that clause verbatim.

## The honest-vs-printed delta (leg by leg)

* **Good-event index.**  Print gates at `𝒢(n, z; s/8, (s/8)δ^{1/2})`; the
  anchor delivers at index `n - 2 + 3 = n + 1`.  Carried here at the anchor's
  index.  The two events are **incomparable** (no monotonicity of `goodEventAt`
  in the scale index exists, and none is structurally available: the `𝒢₀`/`𝒢₂`
  weights themselves depend on the index).
* **Good-event `ε` slot.**  Print gates at `ε = (s/8)δ^{1/2}`, the anchor at `ε
  = 1/2`.  Both appear here: `hmem` is at the printed `ε`, `hharm` at the
  anchor's, and `OneStepGoodScales.le_of_indicator_goodEventAt_le` bridges them
  (`goodEventAt_mono_ep`).  This is a *bridge*, not a deviation.
* **Replacement window.**  Print puts `‖u-v‖` on `U_2 = (x+□_{n-2}) ∩ □_m`; the
  anchor puts it on the full cube `y + □_{n-2} ⊇ U_2`.  Carried at the anchor's
  window, paid at the volume ratio `3^{d}`.
* **Contraction factor.**  The `3^{-k/2}` leg is at the printed window `E(u,
  (x+□_n) ∩ □_m)`; the `δ^{1/2}` leg is inside `B`, i.e. inside the unexpanded
  anchor.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The one-step excess-decay contraction, conditional on the harmonic
approximation anchor.**

```text
  E(u, U_k)  ≤  C_t Csch κ (3^{-k})^{1/2} E(u, U_0)
                 + (81 C_t Csch + 9·3^k √((3^k)^d)) · 3^{-n} · 3^d · ‖RHS‖
                 + C_t (3^{n-k})^{1/2} Kh
```

valid pathwise at every `ω` of the printed good event
`𝒢(n-2+3, z; s/8, (s/8)δ^{1/2})`. -/
theorem excessDecay_oneStep_of_harmonicApprox (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {M : ABKModel d} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {delta : ℝ}
    (hdelta1 : delta ≤ 1) {x z : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m) {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)))
    (huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)))
    {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
      (Support.cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
      (s / 8 * Real.sqrt delta))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hharm : Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d)
          (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
        (fun _omega' =>
          MeasureTheory.eLpNorm (fun y => u y - v y) 2
            (Support.normalizedVolumeMeasureOn
              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                openCubeSet (originCube d (n - 2)))))
        omega ≤ B)
    {Gv : Vec d → Vec d} {K Kh Csch : ℝ} (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hint : ∀ i, IntegrableOn (fun p => Gv p i) (truncatedWindow x m (n - 3)) volume)
    (hgrad : HasGradientOn (truncatedWindow x m (n - 3)) v Gv)
    (hhol : HolderSeminormBoundOn (truncatedWindow x m (n - 3)) (1 / 2 : ℝ) K Gv)
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)
        * affineExcess (truncatedWindow x m (n - 2)) v + Kh) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * Csch * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d Csch k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta := by positivity
  have heple : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  -- strip the anchor's indicator on the printed (smaller) event
  have hnorm := le_of_indicator_goodEventAt_le hep0 heple hmem hharm
  -- move to the real carrier
  have hD : normalizedL2On (movedReplacementCube x m n) (fun y => u y - v y) ≤ B.toReal :=
    normalizedL2On_le_toReal_of_eLpNorm_le (volume_movedReplacementCube_pos x m n)
      (volume_movedReplacementCube_ne_top x m n) huv hB hnorm
  exact excessDecay_oneStep_of_movedCubeBound hd hk hx hnm hu hv huv hK hCsch hint hgrad
    hhol hschauder hD

end

end Algsuperdiff.Section4.Provider.ExcessDecay
