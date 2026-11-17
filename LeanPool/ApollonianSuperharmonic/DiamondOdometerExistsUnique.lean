/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4818T1Representatives
public import LeanPool.ApollonianSuperharmonic.P4818T1BoundaryRecovery
public import LeanPool.ApollonianSuperharmonic.P4818T1OverlapDifferences
public import LeanPool.ApollonianSuperharmonic.P4818T1AffineTransversalExtension

-- [TABLET NODE: DiamondOdometerExistsUnique]

/-!
# DiamondOdometerExistsUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondOdometerExistsUnique (K : DiamondParameter) :
    ∃! g : IntegerLatticeFunction,
      (∀ x, g (x + ⟨0, -(2 * K.1 : Int)⟩) = g x +
        (-(K.1 : Int)) * x.re + ((K.1 : Int) - 1) * x.im -
          (K.1 : Int) * ((K.1 : Int) - 2)) ∧
      (∀ x, g (x + ⟨(K.1 + 1 : Int), (K.1 : Int)⟩) = g x +
        (K.1 : Int) * x.re + x.im + (K.1 : Int) * (K.1 + 1) / 2) ∧
      (∀ x, g (x + ⟨-(K.1 : Int) - 1, (K.1 : Int)⟩) = g x -
        (K.1 : Int) * x.im - (K.1 : Int) * (K.1 + 1) / 2) ∧
      (∀ x, x ∈ DiamondVertexDomains K false ->
        g x = (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int) - 1) / 2 -
          (x.re - x.im) ^ 2 / 4) := by
-- BODY
  classical
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -2 * k⟩
  let b : GaussianInt := ⟨k + 1, k⟩
  let c : GaussianInt := ⟨-k - 1, k⟩
  let C : Int := k * (k + 1) / 2
  let α : GaussianInt →+ Int :=
    { toFun := fun x => -k * x.re + (k - 1) * x.im
      map_zero' := by simp
      map_add' := by intros; simp; ring }
  let β : GaussianInt →+ Int :=
    { toFun := fun x => k * x.re + x.im
      map_zero' := by simp
      map_add' := by intros; simp; ring }
  have hrep : ∀ x : GaussianInt, ∃! p : GaussianInt × (Int × Int),
      p.1 ∈ P4818T1HalfOpen K ∧ x = p.1 + p.2.1 • a + p.2.2 • b :=
    P4818T1Representatives K
  have hcomm : α b = β a := by
    simp [α, β, a, b]
    ring
  obtain ⟨g, hH, hga, hgb, _, huniq⟩ :=
    P4818T1AffineTransversalExtension (P4818T1HalfOpen K) a b
      α β (-k * (k - 2)) C P4207T1DiamondFormula hrep hcomm
  have ga (x) : g (x + a) = g x + (-k) * x.re +
      (k - 1) * x.im - k * (k - 2) := by
    have h := hga x
    change g (x + a) = g x + (-k * x.re + (k - 1) * x.im) +
      (-k * (k - 2)) at h
    linarith
  have gb (x) : g (x + b) = g x + k * x.re + x.im + C := by
    have h := hgb x
    change g (x + b) = g x + (k * x.re + x.im) + C at h
    linarith
  have gc (x) : g (x + c) = g x - k * x.im - C := by
    have h1 := ga (x + c)
    have h2 := gb (x + c + a)
    have he : x + c + a + b = x := by
      ext <;> simp [a, b, c] <;> ring
    rw [he] at h2
    simp only [Zsqrtd.re_add, Zsqrtd.im_add] at h1 h2
    dsimp [a, c] at h1 h2
    nlinarith
  obtain ⟨oA, oB, oC⟩ := P4818T1OverlapDifferences K
  have pa : ∀ x, x ∈ DiamondVertexDomains K false →
      x + a ∈ DiamondVertexDomains K false →
      (g x = P4207T1DiamondFormula x ↔
        g (x + a) = P4207T1DiamondFormula (x + a)) := by
    intro x hx hxa
    have hg := ga x
    have hf := oA x hx hxa
    constructor <;> intro h <;> linarith
  have pb : ∀ x, x ∈ DiamondVertexDomains K false →
      x + b ∈ DiamondVertexDomains K false →
      (g x = P4207T1DiamondFormula x ↔
        g (x + b) = P4207T1DiamondFormula (x + b)) := by
    intro x hx hxb
    have hg := gb x
    have hf := oB x hx hxb
    change _ = k * x.re + x.im + C at hf
    constructor <;> intro h <;> linarith
  have pc : ∀ x, x ∈ DiamondVertexDomains K false →
      x + c ∈ DiamondVertexDomains K false →
      (g x = P4207T1DiamondFormula x ↔
        g (x + c) = P4207T1DiamondFormula (x + c)) := by
    intro x hx hxc
    have hg := gc x
    have hf := oC x hx hxc
    change _ = -k * x.im - C at hf
    constructor <;> intro h <;> linarith
  have hclosed : ∀ x, x ∈ DiamondVertexDomains K false →
      g x = P4207T1DiamondFormula x :=
    P4818T1BoundaryRecovery K (fun x => g x = P4207T1DiamondFormula x)
      hH (by simpa only [a, k, neg_mul] using pa)
      (by simpa only [b, k] using pb) (by simpa only [c, k] using pc)
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    simpa only [a, k, neg_mul] using ga x
  · intro x
    exact gb x
  · intro x
    exact gc x
  · exact hclosed
  · intro g' hg'
    obtain ⟨ha', hb', _, hF'⟩ := hg'
    apply huniq g'
    · intro x
      change g' (x + a) = g' x + (-k * x.re + (k - 1) * x.im) +
        (-k * (k - 2))
      have h : g' (x + a) = g' x + (-k) * x.re +
          (k - 1) * x.im - k * (k - 2) := by
        simpa only [a, k, neg_mul] using ha' x
      linarith
    · intro x
      change g' (x + b) = g' x + (k * x.re + x.im) + C
      have h := hb' x
      change g' (x + b) = g' x + k * x.re + x.im + C at h
      linarith
    · intro h hh
      exact hF' h hh.1

end ApollonianSuperharmonic

end
