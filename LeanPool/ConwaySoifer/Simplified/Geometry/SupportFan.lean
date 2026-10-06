/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Support
import Mathlib.Tactic

/-! Geometric orientation fans. Every cone uses the same support triple at
both endpoints. All inputs are propositions about real points, not Boolean
checker results. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section
namespace ConwaySoifer.Simplified

/-- A lower support estimate witnessed by three contained points. -/
def SupportBound (Q : EquilateralTriangle) (e : Point) : Prop :=
  ∃ p₀ ∈ Q.carrier, ∃ p₁ ∈ Q.carrier, ∃ p₂ ∈ Q.carrier,
    len e ≤ supportNum e p₀ p₁ p₂

/-- Critically, one triple witnesses both ends of this cone. -/
def ConeBound (Q : EquilateralTriangle) (u v : Point) : Prop :=
  ∃ p₀ ∈ Q.carrier, ∃ p₁ ∈ Q.carrier, ∃ p₂ ∈ Q.carrier,
    len u ≤ supportNum u p₀ p₁ p₂ ∧ len v ≤ supportNum v p₀ p₁ p₂

theorem SupportBound.smul {Q : EquilateralTriangle} {e : Point} (h : SupportBound Q e)
    {a : ℝ} (ha : 0 ≤ a) : SupportBound Q (a • e) := by
  obtain ⟨p₀, h₀, p₁, h₁, p₂, h₂, h⟩ := h
  refine ⟨p₀, h₀, p₁, h₁, p₂, h₂, ?_⟩
  rw [len_smul_nonneg ha, supportNum_smul]
  exact mul_le_mul_of_nonneg_left h ha

theorem ConeBound.bound {Q : EquilateralTriangle} {u v l : Point}
    (h : ConeBound Q u v) (huv : 0 < cross u v)
    (hul : 0 ≤ cross u l) (hlv : 0 ≤ cross l v) : SupportBound Q l := by
  obtain ⟨p₀, h₀, p₁, h₁, p₂, h₂, hu, hv⟩ := h
  exact ⟨p₀, h₀, p₁, h₁, p₂, h₂, support_bound_on_cone hu hv huv hul hlv⟩

/-- A chain ending on the last boundary of a 120-degree orientation arc. -/
def SupportFan (Q : EquilateralTriangle) : Point → List Point → Prop
  | u, [] => u = rot eastDir ∧ SupportBound Q u
  | u, v :: vs => 0 < cross u v ∧ ConeBound Q u v ∧ SupportFan Q v vs

theorem SupportFan.bound {Q : EquilateralTriangle} {l : Point}
    (hl0 : l ≠ 0) (hl1 : 0 ≤ cross eastDir l) (hl2 : 0 ≤ cross l (rot eastDir))
    (vs : List Point) : ∀ u, SupportFan Q u vs → 0 ≤ cross u l → SupportBound Q l := by
  induction vs with
  | nil =>
    intro u h hu
    obtain ⟨rfl, hb⟩ := h
    have he : cross (rot eastDir) l = 0 := by
      have hanti := cross_anticomm (rot eastDir) l
      linarith
    obtain ⟨a, ha, rfl⟩ := pos_of_parallel_in_arc
      (u := rot eastDir) (by simp [rot, eastDir]) hl0
      (by norm_num [cross, rot, eastDir]) (by norm_num [cross, rot, eastDir]) hl1 hl2 he
    exact hb.smul ha.le
  | cons v vs ih =>
    intro u h hu
    obtain ⟨huv, hc, hrest⟩ := h
    rcases le_total (cross v l) 0 with hv | hv
    · exact hc.bound huv hu (by rw [cross_anticomm]; linarith)
    · exact ih v hrest hv

theorem one_le_side_of_fan {Q : EquilateralTriangle} (hq : 0 < Q.side)
    {vs : List Point} (hf : SupportFan Q eastDir vs) : 1 ≤ Q.side := by
  obtain ⟨O, h1, h2⟩ := Q.exists_orientation_in_arc hq
  have h0 : O.dir ≠ 0 := (normSq_pos_iff _).mp O.dir_pos
  obtain ⟨p₀, h₀, p₁, h₁, p₂, h₂, h⟩ := SupportFan.bound h0 h1 h2 vs eastDir hf h1
  exact O.one_le_side_of_bound h₀ h₁ h₂ h

/-- Polynomial inequalities imply a geometric support estimate without square roots. -/
theorem support_of_sq {u p₀ p₁ p₂ : Point} (hN : 0 ≤ supportNum u p₀ p₁ p₂)
    (hD : normSq u ≤ (supportNum u p₀ p₁ p₂) ^ 2) :
    len u ≤ supportNum u p₀ p₁ p₂ := by
  nlinarith [len_sq u, len_nonneg u]

end ConwaySoifer.Simplified
