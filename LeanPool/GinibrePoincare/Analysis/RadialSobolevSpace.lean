/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSobolevSpace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.FullRadialLSIReduction

/-! # The closed radial Sobolev gradient and its sharp LSI

The domain consists of the values in the smooth radial value-gradient graph
closure. Closability makes the gradient uniquely determined by the value.
This construction does not identify the domain with an independently defined
distributional weak-H¹ space; the reverse core-density theorem remains separate.
-/


@[expose] public section


open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Values in the genuine radial symmetric Sobolev graph completion. -/
def radialSobolevDomain (n : ℕ) : Set (Lp ℝ 2 (ginibreMeasure n)) :=
  {u | ∃ g, (u, g) ∈ radialSobolevClosure n}

/-- The closed radial gradient, extended by zero outside its domain.
For positive particle number, uniqueness is proved by test-function separation. -/
def radialSobolevGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := by
  classical
  exact if hu : u ∈ radialSobolevDomain n then hu.choose else 0

theorem radialSobolevGradient_mem_graph (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (hu : u ∈ radialSobolevDomain n) :
    (u, radialSobolevGradient n u) ∈ radialSobolevClosure n := by
  simpa only [radialSobolevGradient, dite_eq_left hu] using hu.choose_spec

theorem radialSobolevGradient_eq_of_mem_graph (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : (u, g) ∈ radialSobolevClosure n) : radialSobolevGradient n u = g :=
  radialSobolevClosure_gradient_unique n hn u _ g
    (radialSobolevGradient_mem_graph n u ⟨g, hg⟩) hg

/-- The actual graph closure equals the graph of the uniquely determined gradient. -/
theorem radialSobolevClosure_eq_gradient_graph (n : ℕ) (hn : 0 < n) :
    radialSobolevClosure n =
      {p | p.1 ∈ radialSobolevDomain n ∧ radialSobolevGradient n p.1 = p.2} := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p.2, hp⟩, radialSobolevGradient_eq_of_mem_graph n hn p.1 p.2 hp⟩
  · rintro ⟨hu, hg⟩
    have h := radialSobolevGradient_mem_graph n p.1 hu
    rwa [hg, Prod.mk.eta] at h

theorem radialSobolevGradient_closed (n : ℕ) (hn : 0 < n) :
    IsClosed {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      p.1 ∈ radialSobolevDomain n ∧ radialSobolevGradient n p.1 = p.2} := by
  rw [← radialSobolevClosure_eq_gradient_graph n hn]
  exact isClosed_closure

theorem radialSobolevGradient_weak (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n) :
    IsGinibreWeakGradient n u (radialSobolevGradient n u) :=
  radialSobolevClosure_weak_gradient n hn (u, radialSobolevGradient n u)
    (radialSobolevGradient_mem_graph n u hu)

/-- Sharp LSI on the radial Sobolev domain, with the function's unique closed
gradient and no auxiliary gradient witness or logarithmic-integrability assumption. -/
theorem radialSobolevDomain_lsi (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) u ≤
        (1 / (n : ℝ)) * ‖radialSobolevGradient n u‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, radialSobolevGradient n u)
    (radialSobolevGradient_mem_graph n u hu)

/-- Any weak-gradient representative of a value in the completed domain yields
the same sharp LSI, by the independently proved weak-gradient uniqueness. -/
theorem radialSobolevDomain_lsi_with_weak_gradient (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreWeakGradient n u g) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 := by
  have he := ginibre_weak_gradient_unique n hn u (radialSobolevGradient n u) g
    (radialSobolevGradient_weak n hn u hu) hg
  simpa only [he] using radialSobolevDomain_lsi n hn u hu

/-- The closed radial gradient is the ordinary distributional gradient on the
collision-free open set, with genuine local Lebesgue integrability. -/
theorem radialSobolevGradient_distributional (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n) :
    IsGinibreDistributionalGradient n u (radialSobolevGradient n u) :=
  ginibre_weak_gradient_distributional n hn u (radialSobolevGradient n u)
    (radialSobolevGradient_weak n hn u hu)

/-- The radial completion embeds in the independently defined weak-H¹ domain. -/
theorem radialSobolevDomain_subset_distributional (n : ℕ) (hn : 0 < n) :
    radialSobolevDomain n ⊆ ginibreDistributionalSobolevDomain n := by
  intro u hu
  exact ⟨radialSobolevGradient n u, radialSobolevGradient_distributional n hn u hu⟩

/-- The completed radial gradient agrees with the maximal ordinary weak gradient. -/
theorem radialSobolevGradient_eq_distributionalSobolevGradient (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n) :
    radialSobolevGradient n u = ginibreDistributionalSobolevGradient n u :=
  (ginibreDistributionalSobolevGradient_eq n hn u _
    (radialSobolevGradient_distributional n hn u hu)).symm

/-- The sharp radial LSI uses any ordinary distributional gradient of a value
in the completed domain; uniqueness identifies it with the closed gradient. -/
theorem radialSobolevDomain_lsi_with_distributional_gradient (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ radialSobolevDomain n)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 := by
  have he := ginibre_distributional_gradient_unique n hn u (radialSobolevGradient n u) g
    (radialSobolevGradient_distributional n hn u hu) hg
  simpa only [he] using radialSobolevDomain_lsi n hn u hu

end
end GinibrePoincare
