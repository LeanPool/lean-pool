/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Init

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The algebraic consequence of the four witness properties in v36.
This file alone makes no assertion about arithmetic or program indices.
-/

@[expose] public section

namespace FailureOfComposition

universe u

theorem no_quotient_composition_of_noncongruence {A : Type u} (s : Setoid A) (comp : A → A → A)
    (f i g : A) (hfi : s.r f i) (hcomp : ¬s.r (comp f g) (comp i g)) :
    ¬∃ C : Quotient s → Quotient s → Quotient s,
        ∀ a b, C (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (comp a b) :=
  by
  rintro ⟨C, hC⟩
  apply hcomp
  apply Quotient.exact
  calc
    Quotient.mk s (comp f g) = C (Quotient.mk s f) (Quotient.mk s g) := (hC f g).symm
    _ = C (Quotient.mk s i) (Quotient.mk s g) := by rw [Quotient.sound hfi]
    _ = Quotient.mk s (comp i g) := hC i g

theorem no_quotient_composition {A : Type u} (s : Setoid A) (comp : A → A → A) (f i g z : A)
    (hfi : s.r f i) (hfg : s.r (comp f g) z) (hig : s.r (comp i g) g) (hgz : ¬s.r g z) :
    ¬∃ C : Quotient s → Quotient s → Quotient s,
        ∀ a b, C (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (comp a b) :=
  by
  rintro ⟨C, hC⟩
  apply hgz
  apply Quotient.exact
  calc
    Quotient.mk s g = Quotient.mk s (comp i g) := (Quotient.sound hig).symm
    _ = C (Quotient.mk s i) (Quotient.mk s g) := (hC i g).symm
    _ = C (Quotient.mk s f) (Quotient.mk s g) := by rw [Quotient.sound hfi]
    _ = Quotient.mk s (comp f g) := (hC f g)
    _ = Quotient.mk s z := Quotient.sound hfg

/-- The Weakly Total construction in `FailureOfComposition`. -/
def WeaklyTotal {A : Type u} (s : Setoid A) (comp : A → A → A) (z e : A) : Prop :=
  ∀ d, s.r (comp e d) z → s.r d z

theorem weaklyTotal_identity {A : Type u} (s : Setoid A) (comp : A → A → A) (i z : A)
    (hi : ∀ d, s.r (comp i d) d) : WeaklyTotal s comp z i :=
  by
  intro d hd
  exact s.trans (s.symm (hi d)) hd

theorem not_weaklyTotal_guard {A : Type u} (s : Setoid A) (comp : A → A → A) (f g z : A)
    (hfg : s.r (comp f g) z) (hgz : ¬s.r g z) : ¬WeaklyTotal s comp z f :=
  by
  intro hf
  exact hgz (hf g hfg)

end FailureOfComposition

end

end PointwiseComposition
