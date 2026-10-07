/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.ModelSound
import Mathlib.Tactic

/-!
# IntervalCover

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

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

namespace ConwaySoifer.Certificates

/-- Consecutive coverage of `(start, stop]` by the intervals `(C.lo, C.hi]`. -/
def coverChain (stop : Rat) : Rat → List CertData → Bool
  | _, [] => false
  | cur, [C] => decide (C.lo ≤ cur) && decide (stop ≤ C.hi)
  | cur, C :: C' :: rest => decide (C.lo ≤ cur) && coverChain stop C.hi (C' :: rest)

theorem coverChain_sound (stop : Rat) (certs : List CertData) :
    ∀ cur : Rat, coverChain stop cur certs = true → ∀ s : ℝ, (cur : ℝ) < s → s ≤ stop →
      ∃ C ∈ certs, (C.lo : ℝ) < s ∧ s ≤ C.hi := by
  induction certs with
  | nil => intro cur h; simp [coverChain] at h
  | cons C rest ih =>
    intro cur h s hs hstop
    cases rest with
    | nil =>
      simp only [coverChain, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨C, List.mem_singleton_self _, ?_, ?_⟩
      · have : (C.lo : ℝ) ≤ cur := by
          exact_mod_cast h.1
        linarith
      · have : (stop : ℝ) ≤ C.hi := by
          exact_mod_cast h.2
        linarith
    | cons C' rest' =>
      simp only [coverChain, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases le_or_gt s (C.hi : ℝ) with hle | hlt
      · refine ⟨C, List.mem_cons_self .., ?_, hle⟩
        have : (C.lo : ℝ) ≤ cur := by
          exact_mod_cast h.1
        linarith
      · obtain ⟨D, hD, hlo, hhi⟩ := ih C.hi h.2 s hlt hstop
        exact ⟨D, List.mem_cons_of_mem _ hD, hlo, hhi⟩

end ConwaySoifer.Certificates
