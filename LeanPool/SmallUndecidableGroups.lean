/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin

/-!
# Small undecidable groups and effective Adian–Rabin families

Source: arxiv:2609.10461, url:https://github.com/32805433/Adian-Rabin
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
Status: verified
Main declarations: `Undecidability.exists_small_undecidable_presentations`
Tags: group-theory, undecidability, finite-presentations, hnn-extensions, rewriting-systems
MSC: 20F10, 03D35
-/

@[expose] public section

namespace Undecidability

/-- There is a three-generator, nine-relator group with unsolvable word problem. -/
theorem exists_three_generator_nine_relator_group_with_unsolvable_word_problem :
    ∃ P : FP 3 9,
      ¬ ComputablePred P.wordProblem := by
  obtain ⟨P, _, hP⟩ := Host.exists_threeNineHost
  exact ⟨P, hP⟩

/--
There is an effective Adian--Rabin family for triviality whose members have four
generators and eleven relators.
-/
theorem exists_four_generator_eleven_relator_adian_rabin_family :
    ∃ A : ℕ → FP 4 11,
      FP.IsAdianRabinFamily A := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact AdianRabin.exists_miller_tancer_family
    (Host.presentationOf datum) (2 : Fin 3)
      (Host.wordProblem_unsolvable datum) (by
        simpa [Host.zWord] using Host.z_normallyGenerates datum)

/--
There is an effective Adian--Rabin family for triviality whose members have two
generators and ten relators.
-/
theorem exists_two_generator_ten_relator_adian_rabin_family :
    ∃ A : ℕ → FP 2 10,
      FP.IsAdianRabinFamily A := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact AdianRabin.exists_gordon_family
    (Host.presentationOf datum) (Host.gordonCondition21 datum)
      (Host.wordProblem_unsolvable datum)

/-- The three small-presentation bounds, collected with their effective
undecidability assertions. -/
theorem exists_small_undecidable_presentations :
    (∃ P : FP 3 9, ¬ ComputablePred P.wordProblem) ∧
      (∃ A : ℕ → FP 4 11, FP.IsAdianRabinFamily A) ∧
      ∃ A : ℕ → FP 2 10, FP.IsAdianRabinFamily A :=
  ⟨exists_three_generator_nine_relator_group_with_unsolvable_word_problem,
    exists_four_generator_eleven_relator_adian_rabin_family,
    exists_two_generator_ten_relator_adian_rabin_family⟩

end Undecidability

/-!
## Upstream license

The upstream source is MIT licensed. Its original notice follows.

MIT License

Copyright (c) 2026 Qiuyu Ren

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
