/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.ExactLearningTheorem

/-!
# Exact adaptive single-copy stabilizer learning

Source: arxiv:2610.02031
Authors: Antonio Anna Mele
Status: verified
Main declarations: `LeanPool.SingleCopyStabilizer.ExactLearningTheorem.exact_learning`
Tags: quantum-computing, stabilizer-states, quantum-learning, probability
MSC: 81P68, 68Q32, 81P45
-/

/-!
## Mathematical overview

Ported from Antonio Anna Mele’s MIT-licensed formalization at
`d8282e1d59a1a9b8d34396f06298f478c54237c6`.

The original license for this project’s imported sources follows.
-/

/-
MIT License

Copyright (c) 2026 Antonio Anna Mele

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
