/-
Copyright (c) 2026 Lean Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI
-/

import Mathlib

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma3

/-- The number of primes `p = l (mod k)` with `y < p ≤ x + y`. -/
def pi_interval (x y : ℝ) (k l : ℕ) : ℕ :=
  ((Ioc ⌊y⌋₊ ⌊x + y⌋₊).filter (fun p => p.Prime ∧ p ≡ l [MOD k])).card

/-- Unformalized Lemma 3 from Vaughan 1977 (P0066).
    A sharp form of the Brun-Titchmarsh theorem: `π(x+y; k, l) - π(y; k, l) < 2x / (φ(k) log(x/k))`.
    The theorem holds for `x > k` and all `y`, for a modulus `k ≥ 1`.
    Cited input, Montgomery and Vaughan 1973 Theorem 2; not proved here, any use is CONDITIONAL.
    Review fix by Claude: the hypothesis `0 < k` was added; without it the Prop is false at
    `k = 0`, since then the right side is `0` in Lean while `pi_interval 10 0 0 2 = 1`. -/
def Lemma3 : Prop :=
  ∀ (x y : ℝ) (k l : ℕ), 0 < k → (k : ℝ) < x →
    (pi_interval x y k l : ℝ) ≤ 2 * x / ((k.totient : ℝ) * Real.log (x / k))

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma3
