import LeanLab.HeathBrownPuchta.SReduction

/-!
# Heath-Brown and Puchta 2002, display 41: the Liu, Liu and Wang input split

P0012 page 26 quotes Liu, Liu and Wang 1999, J. Theor. Nombres Bordeaux 11, display 3.9:
`2X/φ(2X) ≤ 2 e^γ log x` for `x ≥ 9`, `X = Π_{d ≤ x} (2^d - 1)`.  Their proof, page 142,
uses Rosser and Schoenfeld 1962 display 3.42, `d/φ(d) < u(d)` with
`u(d) = e^γ log log d + 2.5064/log log d`, the monotonicity of `u` for `d ≥ 30`, and
`2X ≤ 2^(x²+1)`.  This file states those pieces as leaves and proves
`SReduction.LLW` and the parent `c2_bound` from them.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.HeathBrownPuchta.DecompJ417LeavesC2

open LeanLab.HeathBrownPuchta.SReduction

/-- Liu, Liu and Wang 1999 page 142, the function `u(d)` defined after display 3.9 from
Rosser and Schoenfeld display 3.42. -/
noncomputable def uRS (t : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) +
    25064 / 10000 / Real.log (Real.log t)

/-- LEAF: Rosser and Schoenfeld 1962 display 3.42, as used by Liu, Liu and Wang page 142.
Class CITED-LEFT. P0012 page 26, reference 13. For every integer `d ≥ 3`,
`d/φ(d) < u(d)`. The RS exception `d = 223092870` still satisfies the bound with 2.5064. -/
theorem rosser_schoenfeld_342 (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) / (Nat.totient d : ℝ) < uRS d := by
  sorry

/-- LEAF: Liu, Liu and Wang 1999 page 142, after display 3.9: the function `u` increases
for `d ≥ 30`. Class MEDIUM. P0012 page 26, reference 13. Real calculus: `log log t ≥ 1.22`
on `t ≥ 30` and `e^γ s + 2.5064/s` increases for `s² ≥ 2.5064/e^γ`. -/
theorem uRS_mono (a b : ℝ) (ha : 30 ≤ a) (hab : a ≤ b) : uRS a ≤ uRS b := by
  sorry

/-- Liu, Liu and Wang 1999 page 142, last display: `2X ≤ 2^(x²+1)`, PROVED here.
P0012 page 26, reference 13. Each factor `2^e - 1` with `e ≤ n` is below
`2^n`, so the product of `n` factors is at most `2^(n²)`. -/
theorem two_mprod_le (n : ℕ) : 2 * (mprod n : ℝ) ≤ 2 ^ (n ^ 2 + 1) := by
  have h : mprod n ≤ 2 ^ (n ^ 2) := by
    unfold mprod
    calc ∏ e ∈ Finset.Icc 1 n, (2 ^ e - 1) ≤ ∏ _e ∈ Finset.Icc 1 n, 2 ^ n := by
          apply Finset.prod_le_prod'
          intro e he
          simp only [Finset.mem_Icc] at he
          exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) he.2)
      _ = 2 ^ (n ^ 2) := by
          rw [Finset.prod_const, Nat.card_Icc, ← pow_mul]; congr 1; simp [sq]
  have h' : (mprod n : ℝ) ≤ 2 ^ (n ^ 2) := by exact_mod_cast h
  rw [pow_succ]; linarith

/-- LEAF: Liu, Liu and Wang 1999 page 142, the scalar step closing display 3.9:
`u(2^(x²+1)) ≤ 2 e^γ log x` for integers `x ≥ 9`. Class MEDIUM. P0012 page 26, reference 13.
Needs a lower bound `e^γ ≥ 1.76` and explicit logarithms; at `x = 9` the margin is about
`0.01`. -/
theorem uRS_endpoint (n : ℕ) (hn : 9 ≤ n) :
    uRS (2 ^ (n ^ 2 + 1)) ≤ 2 * Real.exp Real.eulerMascheroniConstant * Real.log n := by
  sorry

/-- Liu, Liu and Wang display 3.9 in the form `SReduction.LLW`, from the four leaves. -/
theorem llw_of_leaves : LLW := by
  intro n hn
  set X := mprod n with hX
  have hX0 : X ≠ 0 := mprod_ne_zero n
  have hodd : ¬ 2 ∣ X := mprod_odd n
  have h15 : 15 ∣ X := by
    have := dvd_mprod (n := n) (e := 4) (by norm_num) (by omega)
    simpa using this
  have hX15 : 15 ≤ X := Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) h15
  have hcop : Nat.Coprime 2 X := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have htot : Nat.totient (2 * X) = Nat.totient X := by
    rw [Nat.totient_mul hcop]; simp
  have hphi0 : (0 : ℝ) < Nat.totient X := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hX0)
  have h1 := rosser_schoenfeld_342 (2 * X) (by omega)
  rw [htot] at h1
  have h2 : uRS ((2 * X : ℕ) : ℝ) ≤ uRS (2 ^ (n ^ 2 + 1)) := by
    apply uRS_mono
    · have : (30 : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast (by omega : 30 ≤ 2 * X)
      exact this
    · push_cast; exact two_mprod_le n
  have h3 := uRS_endpoint n hn
  have h4 : ((2 * X : ℕ) : ℝ) / (Nat.totient X : ℝ) =
      2 * ((X : ℝ) / (Nat.totient X : ℝ)) := by push_cast; ring
  rw [h4] at h1
  show (X : ℝ) / (Nat.totient X : ℝ) ≤ _
  linarith

/-- P0012 page 26, display 41, `C₂ ≤ 2.2141`, the exact parent statement
`DecompJ417.c2_bound`, from the leaves of this file through `SReduction.C2_le_at_20`. -/
theorem c2_bound_of_leaves : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 :=
  C2_le_at_20 llw_of_leaves

end LeanLab.HeathBrownPuchta.DecompJ417LeavesC2
