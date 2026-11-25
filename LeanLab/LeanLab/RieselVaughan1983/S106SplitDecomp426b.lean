import LeanLab.RieselVaughan1983.Lemma6Theta
import LeanLab.BS2022GRH.ThetaInputs224
import LeanLab.RieselVaughan1983.S143SplitDusartRows

/-!
Split for the two initial band leaves of Decomp426b, session S106, burst-20261122.
On the band 22 ≤ log x < 27 every x lies below 10^19, inside the range of the
finite verification in Buthe 2018 Theorem 2, displays 1.6 and 1.7,
arXiv 1511.02032 page 2. Dusart 2010 itself reaches these signs on this band
through the exact theta tables, see the proof of Proposition 5.1 on page 4.
The lower side display 1.7 is the shared lab leaf ThetaInputs224.theta_buthe_1e19.
The upper side display 1.6 is the one new LEAF below.
Both assembly theorems below carry statements identical to the originals.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.S106SplitDecomp426b

/-- Was LEAF, wired by S143 to the shared lab leaf: Buthe 2018 Theorem 2, display 1.6, arXiv 1511.02032 page 2:
x minus theta x is at most 1.95 sqrt x for 1423 ≤ x ≤ 10^19.
A finite analytic computation, cited. Class HARD for Codex. -/
theorem buthe_theta_gap_upper (x : ℝ) (hx : 1423 ≤ x) (hx1 : x ≤ 1e19) :
    x - θ x ≤ 1.95 * sqrt x :=
  -- S143: this is the shared lab leaf for the same display, cited once.
  LeanLab.BS2022GRH.ThetaLeavesS63.buthe2018_display16 x hx hx1

/-- Every x with log x at most 32 is below 10^19. -/
theorem le_1e19_of_log_le_32 (x : ℝ) (hx : 0 < x) (h32 : log x ≤ 32) :
    x ≤ 1e19 := by
  have hx' : x ≤ exp 32 := by
    rw [← exp_log hx]; exact exp_le_exp.mpr h32
  have he : exp (32 : ℝ) ≤ 3 ^ 32 := by
    have h1 : exp (1 : ℝ) ≤ 3 := (exp_one_lt_d9.trans (by norm_num)).le
    have : exp (32 : ℝ) = exp 1 ^ 32 := by
      rw [← exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (exp_pos 1).le h1 32
  linarith [show (3 : ℝ) ^ 32 ≤ 1e19 by norm_num]

/-- Every x with log x below 27 is below 10^19. -/
theorem le_1e19_of_log_lt_27 (x : ℝ) (hx : 0 < x) (h27 : log x < 27) :
    x ≤ 1e19 :=
  le_1e19_of_log_le_32 x hx (by linarith)

/-- Every x with log x at least 22 is at least exp 22. -/
theorem exp22_le_of_log (x : ℝ) (hx : 0 < x) (h22 : 22 ≤ log x) :
    exp 22 ≤ x := by
  rw [← exp_log hx]; exact exp_le_exp.mpr h22

/-- Statement identical to Task426.dusart_initial_upper.
CONDITIONAL ON the shared lab leaf ThetaInputs224.theta_buthe_1e19,
Buthe 2018 Theorem 2 display 1.7. -/
theorem dusart_initial_upper (x : ℝ) (hx : 0 < x) (h22 : 22 ≤ log x)
    (h27 : log x < 27) :
    θ x - x < x / 36260 := by
  have hx1 : 1 ≤ x := by
    have := exp22_le_of_log x hx h22
    have : (1 : ℝ) ≤ exp 22 := one_le_exp (by norm_num)
    linarith
  have hB := LeanLab.BS2022GRH.ThetaInputs224.theta_buthe_1e19 x hx1
    (le_1e19_of_log_lt_27 x hx h27)
  have hs : 0 ≤ sqrt x := sqrt_nonneg x
  have hq : 0 < x / 36260 := by positivity
  nlinarith

/-- Statement identical to Task426.dusart_initial_lower.
CONDITIONAL ON the LEAF buthe_theta_gap_upper above, Buthe 2018 display 1.6. -/
theorem dusart_initial_lower (x : ℝ) (hx : 0 < x) (h22 : 22 ≤ log x)
    (h27 : log x < 27) :
    -(1 / 1000 : ℝ) * x / log x < θ x - x := by
  have hE := exp22_le_of_log x hx h22
  have he11 : (52651 : ℝ) ≤ exp 11 := by
    have h := Lemma6Theta.exp_nat_ge 11
    norm_num at h
    linarith
  have hsq : exp 11 ≤ sqrt x := by
    have : exp (22 : ℝ) = exp 11 ^ 2 := by
      rw [← exp_nat_mul]; norm_num
    rw [this] at hE
    calc exp 11 = sqrt (exp 11 ^ 2) := (sqrt_sq (exp_pos 11).le).symm
      _ ≤ sqrt x := sqrt_le_sqrt hE
  have h1423 : (1423 : ℝ) ≤ x := by
    have := sq_sqrt hx.le
    nlinarith
  have hB := buthe_theta_gap_upper x h1423 (le_1e19_of_log_lt_27 x hx h27)
  have hL : 0 < log x := by linarith
  have hs0 : 0 < sqrt x := by linarith
  have hxs : sqrt x * sqrt x = x := mul_self_sqrt hx.le
  -- 1950 log x < 1950 * 27 < 52651 ≤ sqrt x
  have hkey : 1950 * log x < sqrt x := by linarith
  have hgoal : 1.95 * sqrt x < (1 / 1000 : ℝ) * x / log x := by
    rw [lt_div_iff₀ hL]
    have hm := mul_lt_mul_of_pos_left hkey hs0
    nlinarith [hm, hxs]
  have : -(1 / 1000 : ℝ) * x / log x = -((1 / 1000 : ℝ) * x / log x) := by ring
  rw [this]
  linarith

/-- Was LEAF, split by S143 in S143SplitDusartRows: Dusart 2010 page 15, Table 6.3, theta column, rows b = 32 and b = 100.
Each estimate is restricted to the bounded interval ending at u, as in
Task426.dusart_theta_relative_rows; only these two of its four rows remain cited.
Class HARD for Codex. -/
theorem dusart_theta_late_rows (b u ε x : ℝ)
    (hrow : (b, u, ε) ∈
      ([(32, 100, 4057 / 1000000000), (100, 300, 2903 / 100000000000000)] :
        List (ℝ × ℝ × ℝ)))
    (hx : 0 < x) (hb : b ≤ log x) (hu : log x ≤ u) :
    |θ x - x| < ε * x :=
  -- S143: split in S143SplitDusartRows, row b = 32 from shared lab leaves, row b = 100 a LEAF.
  LeanLab.RieselVaughan1983.S143SplitDusartRows.dusart_theta_late_rows_of_leaves b u ε x hrow hx hb hu

/-- The two early Table 6.3 theta rows on 27 ≤ log x ≤ 32 follow from both halves of
Buthe 2018 Theorem 2, displays 1.6 and 1.7, since every such x is below 10^19.
CONDITIONAL ON the LEAF buthe_theta_gap_upper and the shared lab leaf
ThetaInputs224.theta_buthe_1e19. -/
theorem early_theta_rows_of_buthe (x : ℝ) (hx : 0 < x) (h27 : 27 ≤ log x)
    (h32 : log x ≤ 32) :
    |θ x - x| < (2308 / 100000000 : ℝ) * x := by
  have hE : exp 26 ≤ x := by
    rw [← exp_log hx]; exact exp_le_exp.mpr (by linarith)
  have he13 : (440000 : ℝ) ≤ exp 13 := by
    have h := Lemma6Theta.exp_nat_ge 13
    norm_num at h
    linarith
  have hsq : exp 13 ≤ sqrt x := by
    have : exp (26 : ℝ) = exp 13 ^ 2 := by
      rw [← exp_nat_mul]; norm_num
    rw [this] at hE
    calc exp 13 = sqrt (exp 13 ^ 2) := (sqrt_sq (exp_pos 13).le).symm
      _ ≤ sqrt x := sqrt_le_sqrt hE
  have hxs : sqrt x * sqrt x = x := mul_self_sqrt hx.le
  have hs0 : 0 < sqrt x := by linarith
  have h1423 : (1423 : ℝ) ≤ x := by nlinarith
  have h1e19 := le_1e19_of_log_le_32 x hx h32
  have hU := buthe_theta_gap_upper x h1423 h1e19
  have hL := LeanLab.BS2022GRH.ThetaInputs224.theta_buthe_1e19 x (by linarith) h1e19
  have hgap : 1.95 * sqrt x < (2308 / 100000000 : ℝ) * x := by
    have hk : (1.95 : ℝ) < (2308 / 100000000 : ℝ) * sqrt x := by linarith
    nlinarith [mul_lt_mul_of_pos_left hk hs0]
  rw [abs_lt]
  constructor <;> nlinarith

/-- Statement identical to Task426.dusart_theta_relative_rows.
CONDITIONAL ON the LEAFs buthe_theta_gap_upper and dusart_theta_late_rows and the
shared lab leaf ThetaInputs224.theta_buthe_1e19. -/
theorem dusart_theta_relative_rows (b u ε x : ℝ)
    (hrow : (b, u, ε) ∈
      ([(27, 28, 3507 / 100000000), (28, 32, 2308 / 100000000),
        (32, 100, 4057 / 1000000000), (100, 300, 2903 / 100000000000000)] :
        List (ℝ × ℝ × ℝ)))
    (hx : 0 < x) (hb : b ≤ log x) (hu : log x ≤ u) :
    |θ x - x| < ε * x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
  rcases hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have h := early_theta_rows_of_buthe x hx hb (by linarith)
    nlinarith
  · exact early_theta_rows_of_buthe x hx (by linarith) hu
  · exact dusart_theta_late_rows 32 100 _ x (by simp) hx hb hu
  · exact dusart_theta_late_rows 100 300 _ x (by simp) hx hb hu

end LeanLab.RieselVaughan1983.S106SplitDecomp426b
