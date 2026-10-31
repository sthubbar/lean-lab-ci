/-
P0011 Deshouillers, Effinger, te Riele, Zinoviev 1997, the even range the main theorem needs.
Unit U-1269, PC run 20261020T1903Z-4664, track T1, Part 2. AI wrote this Lean code; checked
only by the Lean kernel. Known mathematics, bookkeeping only.

P0011 assembles its main theorem from Zinoviev's `10^20` bound, the intermediate lemma with gap
`1.615 · 10^12`, and the Deshouillers-te Riele even check to `10^13`, `dtr`. The even check is
used only at `n - 3` for small odd `n` and at `n - p ≤ H` for the rest, so any range `E ≥ H`
suffices. Here:
* `derz_main_of_gap_even`: the assembly for any gap `H ≤ E` and even range `E`;
* `derz_main_of_even1615`: the printed lemma needs the even check only to `1.615 · 10^12`;
* `derz_main_of_hsw_even`: under GRH, CONDITIONAL ON Zinoviev's `10^20` bound,
  `HSWN70`, `HSWHead14`, `Ordinates14`, and the even check only to `1.545 · 10^12`,
  from cloud48's `theta_uniform_hsw`, `|θ(x) - x| ≤ 7.72 · 10^11` on `[10^11, 10^20]`.
The cited `dtr` to `10^13` is NOT closed: a check to `1.545 · 10^12` is still a cited computation,
and no ladder lowers it, since the even number `n - p` must itself be a Goldbach sum.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.PNTPort.ExplicitPsi1.DERZSchoenfeld
import LeanLab.Ricci1937.FormA

namespace LeanLab.DERZ1997
open Real Chebyshev
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)

/-- The paper's assembly with gap bound `H` and even range `E`, `H ≤ E`. -/
theorem derz_main_of_gap_even (H E : ℕ) (hHE : H ≤ E)
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ H)
    (hD : EvenGoldbachUpTo E) :
    GRH → TernaryGoldbach := by
  intro hG n ho h7
  rcases Nat.lt_or_ge (10 ^ 20) n with hbig | hsmall
  · exact hZ hG n ho hbig
  rcases Nat.lt_or_ge n (E + 4) with hlow | hmid
  · have hev : Even (n - 3) := Nat.Odd.sub_odd ho (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  · obtain ⟨p, hp, h4, hle⟩ := hL hG n (by omega) hsmall
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hev : Even (n - p) := Nat.Odd.sub_odd ho hpodd
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - p) hev h4 (by omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-- **P0011 main theorem with the even check only to `1.615 · 10^12`**: `derz_main_of` with
`dtr`'s range `10^13` lowered to the printed lemma's gap. CONDITIONAL ON Zinoviev, the lemma,
and the even check to `1615 · 10^9`. -/
theorem derz_main_of_even1615
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9)
    (hD : EvenGoldbachUpTo (1615 * 10 ^ 9)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap_even (1615 * 10 ^ 9) (1615 * 10 ^ 9) le_rfl hZ hL hD

/-- The gap `1.545 · 10^12` from `theta_uniform_hsw`, under RH and the zero counts. -/
theorem derz_gap1545_hsw (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1545 * 10 ^ 9 :=
  gap_of_theta (10 ^ 11) (772 * 10 ^ 9) (1545 * 10 ^ 9) le_rfl
    (fun _ h1 h2 => theta_uniform_hsw hRH hN hH h14 h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- **P0011 main theorem, no Schoenfeld input, even check only to `1.545 · 10^12`**: GRH implies
ternary Goldbach, CONDITIONAL ON Zinoviev's `10^20` bound, `HSWN70`, `HSWHead14`,
`Ordinates14` and `EvenGoldbachUpTo (1545 · 10^9)`. -/
theorem derz_main_of_hsw_even
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    (hD : EvenGoldbachUpTo (1545 * 10 ^ 9)) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap_even (1545 * 10 ^ 9) (1545 * 10 ^ 9) le_rfl hZ
    (fun hG => derz_gap1545_hsw (rh_of_GRH hG) hN hH h14) hD

/-- The new even input is weaker than the paper's: `dtr`'s range implies it. -/
theorem even1545_of_dtr (h : EvenGoldbachUpTo (10 ^ 13)) : EvenGoldbachUpTo (1545 * 10 ^ 9) :=
  fun n he h4 hn => h n he h4 (by omega)

/-! ### Vacuity -/

/-- `derz_main_of_gap_even`'s even input is satisfiable by a kernel-checked range: Ricci's
`EvenGoldbachUpTo 6720`, with `H = E = 6720`. The lemma input at `H = 6720` is then the claim
that prime gaps below `10^20` are below `6716`; maximal gap tables to `2^64` give at most
`1550`, not proved here. This only shows the theorem's even input can hold. -/
example (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 6720) :
    GRH → TernaryGoldbach :=
  derz_main_of_gap_even 6720 6720 le_rfl hZ hL
    LeanLab.Ricci1937.evenGoldbachUpTo_6720

end LeanLab.DERZ1997
