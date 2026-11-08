import LeanLab.ExceptionalSet.Progressions465
import LeanLab.ExceptionalSet.Arithmetic465
import LeanLab.ExceptionalSet.Growth465

/-!
P0082 page364 display22 and its large conductor consequence.
The only analytic input is Lemma4, passed as an explicit hypothesis.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page364 display22 and the next sentence. This has the exact
new large gcd leaf statement, with Lemma4 as an explicit input.
CONDITIONAL ON that discrepancy estimate. No new admission is used. -/
theorem large_gcd_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              (((window γ N).filter (fun n =>
                (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨D, hD, hτ⟩ := divisor_count_ratio
  obtain ⟨δ₀, hδ₀, hp⟩ := progression_counts h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hp⟩ := hp δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨C, hC, Np, hp⟩ := hp κ hκ hκsmall
  obtain ⟨Ng, hg⟩ := logarithmic_error_absorbed γ δ κ h1 h2 hδ hκ
  refine ⟨24 * C * (D + 1), by positivity, max 16 (max Np Ng), fun N hN r hr hrP hlarge j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNg : Ng ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hrNat : 0 < r := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    apply mul_nonneg hκ.le
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hprog : ∀ d ∈ r.divisors,
      (((window γ N).filter (fun n => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdr : d ≤ r := Nat.le_of_dvd hrNat (Nat.mem_divisors.mp hd).1
    exact hp N hNp d hd1 ((by exact_mod_cast hdr : (d : ℝ) ≤ r).trans hrP) j hj
  have hcount := large_gcd_of_progressions (window γ N) (fun n => nu γ n + j)
    r hrNat C (calE γ κ N) N hE hprog
  have hτr := hτ (calE γ κ N) hE1 r hr hlarge
  have hlogr : Real.log r ≤ 6 * δ * Real.log (F γ N) := by
    calc
      _ ≤ Real.log (F γ N ^ (6 * δ)) := Real.log_le_log hr0 hrP
      _ = _ := Real.log_rpow hX _
  have hsigma : ((∑ d ∈ r.divisors, (d : ℝ)) / r) / calE γ κ N ≤
      calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    refine (div_le_div_of_nonneg_right ((divisor_sum_ratio r hrNat).trans ?_) hE.le).trans (hg N hNg)
    linarith
  calc
    _ ≤ 24 * (C * N * r.divisors.card + C * N / calE γ κ N * ∑ d ∈ r.divisors, (d : ℝ)) / r := hcount
    _ = (24 * C * N) * ((r.divisors.card : ℝ) / r +
        ((∑ d ∈ r.divisors, (d : ℝ)) / r) / calE γ κ N) := by ring
    _ ≤ (24 * C * N) * (D * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        calE γ κ N ^ (-(1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hτr hsigma) (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
