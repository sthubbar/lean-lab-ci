import LeanLab.ExceptionalSet.NearWindow465
import LeanLab.ExceptionalSet.FarWindow465
import LeanLab.ExceptionalSet.GammaRanges465

/-!
P0082 pages360 to362, the infinite Gamma2 mean in Lemma5.
The discrepancy Lemma4 is an explicit cited input.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Supply465
open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 pages361 and362 displays17 to19. The complete infinite Gamma2
average follows from the near progression estimate and the far divisor
bound. CONDITIONAL ON the explicit Lemma4 input. -/
theorem gammaTwo_mean_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N, (r : ℝ) * (∑' q : ℕ,
                if F γ N ^ (6 * δ) < (q : ℝ) ∧ r ∣ q then
                  1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ)) else 0) ≤
                C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨A, hA, hφ⟩ := totient_ratio_log
  obtain ⟨B, hB, hfar⟩ := far_gammaTwo_window_bound
  obtain ⟨κ₀, C, hκ₀, hC, hprog⟩ := progression_counts_below_sqrt h4 γ h1 h2
  refine ⟨1 / 100, by norm_num, fun δ hδ hδsmall => ?_⟩
  obtain ⟨D, hD, hτ⟩ := gammaTwo_divisor_envelope δ hδ
  obtain ⟨Nr, hranges⟩ := gammaTwo_ranges γ δ h1 hδ hδsmall.le
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Nn, hnearparam⟩ := gammaTwo_near_parameters γ δ κ h1 h2 hδ hκ
  obtain ⟨Nf, hfarparam⟩ := gammaTwo_far_parameters γ κ h1 h2 hκ
  refine ⟨2 * A ^ 2 * (4 * D + 1) * C + B, by positivity,
    max 16 (max Nr (max Nn Nf)), fun N hN r hr hrP j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNn : Nn ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNf : Nf ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hP, hthird, hPY, hYsqrt, hYX⟩ := hranges N hNr
  let X := F γ N
  let P := X ^ (6 * δ)
  let Y := ⌊X ^ (1 / 3 : ℝ)⌋₊
  let t := (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q)
  let K := A ^ 2 * (4 * D + 1) * C
  have hX0 : 0 < X := Real.exp_pos _
  have hX : 1 ≤ X := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hY : 1 ≤ Y := Nat.le_floor (by dsimp [Y, X]; linarith)
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hp : ∀ d : ℕ, 1 ≤ d → d ≤ Y →
      (((window γ N).filter (fun n : ℕ => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd hdY
    exact hprog κ hκ hκsmall N hN16 d hd
      ((by exact_mod_cast hdY : (d : ℝ) ≤ Y).trans_lt hYsqrt) j hj
  have htau : ∀ q ∈ Ioc ⌊P⌋₊ Y, (q.divisors.card : ℝ) ≤ D * P ^ (1 / 2 : ℝ) := by
    intro q hq
    have hqI := mem_Ioc.mp hq
    exact hτ X hX q (by have := hqI.1; omega)
      ((by exact_mod_cast hqI.2 : (q : ℝ) ≤ Y).trans hYX)
  have hnear := near_gammaTwo_window_log (window γ N) (fun n => nu γ n + j)
    r Y X P (calE γ κ N) C A D N hr hX hP hPY hYX hE hC.le hA.le hD.le hφ htau hp
  have hnear' : (r : ℝ) * ∑ q ∈ t, ∑ n ∈ window γ N,
      1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ)) ≤
      2 * K * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ K * N * ((1 + Real.log X) ^ 4 * (P ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N)) := by
        convert hnear using 1 <;> dsimp [K] <;> ring
      _ ≤ K * N * (2 * calE γ κ N ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hnearparam N hNn) (by dsimp [K]; positivity)
      _ = _ := by ring
  have hfar' : (r : ℝ) * ∑ n ∈ window γ N,
      4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y ≤
        B * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ B * N * (1 + Real.log X) * X ^ (-(1 / 8 : ℝ)) :=
        hfar γ δ h1 hδ hδsmall.le N hN16 hthird r hrP j hj
      _ = (B * N) * ((1 + Real.log X) * X ^ (-(1 / 8 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfarparam N hNf) (by positivity)
  have hsplit (n : ℕ) (hn : n ∈ window γ N) := by
    have hlo := (mem_filter.mp hn).2.1
    have hj0 : (0 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
    have hm : nu γ n + j ≠ 0 := by
      intro hm
      have hmR : (nu γ n : ℝ) + (j : ℝ) = 0 := by exact_mod_cast hm
      change X / 2 < (nu γ n : ℝ) at hlo
      linarith
    exact gammaTwo_split_bound r P (by positivity) (nu γ n + j) hm Y hY
  calc
    _ ≤ ∑ n ∈ window γ N,
        ((r : ℝ) * (∑ q ∈ t, 1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ))) +
          (r : ℝ) * (4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y)) :=
      sum_le_sum hsplit
    _ = (r : ℝ) * (∑ q ∈ t, ∑ n ∈ window γ N,
          1 / ((q.totient : ℝ) * ((q / Int.gcd (nu γ n + j) q).totient : ℝ))) +
        (r : ℝ) * (∑ n ∈ window γ N,
          4 * (6 + 2 * Real.log Y) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
    _ ≤ 2 * K * N * calE γ κ N ^ (-(1 / 2 : ℝ)) + B * N * calE γ κ N ^ (-(1 / 2 : ℝ)) :=
      add_le_add hnear' hfar'
    _ = _ := by dsimp [K]; ring
end LeanLab.ExceptionalSet.Supply465
