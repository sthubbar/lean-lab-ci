import LeanLab.Halupczok2012.Split398aMajor

/-!
# Split of the leaf `Split398aMajor.a4_sigma1`, PP1993 page 45

Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. 47, 1993, page 45, the two unnumbered displays after display 7,
copy papers/PP1993.pdf. With A3, the integral over `xi'_q` is `M*(2k) + O(qY L^(-2B))`, so
`Sigma_1 = M*(2k) S(2k, L^B) + O(Y L^(-2B) Σ_{q ≤ L^B} q/φ(q))`, and `S(2k, L^B)` is the
singular series minus its Ramanujan tail over `q > L^B`.

Leaves, each with a sorry:
* `leaf_a4_ramanujan_expansion`, MEDIUM: the singular series of PP1993 p. 41 is the Ramanujan
  series `Σ_q μ(q)^2/φ(q)^2 c_q(-m)` for even `m ≥ 2`, split at `X`; Vaughan 1981 chapter 3,
  papers/Vaughan1981-ch3.pdf, and the Euler product algebra of `U1457SingSeries`.
* `leaf_a4_sum_q_div_phi`, EASY: `Σ_{q ≤ X} q/φ(q) ≪ X`, the classical average of `q/φ(q)`.
Proved here: `ramanujan_norm_le`, `ppM_le`, and the wiring `a4_sigma1_of_leaves`, which has
exactly the type `A3Stmt → A4Stmt` of the leaf `a4_sigma1`.

Session S135 burst-20261122. AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.A4Split

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a LeanLab.Halupczok2012.Split398aMajor

/-- Statement of the leaf `leaf_a4_ramanujan_expansion`. -/
def RamanujanExpansion : Prop :=
  ∀ m : ℕ, 2 ≤ m → Even m → ∀ X : ℝ, 0 ≤ X →
    ((S m : ℝ) : ℂ) = (∑ q ∈ Icc 1 ⌊X⌋₊, ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujanSum q (-(m : ℤ))) + ramanujanTail m X

/-- Statement of the leaf `leaf_a4_sum_q_div_phi`. -/
def SumQDivPhi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∑ q ∈ Icc 1 ⌊X⌋₊, (q : ℝ) / (Nat.totient q : ℝ) ≤ C * X

/-- LEAF: PP1993 p. 41 and p. 45, the singular series as the Ramanujan series
`Σ_q μ(q)^2/φ(q)^2 c_q(-m)`, for even `m ≥ 2`, split into the moduli up to `X` and the tail
`ramanujanTail m X`; Vaughan 1981 chapter 3, papers/Vaughan1981-ch3.pdf, with the Euler
product of `U1457SingSeries.local_factor`. Class MEDIUM. -/
theorem leaf_a4_ramanujan_expansion : RamanujanExpansion := by
  sorry

/-- LEAF: PP1993 p. 45, the bound `Σ_{q ≤ L^B} q/φ(q) ≪ L^B` used for the error of the two
unnumbered displays after display 7; classical, `q/φ(q) = Σ_{d ∣ q} μ(d)^2/φ(d)`. Class EASY. -/
theorem leaf_a4_sum_q_div_phi : SumQDivPhi := by
  sorry

/-- The Ramanujan sum has modulus at most `φ(q)`. PROVED. -/
theorem ramanujan_norm_le (q : ℕ) (n : ℤ) : ‖ramanujanSum q n‖ ≤ Nat.totient q := by
  unfold ramanujanSum
  refine (norm_sum_le _ _).trans ?_
  simp only [phase, LeanLab.PNTPort.LargeSieve.norm_e, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_redRes]

/-- `M*(m) ≤ Y + 1`: the counted `h` lie in `]N - Y, N]`. PROVED. -/
theorem ppM_le (m : ℕ) {N Y : ℝ} (hY : 0 ≤ Y) : ppM m N Y ≤ Y + 1 := by
  unfold ppM
  have hsub : (Ioo 0 m).filter (ppCond m N Y) ⊆ kRange (N - Y) Y := by
    intro h hh
    simp only [mem_filter, ppCond] at hh
    simp only [kRange, mem_filter, mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, hh.2.1, by linarith [hh.2.2.1]⟩
    have : (h : ℝ) ≤ N - Y + Y := by linarith [hh.2.2.1]
    exact_mod_cast this.trans (Nat.le_ceil _)
  calc (((Ioo 0 m).filter (ppCond m N Y)).card : ℝ) ≤ (kRange (N - Y) Y).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ Y + 1 := card_kRange_le hY

set_option maxHeartbeats 1000000 in
/-- PP1993 p. 45, the two unnumbered displays after display 7: the leaf `a4_sigma1`, exact type
`A3Stmt → A4Stmt`, PROVED from the two LEAFs of this file, with constant `2 + C2 |C3|`. -/
theorem a4_sigma1_of_leaves (hE : RamanujanExpansion) (hQ : SumQDivPhi) (h3 : A3Stmt) :
    A4Stmt := by
  intro ε A hε hA
  obtain ⟨C3, N3, h3'⟩ := h3 ε A hε hA
  obtain ⟨C2, hC2, hs⟩ := hQ
  refine ⟨2 + C2 * |C3|, max N3 3, ?_⟩
  intro N Y k hN hlow hYN hk
  have hN3 : N3 ≤ N := le_trans (le_max_left _ _) hN
  have hN3' : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9; linarith
  have hB0 : 0 < bigB ε A := by unfold bigB; positivity
  have hX1 : 1 ≤ Real.log N ^ bigB ε A := Real.one_le_rpow hL1 hB0.le
  have hX0 : 0 < Real.log N ^ bigB ε A := by linarith
  have hY1 : 1 ≤ Y := (Real.one_le_rpow (by linarith) (by positivity)).trans hlow
  have hY0 : 0 ≤ Y := by linarith
  have hk2 : 2 ≤ 2 * k := by
    simp only [kRange, mem_filter] at hk
    have : (1 : ℝ) < k := by linarith [hk.2.1]
    have : 1 < k := by exact_mod_cast this
    omega
  have hexp := hE (2 * k) hk2 (even_two_mul k) _ hX0.le
  have hmaj : majorQ N ε A = Icc 1 ⌊Real.log N ^ bigB ε A⌋₊ := rfl
  -- Sigma_1 as a sum over q of weight times Ramanujan sum times the integral
  have hsig : sigma1 N Y ε A (2 * k) = ∑ q ∈ majorQ N ε A,
      ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-((2 * k : ℕ) : ℤ)) *
        ∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η) := by
    unfold sigma1
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Finset.sum_mul]
    have : ∑ a ∈ redRes q, phase (-((2 * k : ℕ) : ℝ) * a / q) =
        ramanujanSum q (-((2 * k : ℕ) : ℤ)) := by
      unfold ramanujanSum
      refine Finset.sum_congr rfl (fun a _ => ?_)
      congr 1; push_cast; ring
    rw [this]; ring
  set Mv : ℝ := ppM (2 * k) N Y with hMvdef
  set T := ramanujanTail (2 * k) (Real.log N ^ bigB ε A) with hT
  have hdiff : sigma1 N Y ε A (2 * k) - ((S (2 * k) * Mv : ℝ) : ℂ) =
      (∑ q ∈ majorQ N ε A,
        ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-((2 * k : ℕ) : ℤ)) *
        ((∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η))
          - (Mv : ℂ))) - (Mv : ℂ) * T := by
    rw [hsig]
    have e1 : ((S (2 * k) * Mv : ℝ) : ℂ) = ((S (2 * k) : ℝ) : ℂ) * (Mv : ℂ) := by push_cast; ring
    rw [e1, hexp, ← hmaj]
    simp only [mul_sub, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
    ring
  -- the bound of each term
  have hterm : ∀ q ∈ majorQ N ε A,
      ‖((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-((2 * k : ℕ) : ℤ)) *
        ((∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η))
          - (Mv : ℂ))‖ ≤
      ((q : ℝ) / (Nat.totient q : ℝ)) * (|C3| * Y / Real.log N ^ (2 * bigB ε A)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hA3 := h3' N Y q (2 * k) hN3 hlow hYN hq
    have hμ : ‖((μ q : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
      rw [Complex.norm_intCast]
      have := ArithmeticFunction.abs_moebius_le_one (n := q)
      have h0 : (0 : ℝ) ≤ |((μ q : ℤ) : ℝ)| := abs_nonneg _
      have : |((μ q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast this
      nlinarith
    have hc := ramanujan_norm_le q (-((2 * k : ℕ) : ℤ))
    have hW : 0 < Real.log N ^ (2 * bigB ε A) := Real.rpow_pos_of_pos (by linarith) _
    have hA3' : ‖(∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η *
        phase (-((2 * k : ℕ) : ℝ) * η)) - (Mv : ℂ)‖ ≤ |C3| * q * Y / Real.log N ^ (2 * bigB ε A) := by
      refine hA3.trans ?_
      apply div_le_div_of_nonneg_right _ hW.le
      have : 0 ≤ (q : ℝ) * Y := by positivity
      nlinarith [le_abs_self C3]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hE0 : 0 ≤ ‖(∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η *
        phase (-((2 * k : ℕ) : ℝ) * η)) - (Mv : ℂ)‖ := norm_nonneg _
    calc ‖((μ q : ℤ) : ℂ)‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 * ‖ramanujanSum q (-((2 * k : ℕ) : ℤ))‖ *
          ‖(∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η *
            phase (-((2 * k : ℕ) : ℝ) * η)) - (Mv : ℂ)‖
        ≤ 1 / (Nat.totient q : ℝ) ^ 2 * (Nat.totient q : ℝ) *
          (|C3| * q * Y / Real.log N ^ (2 * bigB ε A)) := by
          gcongr
      _ = ((q : ℝ) / (Nat.totient q : ℝ)) * (|C3| * Y / Real.log N ^ (2 * bigB ε A)) := by
          field_simp
  have hsumq := hs _ hX1
  have hL2B : Real.log N ^ (2 * bigB ε A) =
      Real.log N ^ bigB ε A * Real.log N ^ bigB ε A := by
    rw [two_mul, Real.rpow_add (by linarith)]
  have hLneg : Real.log N ^ (-bigB ε A) = 1 / Real.log N ^ bigB ε A := by
    rw [Real.rpow_neg (by linarith), one_div]
  have hMv : Mv ≤ Y + 1 := ppM_le (2 * k) hY0
  have hMv0 : 0 ≤ Mv := by rw [hMvdef]; unfold ppM; positivity
  rw [hdiff]
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hfirst : ‖∑ q ∈ majorQ N ε A,
      ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-((2 * k : ℕ) : ℤ)) *
        ((∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η))
          - (Mv : ℂ))‖ ≤ C2 * |C3| * (Y * Real.log N ^ (-bigB ε A)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul, hmaj]
    have hK0 : 0 ≤ |C3| * Y / Real.log N ^ (2 * bigB ε A) := by positivity
    calc (∑ q ∈ Icc 1 ⌊Real.log N ^ bigB ε A⌋₊, (q : ℝ) / (Nat.totient q : ℝ)) *
          (|C3| * Y / Real.log N ^ (2 * bigB ε A))
        ≤ (C2 * Real.log N ^ bigB ε A) * (|C3| * Y / Real.log N ^ (2 * bigB ε A)) :=
          mul_le_mul_of_nonneg_right hsumq hK0
      _ = C2 * |C3| * (Y * Real.log N ^ (-bigB ε A)) := by
          rw [hL2B, hLneg]; field_simp
  calc ‖(∑ q ∈ majorQ N ε A,
      ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-((2 * k : ℕ) : ℤ)) *
        ((∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η))
          - (Mv : ℂ))) - (Mv : ℂ) * T‖
      ≤ C2 * |C3| * (Y * Real.log N ^ (-bigB ε A)) + Mv * ‖T‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMv0]
        exact add_le_add hfirst le_rfl
    _ ≤ (2 + C2 * |C3|) * (Y * ‖T‖ + Y * Real.log N ^ (-bigB ε A)) := by
        have hLp : 0 ≤ Y * Real.log N ^ (-bigB ε A) := by positivity
        have h1 : Mv * ‖T‖ ≤ 2 * (Y * ‖T‖) := by nlinarith [hMv]
        have h2 : 0 ≤ C2 * |C3| := by positivity
        have h3 : 0 ≤ C2 * |C3| * (Y * ‖T‖) := mul_nonneg h2 (by positivity)
        linarith

/-- LEAF-free twin of `Split398aMajor.a4_sigma1`, CONDITIONAL ON the two LEAFs of this file. -/
theorem a4_sigma1_twin (h3 : A3Stmt) : A4Stmt :=
  a4_sigma1_of_leaves leaf_a4_ramanujan_expansion leaf_a4_sum_q_div_phi h3

end LeanLab.Halupczok2012.A4Split
