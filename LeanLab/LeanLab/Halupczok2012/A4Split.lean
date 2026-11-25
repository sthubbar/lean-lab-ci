import LeanLab.Halupczok2012.Split398aMajor
import LeanLab.Halupczok2012.Split398aMinor

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

/-- `q/φ(q) ≤ Σ_{d ∣ q} 1/φ(d)`, from `φ(d) φ(q/d) ≤ φ(q)` and `Σ_{d ∣ q} φ(q/d) = q`. PROVED. -/
theorem q_div_phi_le (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (Nat.totient q : ℝ) ≤ ∑ d ∈ q.divisors, 1 / (Nat.totient d : ℝ) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [div_le_iff₀ hφ, Finset.sum_mul]
  have hnat : ∑ d ∈ q.divisors, Nat.totient (q / d) = q := by
    rw [Nat.sum_div_divisors, Nat.sum_totient]
  have hq' : (q : ℝ) = ∑ d ∈ q.divisors, (Nat.totient (q / d) : ℝ) := by
    rw [← Nat.cast_sum, hnat]
  rw [hq']
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 hd0
  have h := Nat.totient_super_multiplicative d (q / d)
  rw [Nat.mul_div_cancel' hdq] at h
  have h' : (Nat.totient d : ℝ) * (Nat.totient (q / d) : ℝ) ≤ Nat.totient q := by exact_mod_cast h
  rw [one_div_mul_eq_div, le_div_iff₀ hφd]
  linarith

/-- LEAF: PP1993 p. 45, the bound `Σ_{q ≤ L^B} q/φ(q) ≪ L^B` used for the error of the two
unnumbered displays after display 7; classical, `q/φ(q) = Σ_{d ∣ q} μ(d)^2/φ(d)`. Class EASY.
PROVED by S135 from `q/φ(q) ≤ Σ_{d ∣ q} 1/φ(d)`, `#{q ≤ X : d ∣ q} ≤ X/d`, `d ≤ 4 φ(d)^2` and
the convergence of `Σ d^(-3/2)`. -/
theorem leaf_a4_sum_q_div_phi : SumQDivPhi := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  set T := ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) with hT
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => by positivity)
  refine ⟨2 * T + 1, by positivity, ?_⟩
  intro X hX
  set n := ⌊X⌋₊ with hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le (by linarith)
  set Q := Icc 1 n with hQ
  have hdiv : ∀ q ∈ Q, q.divisors = Q.filter (fun d => d ∣ q) := by
    intro q hq
    have hq1 := (Finset.mem_Icc.mp hq)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, hQ, Finset.mem_Icc]
    constructor
    · rintro ⟨hdq, _⟩
      have := Nat.le_of_dvd (by omega) hdq
      have := Nat.pos_of_dvd_of_pos hdq (by omega)
      exact ⟨⟨by omega, by omega⟩, hdq⟩
    · rintro ⟨_, hdq⟩; exact ⟨hdq, by omega⟩
  have hswap : ∑ q ∈ Q, ∑ d ∈ q.divisors, 1 / (Nat.totient d : ℝ) =
      ∑ d ∈ Q, 1 / (Nat.totient d : ℝ) * ((Q.filter (fun q => d ∣ q)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun q hq => by rw [hdiv q hq])]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : ∀ d ∈ Q, ((Q.filter (fun q => d ∣ q)).card : ℝ) ≤ X / d := by
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hQ' : Q = Ioc 0 n := by rw [hQ]; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hQ', Nat.Ioc_filter_dvd_card_eq_div]
    calc ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      _ ≤ X / d := div_le_div_of_nonneg_right hnX (by positivity)
  have hterm : ∀ d ∈ Q, 1 / (Nat.totient d : ℝ) * ((Q.filter (fun q => d ∣ q)).card : ℝ) ≤
      X * (2 * (1 / (d : ℝ) ^ (3 / 2 : ℝ))) := by
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have h4 := Split398aMinor.b4_le_four_totient_sq d hd1
    have hs0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
    have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hdpos.le
    have hφ2 : Real.sqrt d ≤ 2 * Nat.totient d := by
      by_contra hc; push_neg at hc; nlinarith
    have hinv : 1 / (Nat.totient d : ℝ) ≤ 2 / Real.sqrt d := by
      rw [div_le_div_iff₀ hφd hs0]; linarith
    have h32 : (d : ℝ) ^ (3 / 2 : ℝ) = d * Real.sqrt d := by
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hdpos, Real.rpow_one]
    calc 1 / (Nat.totient d : ℝ) * ((Q.filter (fun q => d ∣ q)).card : ℝ)
        ≤ 2 / Real.sqrt d * (X / d) :=
          mul_le_mul hinv (hcard d hd) (by positivity) (by positivity)
      _ = X * (2 * (1 / (d : ℝ) ^ (3 / 2 : ℝ))) := by
          rw [h32]; field_simp
  have htail : ∑ d ∈ Q, 1 / (d : ℝ) ^ (3 / 2 : ℝ) ≤ T :=
    hsum.sum_le_tsum Q (fun i _ => by positivity)
  calc ∑ q ∈ Icc 1 ⌊X⌋₊, (q : ℝ) / (Nat.totient q : ℝ)
      ≤ ∑ q ∈ Q, ∑ d ∈ q.divisors, 1 / (Nat.totient d : ℝ) :=
        Finset.sum_le_sum (fun q hq => q_div_phi_le q (Finset.mem_Icc.mp hq).1)
    _ = ∑ d ∈ Q, 1 / (Nat.totient d : ℝ) * ((Q.filter (fun q => d ∣ q)).card : ℝ) := hswap
    _ ≤ ∑ d ∈ Q, X * (2 * (1 / (d : ℝ) ^ (3 / 2 : ℝ))) := Finset.sum_le_sum hterm
    _ = X * (2 * ∑ d ∈ Q, 1 / (d : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ X * (2 * T) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ ≤ (2 * T + 1) * X := by nlinarith

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
