/-
ENCODING A of P0083 Perelli 1996, moved here 2026-10-28 by the architect with Steve live.
It was the PC copy of Perelli1996/Statements.lean, run 20261018T1603Z-12862, and never reached
main: the repo kept encoding B, now B/* and Definitions88, and the thin Statements.lean. PC-built
files that use encoding A, Merge, Cor2, Routes/U1579Perelli, failed on main with Unknown
constant. The text below is the PC file verbatim except the namespace, now
`LeanLab.Perelli1996.EncA`, so it can sit beside Definitions88 without name clashes.
-/
/-
P0083 A. Perelli, Goldbach numbers represented by polynomials,
Rev. Mat. Iberoamericana 12 (1996), no. 2, 477-490. Read from a scan with no text layer,
every page rendered, Theorems 1, 2, the 7/(36k) remark and (21), (22), (25) checked at 300 dpi.

* Theorem 1, p. 478, mean square over `N^{1/k} ≤ n ≤ N^{1/k} + H` of
  `R(F(n)) - F(n)𝔖(F(n))` is `≪ H N² L^{-A}` for `N^{1/(3k)+ε} ≤ H ≤ N^{1/k}`. CITED, sorry.
* Corollary 1, p. 478, first part PROVED from Theorem 1; second part, Goldbach numbers among
  the even values, CITED, sorry; the remark of p. 478-479 with `N^{7/(36k)+ε}`, CITED, sorry.
* Theorem 2 and Corollary 2, p. 479, and the Lemma of p. 482, CITED, sorry.
* PROVED: Corollary 1 for `F = 2x^k` implies Perelli's `E_k(N) ≪ N (log N)^{-A}`, display
  (5.4) of Pintz 2021, the lab's `PolyLogPowerSaving k`, for every `k ≥ 1`; the parity count
  `|A_F(N,H)| = ρ_F(2)H/2 + O(1)`; `𝔖(n) = 0` for odd `n`; the exponent arithmetic of
  (9), (10), (13), (25), (26), (32) and the Huxley thresholds `1/(3k)` and `1/(6k)`.
* QUESTION, PRELIMINARY: the exponent `25` in (22), p. 485, see STATEMENTS.md.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.ExceptionalSet.Statements
import LeanLab.ExceptionalSet.Pintz2021
import LeanLab.PerelliPintz1992.Statements
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.Perelli1996.EncA
open Real Filter Topology ArithmeticFunction Polynomial
open LeanLab.ExceptionalSet.Pintz2021 (EPoly EPoly_le PolyLogPowerSaving)

attribute [local instance] Classical.propDecidable

/-! ### Definitions, Section 1 p. 477-479 -/

/-- `R(n) = Σ_{r+s=n} Λ(r)Λ(s)`, p. 477, the lab's `PerelliPintz1992.r`. -/
noncomputable abbrev R (n : ℕ) : ℝ := LeanLab.PerelliPintz1992.r n

/-- `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p ∣ n} (1 + 1/(p-1))`, p. 477. -/
noncomputable def Sing (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `𝔖 = 2 ∏_{p>2} (1 - 1/(p-1)²)`, p. 479, twice the lab's twin prime constant. -/
noncomputable def SingConst : ℝ := 2 * LeanLab.ChenExplicit.twinC

/-- `ρ_F(d) = #{m mod d : F(m) ≡ 0 mod d}`, p. 478. -/
noncomputable def rhoF (F : ℤ[X]) (d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun m : ℕ => (d : ℤ) ∣ F.eval (m : ℤ))).card

/-- `F(n)` as a natural number; `F(n) > 0` for the large `n` the paper uses. -/
noncomputable def Fn (F : ℤ[X]) (n : ℕ) : ℕ := (F.eval (n : ℤ)).toNat

/-- `k = deg F` as a real number. -/
noncomputable def deg (F : ℤ[X]) : ℝ := F.natDegree

/-- `deg F = k ≥ 1` and positive leading coefficient, p. 477. -/
def Admissible (F : ℤ[X]) : Prop := 1 ≤ F.natDegree ∧ 0 < F.leadingCoeff

/-- The integers `n` with `x ≤ n ≤ x + H`. -/
noncomputable def nRange (x H : ℝ) : Finset ℕ := Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊

/-- `R(F(n)) - F(n)𝔖(F(n))`. -/
noncomputable def err (F : ℤ[X]) (n : ℕ) : ℝ := R (Fn F n) - (Fn F n : ℝ) * Sing (Fn F n)

/-- `C(F) = a_k (ρ_F(2)/2) 𝔖 ∏_{p>2} (1 + ρ_F(p)/(p(p-2)))`, p. 479. -/
noncomputable def CF (F : ℤ[X]) : ℝ :=
  (F.leadingCoeff : ℝ) * ((rhoF F 2 : ℝ) / 2) * SingConst *
    ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 + (rhoF F p : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)))

/-! ### Theorem 1 and Corollary 1, p. 478 -/

/-- **Theorem 1**, p. 478. Let `k ∈ ℕ`, `A, ε > 0`, `N^{1/(3k)+ε} ≤ H ≤ N^{1/k}`. Then
`Σ_{N^{1/k} ≤ n ≤ N^{1/k}+H} |R(F(n)) - F(n)𝔖(F(n))|² ≪_{A,ε,F} H N² L^{-A}`, `L = log N`. -/
def Theorem1 (F : ℤ[X]) : Prop :=
  Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (1 / (3 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F) →
    ∑ n ∈ nRange (N ^ (1 / deg F)) H, err F n ^ 2 ≤ C * H * N ^ 2 / Real.log N ^ A

/-- CITED. Theorem 1 of Perelli 1996, Section 2. -/
theorem theorem1 (F : ℤ[X]) : Theorem1 F := by sorry

/-- The `n` in the interval with `|R(F(n)) - F(n)𝔖(F(n))| > N L^{-A}`. -/
noncomputable def excCount (F : ℤ[X]) (N H A : ℝ) : ℕ :=
  ((nRange (N ^ (1 / deg F)) H).filter (fun n => N / Real.log N ^ A < |err F n|)).card

/-- **Corollary 1**, first part, p. 478: `R(F(n)) = F(n)𝔖(F(n)) + O(N L^{-A})` for all
`n ∈ [N^{1/k}, N^{1/k} + H]` but `O(H L^{-A})` exceptions; here the `O` in the error is `1`. -/
def Corollary1a (F : ℤ[X]) : Prop :=
  Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (1 / (3 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F) →
    (excCount F N H A : ℝ) ≤ C * H / Real.log N ^ A

/-- The even values `F(n)`, `n` in the interval, that are not a sum of two primes. -/
noncomputable def goldExc (F : ℤ[X]) (N H : ℝ) (lo : ℝ) : ℕ :=
  ((nRange lo H).filter (fun n : ℕ => (2 : ℤ) ∣ F.eval (n : ℤ) ∧ ¬ IsGoldbachSum (Fn F n))).card

/-- **Corollary 1**, second part, p. 478: if `ρ_F(2) ≠ 0`, for all `n ∈ A_F(N,H)` but
`O(H L^{-A})` exceptions, `F(n)` is a Goldbach number. -/
def Corollary1b (F : ℤ[X]) : Prop :=
  Admissible F → rhoF F 2 ≠ 0 → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (1 / (3 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F) →
    (goldExc F N H (N ^ (1 / deg F)) : ℝ) ≤ C * H / Real.log N ^ A

/-- CITED. Corollary 1, second part, "easily obtained" from Theorem 1, p. 478. -/
theorem corollary1b (F : ℤ[X]) : Corollary1b F := by sorry

/-- The remark of p. 478-479: localizing the primes as in Perelli-Pintz [7], the second
statement of Corollary 1 holds for `N^{7/(36k)+ε} ≤ H ≤ N^{1/k}`. -/
def Corollary1bShort (F : ℤ[X]) : Prop :=
  Admissible F → rhoF F 2 ≠ 0 → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (7 / (36 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F) →
    (goldExc F N H (N ^ (1 / deg F)) : ℝ) ≤ C * H / Real.log N ^ A

/-- CITED. A remark, p. 478-479, no proof in the paper. -/
theorem corollary1bShort (F : ℤ[X]) : Corollary1bShort F := by sorry

/-! ### Theorem 2 and Corollary 2, p. 479 -/

/-- **Theorem 2**, p. 479. For `N^{1/(6k)+ε} ≤ H ≤ N^{1/k-ε}`,
`Σ_{N^{1/k} ≤ n ≤ N^{1/k}+H} R(F(n)) = C(F) H N + O_{A,ε,F}(H N L^{-A})`. -/
def Theorem2 (F : ℤ[X]) : Prop :=
  Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (1 / (6 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F - ε) →
    |∑ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n) - CF F * H * N| ≤ C * H * N / Real.log N ^ A

/-- CITED. Theorem 2, Section 3, proof sketched. -/
theorem theorem2 (F : ℤ[X]) : Theorem2 F := by sorry

/-- **Corollary 2**, p. 479. If `ρ_F(2) ≠ 0` and `N^{1/(6k)+ε} ≤ H ≤ N^{1/k-ε}`, some
`n ∈ [N^{1/k}, N^{1/k}+H]` has `F(n)` a Goldbach number. -/
def Corollary2 (F : ℤ[X]) : Prop :=
  Admissible F → rhoF F 2 ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ (1 / (6 * deg F) + ε) ≤ H → H ≤ N ^ (1 / deg F - ε) →
    ∃ n ∈ nRange (N ^ (1 / deg F)) H, Even (Fn F n) ∧ IsGoldbachSum (Fn F n)

/-- CITED. Corollary 2, an easy consequence of Theorem 2, p. 479. -/
theorem corollary2 (F : ℤ[X]) : Corollary2 F := by sorry

/-! ### The Lemma, p. 482, a variant of Weyl's inequality -/

/-- `K(F,α) = Σ_{N^{1/k} ≤ n ≤ N^{1/k}+H} e(F(n)α)`, p. 480. -/
noncomputable def Kexp (F : ℤ[X]) (N H α : ℝ) : ℂ :=
  ∑ n ∈ nRange (N ^ (1 / deg F)) H, LeanLab.PerelliPintz1992.e (((F.eval (n : ℤ) : ℤ) : ℝ) * α)

/-- **Lemma**, p. 482. If `|α - a/q| ≤ 1/q²`, `(a,q) = 1`, then for any `D > 0`,
`K(F,α) ≪_{F,D} H (1/q + 1/H + q/H^k + L^{-2D+k²-2})^{1/K} L^{(D+1)/K}`, `K = 2^{k-1}`.
The range `1 ≤ H ≤ N^{1/k}` is the one of the proof. -/
def WeylLemma (F : ℤ[X]) : Prop :=
  Admissible F → ∀ D : ℝ, 0 < D → ∃ C : ℝ, ∀ N H α : ℝ, 2 ≤ N → 1 ≤ H → H ≤ N ^ (1 / deg F) →
    ∀ a q : ℕ, 1 ≤ q → Nat.Coprime a q → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
    ‖Kexp F N H α‖ ≤ C * H * (1 / q + 1 / H + q / H ^ deg F +
        Real.log N ^ (-2 * D + deg F ^ 2 - 2)) ^ (1 / (2 : ℝ) ^ (deg F - 1)) *
      Real.log N ^ ((D + 1) / (2 : ℝ) ^ (deg F - 1))

/-- CITED. The Lemma of p. 482, after Vaughan, Lemma 2.4. -/
theorem weylLemma (F : ℤ[X]) : WeylLemma F := by sorry

/-! ### PROVED: Corollary 1, first part, from Theorem 1 -/

theorem excCount_mul_le_of_sum {F : ℤ[X]} {N H A M : ℝ} (hN : 1 < N)
    (hsum : ∑ n ∈ nRange (N ^ (1 / deg F)) H, err F n ^ 2 ≤ M) :
    (excCount F N H A : ℝ) * (N / Real.log N ^ A) ^ 2 ≤ M := by
  have hL : 0 < Real.log N := Real.log_pos hN
  have hpos : 0 ≤ N / Real.log N ^ A := div_nonneg (by linarith) (Real.rpow_nonneg hL.le _)
  unfold excCount
  set T := (nRange (N ^ (1 / deg F)) H).filter (fun n => N / Real.log N ^ A < |err F n|)
  calc (T.card : ℝ) * (N / Real.log N ^ A) ^ 2 = ∑ _n ∈ T, (N / Real.log N ^ A) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ T, err F n ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := (Finset.mem_filter.mp hn).2
        have : (N / Real.log N ^ A) ^ 2 ≤ |err F n| ^ 2 := pow_le_pow_left₀ hpos hn'.le 2
        simpa [sq_abs] using this
    _ ≤ ∑ n ∈ nRange (N ^ (1 / deg F)) H, err F n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ M := hsum

/-- Corollary 1, first part, from Theorem 1 with `3A` in place of `A`. -/
theorem corollary1a_of_theorem1 {F : ℤ[X]} (h : Theorem1 F) : Corollary1a F := by
  intro hF A ε hA hε
  obtain ⟨C, N0, hC⟩ := h hF (3 * A) ε (by linarith) hε
  refine ⟨C, max N0 2, fun N H hN h1 h2 => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have key := excCount_mul_le_of_sum (A := A) (by linarith) (hC N H hN0 h1 h2)
  set a := Real.log N ^ A with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hL A
  have h3 : Real.log N ^ (3 * A) = a * a * a := by
    rw [ha, show 3 * A = A + A + A by ring, Real.rpow_add hL, Real.rpow_add hL]
  rw [h3] at key
  have hNpos : 0 < N := by linarith
  have hq : 0 < (N / a) ^ 2 := by positivity
  have e1 : C * H * N ^ 2 / (a * a * a) = (C * H / a) * (N / a) ^ 2 := by
    field_simp
  rw [e1] at key
  exact le_of_mul_le_mul_right key hq

/-- Corollary 1, first part, CONDITIONAL ON the cited Theorem 1. -/
theorem corollary1a (F : ℤ[X]) : Corollary1a F := corollary1a_of_theorem1 (theorem1 F)

/-- The exceptional count grows with `H`, monotonicity in `H`. -/
theorem excCount_mono {F : ℤ[X]} {N H H' A : ℝ} (hH : H ≤ H') :
    excCount F N H A ≤ excCount F N H' A := by
  unfold excCount nRange
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor (by linarith))⟩, hn.2⟩

theorem goldExc_mono {F : ℤ[X]} {N H H' lo : ℝ} (hH : H ≤ H') :
    goldExc F N H lo ≤ goldExc F N H' lo := by
  unfold goldExc nRange
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor (by linarith))⟩, hn.2⟩

/-! ### PROVED: the singular series and `ρ_F` -/

/-- `𝔖(n) = 0` for odd `n`: the factor at `p = 2` is `1 - 1/1² = 0`. -/
theorem Sing_odd {n : ℕ} (hn : Odd n) : Sing n = 0 := by
  unfold Sing
  apply tprod_of_exists_eq_zero
  refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
  have h2 : ¬ (2 ∣ n) := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hn
  simp [h2]
  norm_num

/-- `𝔖 > 0`, from the lab's `twinC_pos`. -/
theorem SingConst_pos : 0 < SingConst := by
  unfold SingConst; have := LeanLab.ChenExplicit.twinC_pos; linarith

/-- For `p > 2`, `(1 + 1/(p-1)) / (1 - 1/(p-1)²) = 1 + 1/(p-2)`, the step from `𝔖(F(n))` to
`𝔖 Σ_{d ∣ F(n)} f(d)` with `f(p) = 1/(p-2)`, p. 488. -/
theorem sing_factor {p : ℝ} (hp : 2 < p) :
    (1 + 1 / (p - 1)) / (1 - 1 / (p - 1) ^ 2) = 1 + 1 / (p - 2) := by
  have h1 : p - 1 ≠ 0 := by intro h; linarith
  have h2 : p - 2 ≠ 0 := by intro h; linarith
  have h3 : (1 - 1 / (p - 1) ^ 2) ≠ 0 := by
    rw [show 1 - 1 / (p - 1) ^ 2 = (p - 2) * p / (p - 1) ^ 2 by field_simp; ring]
    exact div_ne_zero (mul_ne_zero h2 (by intro h; linarith)) (pow_ne_zero 2 h1)
  rw [div_eq_iff h3]
  field_simp
  ring

theorem rhoF_le (F : ℤ[X]) (d : ℕ) : rhoF F d ≤ d := by
  unfold rhoF
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem rhoF_one (F : ℤ[X]) : rhoF F 1 = 1 := by
  unfold rhoF
  simp

theorem rhoF_two (F : ℤ[X]) :
    rhoF F 2 = (if (2 : ℤ) ∣ F.eval 0 then 1 else 0) + (if (2 : ℤ) ∣ F.eval 1 then 1 else 0) := by
  unfold rhoF
  rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- `F(n) mod 2` depends only on `n mod 2`. -/
theorem two_dvd_eval_iff (F : ℤ[X]) (n : ℤ) :
    (2 : ℤ) ∣ F.eval n ↔ (2 : ℤ) ∣ F.eval (n % 2) := by
  have h : (2 : ℤ) ∣ F.eval n - F.eval (n % 2) := by
    refine dvd_trans ?_ (Polynomial.sub_dvd_eval_sub n (n % 2) F)
    exact ⟨n / 2, by omega⟩
  constructor
  · intro h1; simpa using dvd_sub h1 h
  · intro h1; simpa using dvd_add h1 h

/-- Two consecutive integers carry exactly `ρ_F(2)` even values of `F`. -/
theorem pair_count (F : ℤ[X]) (n : ℕ) :
    (if (2 : ℤ) ∣ F.eval (n : ℤ) then 1 else 0) +
      (if (2 : ℤ) ∣ F.eval ((n + 1 : ℕ) : ℤ) then 1 else 0) = rhoF F 2 := by
  rw [rhoF_two]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have e1 : ((n : ℤ) % 2) = 0 := by omega
    have e2 : (((n + 1 : ℕ) : ℤ) % 2) = 1 := by omega
    have h1 : (2 : ℤ) ∣ F.eval (n : ℤ) ↔ (2 : ℤ) ∣ F.eval 0 := by
      rw [two_dvd_eval_iff F, e1]
    have h2 : (2 : ℤ) ∣ F.eval ((n + 1 : ℕ) : ℤ) ↔ (2 : ℤ) ∣ F.eval 1 := by
      rw [two_dvd_eval_iff F, e2]
    simp only [h1, h2]
  · have e1 : ((n : ℤ) % 2) = 1 := by omega
    have e2 : (((n + 1 : ℕ) : ℤ) % 2) = 0 := by omega
    have h1 : (2 : ℤ) ∣ F.eval (n : ℤ) ↔ (2 : ℤ) ∣ F.eval 1 := by
      rw [two_dvd_eval_iff F, e1]
    have h2 : (2 : ℤ) ∣ F.eval ((n + 1 : ℕ) : ℤ) ↔ (2 : ℤ) ∣ F.eval 0 := by
      rw [two_dvd_eval_iff F, e2]
    simp only [h1, h2]; ring

/-- `A_F` on `2m` consecutive integers has exactly `ρ_F(2) m` elements. -/
theorem card_AF_even (F : ℤ[X]) (a m : ℕ) :
    ((Finset.Ico a (a + 2 * m)).filter (fun n : ℕ => (2 : ℤ) ∣ F.eval (n : ℤ))).card =
      rhoF F 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [show a + 2 * (m + 1) = (a + 2 * m + 1) + 1 by ring,
      Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega), ih, add_assoc,
      pair_count F (a + 2 * m)]
    ring

/-- `|A_F(N,H)| = ρ_F(2) H/2 + O(1)`, p. 478, on `ℓ` consecutive integers:
`2|A_F|` is within `2` of `ρ_F(2) ℓ`. -/
theorem card_AF_bounds (F : ℤ[X]) (a ℓ : ℕ) :
    rhoF F 2 * ℓ ≤ 2 * ((Finset.Ico a (a + ℓ)).filter (fun n : ℕ => (2 : ℤ) ∣ F.eval (n : ℤ))).card + 2 ∧
    2 * ((Finset.Ico a (a + ℓ)).filter (fun n : ℕ => (2 : ℤ) ∣ F.eval (n : ℤ))).card ≤
      rhoF F 2 * ℓ + 2 := by
  have hr := rhoF_le F 2
  rcases Nat.even_or_odd' ℓ with ⟨m, rfl | rfl⟩
  · rw [card_AF_even]; constructor <;> nlinarith
  · have hc := card_AF_even F a m
    rw [Finset.card_filter] at hc ⊢
    rw [show a + (2 * m + 1) = (a + 2 * m) + 1 by ring,
      Finset.sum_Ico_succ_top (by omega), hc]
    split_ifs <;> constructor <;> nlinarith

/-! ### PROVED: Corollary 1 for `F = 2x^k` gives Perelli's (5.4) of Pintz 2021 -/

/-- `F = 2x^k`. -/
noncomputable def F2 (k : ℕ) : ℤ[X] := C 2 * X ^ k

theorem F2_natDegree (k : ℕ) : (F2 k).natDegree = k := natDegree_C_mul_X_pow k 2 (by norm_num)

theorem F2_leadingCoeff (k : ℕ) : (F2 k).leadingCoeff = 2 := by
  unfold F2; rw [leadingCoeff_C_mul_X_pow]

theorem F2_admissible {k : ℕ} (hk : 1 ≤ k) : Admissible (F2 k) :=
  ⟨by rw [F2_natDegree]; exact hk, by rw [F2_leadingCoeff]; norm_num⟩

theorem F2_eval (k n : ℕ) : (F2 k).eval (n : ℤ) = 2 * (n : ℤ) ^ k := by
  simp [F2]

theorem F2_Fn (k n : ℕ) : Fn (F2 k) n = 2 * n ^ k := by
  unfold Fn; rw [F2_eval]
  have : (2 : ℤ) * (n : ℤ) ^ k = ((2 * n ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

theorem F2_rho (k : ℕ) : rhoF (F2 k) 2 = 2 := by
  rw [rhoF_two]
  have h0 : (2 : ℤ) ∣ (F2 k).eval 0 := by simp [F2]
  have h1 : (2 : ℤ) ∣ (F2 k).eval 1 := by simp [F2]
  simp [h0, h1]

/-- `n ≤ N` with `2n^k` not a sum of two primes, counted on `[a, b]`. -/
noncomputable def badCount (k a b : ℕ) : ℕ :=
  ((Finset.Icc a b).filter (fun n => ¬ IsGoldbachSum (2 * n ^ k))).card

theorem EPoly_le_split (k X : ℕ) :
    EPoly k X ≤ EPoly k (X / 2) + badCount k (X / 2) (2 * (X / 2) + 1) := by
  unfold EPoly badCount
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hn ⊢
  by_cases h : n ≤ X / 2
  · left; exact ⟨⟨hn.1.1, h⟩, hn.2⟩
  · right; exact ⟨⟨by omega, by omega⟩, hn.2⟩

/-- A dyadic log power saving for `2n^k`. -/
def DyadicLog (k : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C M0 : ℝ, ∀ M : ℕ, M0 ≤ M →
    (badCount k M (2 * M + 1) : ℝ) ≤ C * M / Real.log M ^ A

/-- From dyadic blocks to `E_k(N) ≪ N (log N)^{-A}`, by strong induction on `N`. -/
theorem polyLog_of_dyadic {k : ℕ} (hD : DyadicLog k) : PolyLogPowerSaving k := by
  intro A hA
  obtain ⟨C, M0, hC⟩ := hD A hA
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set t : ℝ := (4 / 3 : ℝ) ^ (1 / A) with ht
  have ht1 : 1 < t := Real.one_lt_rpow (by norm_num) (by positivity)
  have htA : t ^ A = 4 / 3 := by
    rw [ht, ← Real.rpow_mul (by norm_num), show 1 / A * A = 1 by field_simp, Real.rpow_one]
  set l0 : ℝ := Real.log 3 / (t - 1) with hl0
  set Ymin : ℕ := ⌈max M0 (max 2 (Real.exp l0))⌉₊ with hYmin
  have hYmin_ge : max M0 (max 2 (Real.exp l0)) ≤ Ymin := Nat.le_ceil _
  set X1 : ℕ := 2 * Ymin + 2 with hX1
  set K : ℝ := max (2 * C') (Real.log X1 ^ A) with hK
  have hK0 : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  have claim : ∀ X : ℕ, 2 ≤ X → (EPoly k X : ℝ) ≤ K * X / Real.log X ^ A := by
    intro X
    induction X using Nat.strong_induction_on with
    | _ X ih =>
      intro hX2
      have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
      have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
      have hlx : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
      by_cases hsmall : X < X1
      · have hE : (EPoly k X : ℝ) ≤ X := by exact_mod_cast EPoly_le k X
        have hlog : Real.log X ≤ Real.log X1 :=
          Real.log_le_log (by linarith) (by exact_mod_cast hsmall.le)
        have hpow : Real.log X ^ A ≤ K :=
          le_trans (Real.rpow_le_rpow hlogX.le hlog hA.le) (le_max_right _ _)
        rw [le_div_iff₀ hlx]
        calc (EPoly k X : ℝ) * Real.log X ^ A ≤ X * K :=
              mul_le_mul hE hpow hlx.le (by linarith)
          _ = K * X := by ring
      · push Not at hsmall
        set Y := X / 2 with hY
        have hYge : Ymin ≤ Y := by omega
        have hYr : (Ymin : ℝ) ≤ Y := by exact_mod_cast hYge
        have hY2 : (2 : ℝ) ≤ Y := by
          have : (2 : ℝ) ≤ max M0 (max 2 (Real.exp l0)) :=
            le_trans (le_max_left 2 (Real.exp l0)) (le_max_right M0 _)
          linarith
        have hYM0 : M0 ≤ Y := by have := le_max_left M0 (max 2 (Real.exp l0)); linarith
        have hYexp : Real.exp l0 ≤ Y := by
          have : Real.exp l0 ≤ max M0 (max 2 (Real.exp l0)) :=
            le_trans (le_max_right 2 (Real.exp l0)) (le_max_right M0 _)
          linarith
        have hYpos : (0 : ℝ) < Y := by linarith
        have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
        have hly : 0 < Real.log Y ^ A := Real.rpow_pos_of_pos hlogY A
        have hYlt : Y < X := by omega
        have ihY := ih Y hYlt (by exact_mod_cast hY2)
        have hDY := hC Y hYM0
        have hDY' : (badCount k Y (2 * Y + 1) : ℝ) ≤ C' * Y / Real.log Y ^ A := by
          refine hDY.trans ?_
          gcongr
          exact le_max_left _ _
        have hsplit : (EPoly k X : ℝ) ≤ EPoly k Y + badCount k Y (2 * Y + 1) := by
          exact_mod_cast EPoly_le_split k X
        -- the logs
        have hl0Y : l0 ≤ Real.log Y := by
          rw [Real.le_log_iff_exp_le hYpos]; exact hYexp
        have hXle : (X : ℝ) ≤ 3 * Y := by
          have : X ≤ 2 * Y + 1 := by omega
          have : (X : ℝ) ≤ 2 * Y + 1 := by exact_mod_cast this
          linarith
        have hXge : 2 * (Y : ℝ) ≤ X := by
          have : 2 * Y ≤ X := by omega
          exact_mod_cast this
        have hlogXle : Real.log X ≤ t * Real.log Y := by
          have h1 : Real.log X ≤ Real.log (3 * Y) := Real.log_le_log (by linarith) hXle
          rw [Real.log_mul (by norm_num) hYpos.ne'] at h1
          have h2 : Real.log 3 ≤ (t - 1) * Real.log Y := by
            rw [hl0, div_le_iff₀ (by linarith)] at hl0Y; linarith
          linarith
        have hlxle : Real.log X ^ A ≤ 4 / 3 * Real.log Y ^ A := by
          calc Real.log X ^ A ≤ (t * Real.log Y) ^ A :=
                Real.rpow_le_rpow hlogX.le hlogXle hA.le
            _ = t ^ A * Real.log Y ^ A := Real.mul_rpow (by linarith) hlogY.le
            _ = 4 / 3 * Real.log Y ^ A := by rw [htA]
        have hCK : C' ≤ K / 2 := by have := le_max_left (2 * C') (Real.log X1 ^ A); linarith
        have hsum : (EPoly k X : ℝ) ≤ (3 / 2 * K) * Y / Real.log Y ^ A := by
          calc (EPoly k X : ℝ) ≤ K * Y / Real.log Y ^ A + C' * Y / Real.log Y ^ A :=
                hsplit.trans (add_le_add ihY hDY')
            _ = (K + C') * Y / Real.log Y ^ A := by ring
            _ ≤ (3 / 2 * K) * Y / Real.log Y ^ A := by gcongr; linarith
        refine hsum.trans ?_
        rw [div_le_div_iff₀ hly hlx]
        have hKY : 0 ≤ K * (Y : ℝ) := mul_nonneg hK0 hYpos.le
        nlinarith [mul_le_mul_of_nonneg_left hlxle hKY, mul_le_mul_of_nonneg_left hXge
          (mul_nonneg hK0 hly.le)]
  exact ⟨K, fun N hN => claim N hN⟩

/-- `(log M)^A ≤ M` for large `M`. -/
theorem log_rpow_le_self (A : ℝ) : ∃ Y0 : ℝ, ∀ Y : ℝ, Y0 ≤ Y → Real.log Y ^ A ≤ Y := by
  have h := (isLittleO_log_rpow_rpow_atTop A (one_pos)).bound one_pos
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.mp h
  refine ⟨max Y0 1, fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  have := hY0 Y (le_trans (le_max_left _ _) hY)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hY1) _),
    Real.norm_of_nonneg (by positivity), Real.rpow_one, one_mul] at this
  exact this

/-- Corollary 1, second part, for `F = 2x^k` gives the dyadic saving. -/
theorem dyadic_of_corollary1b {k : ℕ} (hk : 1 ≤ k) (h : Corollary1b (F2 k)) : DyadicLog k := by
  intro A hA
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, N0, hC⟩ := h (F2_admissible hk) (by rw [F2_rho]; norm_num) A (1 / (3 * k))
    hA (by positivity)
  obtain ⟨Y0, hY0⟩ := log_rpow_le_self A
  set C' := max C 0
  refine ⟨C' + 1, max (max N0 2) Y0, fun M hM => ?_⟩
  have hM2 : (2 : ℝ) ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hM)
  have hMN0 : N0 ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hM)
  have hMY0 : Y0 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hdeg : deg (F2 k) = k := by unfold deg; rw [F2_natDegree]
  set N : ℝ := (M : ℝ) ^ k with hN
  have hroot : N ^ (1 / deg (F2 k)) = M := by
    rw [hdeg, hN, one_div]; exact Real.pow_rpow_inv_natCast hMpos.le (by omega)
  have hNM : (M : ℝ) ≤ N := le_self_pow₀ (by linarith) (by omega)
  have hlow : N ^ (1 / (3 * deg (F2 k)) + 1 / (3 * k)) ≤ M := by
    rw [hdeg, hN, ← Real.rpow_natCast, ← Real.rpow_mul hMpos.le]
    have : (k : ℝ) * (1 / (3 * k) + 1 / (3 * k)) = 2 / 3 := by field_simp; ring
    rw [this]
    calc (M : ℝ) ^ (2 / 3 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = M := Real.rpow_one _
  have hc := hC N M (le_trans hMN0 hNM) hlow (le_of_eq hroot.symm)
  rw [hroot] at hc
  -- the count on `[M, 2M]`
  have hset : goldExc (F2 k) N M M = badCount k M (2 * M) := by
    unfold goldExc badCount nRange
    have h1 : ⌈(M : ℝ)⌉₊ = M := Nat.ceil_natCast M
    have h2 : ⌊(M : ℝ) + M⌋₊ = 2 * M := by
      rw [show (M : ℝ) + M = ((2 * M : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    rw [h1, h2]
    congr 1
    apply Finset.filter_congr
    intro n _
    rw [F2_Fn, F2_eval]
    simp
  rw [hset] at hc
  have hsplit : badCount k M (2 * M + 1) ≤ badCount k M (2 * M) + 1 := by
    unfold badCount
    refine (Finset.card_le_card (s := (Finset.Icc M (2 * M + 1)).filter _)
      (t := insert (2 * M + 1) ((Finset.Icc M (2 * M)).filter
        (fun n => ¬ IsGoldbachSum (2 * n ^ k)))) ?_).trans (Finset.card_insert_le _ _)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert] at hn ⊢
    by_cases hn1 : n = 2 * M + 1
    · left; exact hn1
    · right; exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hlogN : Real.log N = k * Real.log M := by rw [hN, Real.log_pow]
  have hLN : Real.log M ^ A ≤ Real.log N ^ A := by
    rw [hlogN]
    exact Real.rpow_le_rpow hlogM.le (by nlinarith) hA.le
  have hlMA : 0 < Real.log M ^ A := Real.rpow_pos_of_pos hlogM A
  have hc' : (badCount k M (2 * M) : ℝ) ≤ C' * M / Real.log M ^ A := by
    refine hc.trans ?_
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    calc C * M / Real.log N ^ A ≤ C' * M / Real.log N ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hMpos.le)
            (Real.rpow_nonneg hlogN0 _)
      _ ≤ C' * M / Real.log M ^ A := by
          apply div_le_div_of_nonneg_left (by positivity) hlMA hLN
  have hone : (1 : ℝ) ≤ M / Real.log M ^ A := by
    rw [le_div_iff₀ hlMA, one_mul]; exact hY0 M hMY0
  have hsplitR : (badCount k M (2 * M + 1) : ℝ) ≤ badCount k M (2 * M) + 1 := by
    exact_mod_cast hsplit
  calc (badCount k M (2 * M + 1) : ℝ) ≤ C' * M / Real.log M ^ A + M / Real.log M ^ A := by
        linarith
    _ = (C' + 1) * M / Real.log M ^ A := by ring

/-- **Corollary 1 for `2x^k` gives Perelli's (5.4) in Pintz 2021**: `E_k(N) ≪ N (log N)^{-A}`. -/
theorem polyLog_of_corollary1b {k : ℕ} (hk : 1 ≤ k) (h : Corollary1b (F2 k)) :
    PolyLogPowerSaving k :=
  polyLog_of_dyadic (dyadic_of_corollary1b hk h)

/-- (5.4) of Pintz 2021 for every `k ≥ 1`, CONDITIONAL ON the cited Corollary 1. -/
theorem perelli54 {k : ℕ} (hk : 1 ≤ k) : PolyLogPowerSaving k :=
  polyLog_of_corollary1b hk (corollary1b (F2 k))

/-! ### PROVED: exponent arithmetic of Sections 2 and 3 -/

/-- (9), p. 482: with `D = B/8 + k²/2 - 1`, the term `L^{-2D+k²-2}` of the Lemma gives
`L^{(-2D+k²-2)/K} L^{(D+1)/K} = L^{-(B-4k²)/(8K)}`. -/
theorem exp9_log {B k K D : ℝ} (hK : K ≠ 0) (hD : D = B / 8 + k ^ 2 / 2 - 1) :
    (-2 * D + k ^ 2 - 2) / K + (D + 1) / K = -(B - 4 * k ^ 2) / (8 * K) := by
  subst hD; field_simp; ring

/-- (9): the term `1/q` with `q > L^{B/4}` gives the same exponent. -/
theorem exp9_q {B k K D : ℝ} (hK : K ≠ 0) (hD : D = B / 8 + k ^ 2 / 2 - 1) :
    -(B / 4) / K + (D + 1) / K = -(B - 4 * k ^ 2) / (8 * K) := by
  subst hD; field_simp; ring

/-- (10), p. 482: `N L · H L^{-(B-4k²)/(8K)} · N L = H N² L^{-(B-4k²-16K)/(8K)}`. -/
theorem exp10 (B k K : ℝ) (hK : K ≠ 0) :
    1 + 1 - (B - 4 * k ^ 2) / (8 * K) = -(B - 4 * k ^ 2 - 16 * K) / (8 * K) := by
  field_simp; ring

/-- (13), p. 483: `Q = Q̄^{1/2}/2` gives `1/Q² = 4/Q̄`. -/
theorem exp13 {Qbar : ℝ} (hQ : 0 < Qbar) : 1 / (Real.sqrt Qbar / 2) ^ 2 = 4 / Qbar := by
  rw [div_pow, Real.sq_sqrt hQ.le]; field_simp; norm_num

/-- With `H = N^{1/(3k)+ε}`, `Q ≈ H^{k/2} = N^{1/6+kε/2}` and `N/Q = N^{5/6-kε/2}`, the base
in (25), p. 485. -/
theorem exp25_base {k ε : ℝ} (hk : k ≠ 0) : 1 - k * (1 / (3 * k) + ε) / 2 = 5 / 6 - k * ε / 2 := by
  field_simp; ring

/-- (25): `N^{2σ-1} N^{12(5/6-kε/2)(1-σ)/5} = N^{1 - (6kε/5)(1-σ)}`. -/
theorem exp25 (k ε σ : ℝ) :
    2 * σ - 1 + 12 * (5 / 6 - k * ε / 2) * (1 - σ) / 5 = 1 - 6 * k * ε / 5 * (1 - σ) := by
  ring

/-- (25): at `1 - σ = 10(B/ε) log L / L`, `N^{-(6kε/5)(1-σ)} = L^{-12kB}`, `L = log N`. -/
theorem exp25_value {N B ε k : ℝ} (hN : 1 < N) (hε : ε ≠ 0) :
    N ^ (-(6 * k * ε / 5) * (10 * (B / ε) * Real.log (Real.log N) / Real.log N)) =
      Real.log N ^ (-(12 * k * B)) := by
  have hL : 0 < Real.log N := Real.log_pos hN
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hL]
  congr 1
  field_simp
  ring

/-- The Huxley threshold of Theorem 1: the density exponent `12/5` on `N^{1-kθ/2}` is at most
`2` exactly when `θ ≥ 1/(3k)`. -/
theorem huxley_threshold1 {k θ : ℝ} (hk : 0 < k) :
    12 / 5 * (1 - k * θ / 2) ≤ 2 ↔ 1 / (3 * k) ≤ θ := by
  rw [div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The Huxley threshold of Theorem 2, `Q = H^k L^{-B}`: `θ ≥ 1/(6k)`. -/
theorem huxley_threshold2 {k θ : ℝ} (hk : 0 < k) :
    12 / 5 * (1 - k * θ) ≤ 2 ↔ 1 / (6 * k) ≤ θ := by
  rw [div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- (26), p. 486: with `D = (B+k²)/2 - 1`, `-2D+k²-2 = -B`, the `1/q`, `q > L^B`, term gives
`L^{-(B-k²)/(2K)}`, and `N L · H L^{-(B-k²)/(2K)} = H N L^{-(B-k²-2K)/(2K)}`. -/
theorem exp26 {B k K D : ℝ} (hK : K ≠ 0) (hD : D = (B + k ^ 2) / 2 - 1) :
    (-2 * D + k ^ 2 - 2 = -B) ∧ (-B / K + (D + 1) / K = -(B - k ^ 2) / (2 * K)) ∧
      (1 - (B - k ^ 2) / (2 * K) = -(B - k ^ 2 - 2 * K) / (2 * K)) := by
  subst hD
  refine ⟨by ring, by field_simp; ring, by field_simp; ring⟩

/-- (32), p. 487: `H ≥ N^{1/(6k)+ε}` gives `H^k ≥ N^{1/6+kε}` and `1/6 + kε ≥ 1/6 + ε`. -/
theorem exp32 {k ε : ℝ} (hk : 1 ≤ k) (hε : 0 ≤ ε) :
    k * (1 / (6 * k) + ε) = 1 / 6 + k * ε ∧ 1 / 6 + ε ≤ 1 / 6 + k * ε := by
  constructor
  · field_simp
  · nlinarith

/-- The three lower exponents: `1/(6k) < 7/(36k) < 1/(3k)`, Theorem 2, the remark, Theorem 1. -/
theorem ranges_order {k : ℝ} (hk : 0 < k) :
    1 / (6 * k) < 7 / (36 * k) ∧ 7 / (36 * k) < 1 / (3 * k) := by
  constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> nlinarith

/-- The ranges are not empty: Theorem 1 needs `ε ≤ 2/(3k)`, Theorem 2 needs `ε ≤ 5/(12k)`. -/
theorem ranges_nonempty {k ε : ℝ} (hk : 0 < k) :
    (1 / (3 * k) + ε ≤ 1 / k ↔ ε ≤ 2 / (3 * k)) ∧
      (1 / (6 * k) + ε ≤ 1 / k - ε ↔ ε ≤ 5 / (12 * k)) := by
  have e1 : 1 / k - 1 / (3 * k) = 2 / (3 * k) := by field_simp; ring
  have e2 : (1 / k - 1 / (6 * k)) / 2 = 5 / (12 * k) := by field_simp; ring
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- QUESTION, PRELIMINARY, (22) p. 485: (21) with `q ≤ Q ≈ N^{1/6+kε/2}`, `T = N` from (18),
`1 - σ ≤ 10(B/ε) log L / L` gives the power `(7/6)(12/5)·10 = 28` of `L^{B/ε}`, not `25`;
with `qT ≤ N^{5/6}` it would be `20`. The slip is harmless: `2·28 = 56 < 100`, the power
`1/(2ε') = 100B/ε` of (20). -/
theorem exp22_question :
    (7 / 6 : ℝ) * (12 / 5) * 10 = 28 ∧ (25 : ℝ) < 28 ∧ (5 / 6 : ℝ) * (12 / 5) * 10 = 20 ∧
      2 * (28 : ℝ) < 100 ∧ (1 : ℝ) / (2 * (1 / 200)) = 100 := by
  norm_num

/-! ### PROVED: links to the lab -/

/-- Binary Goldbach makes the exceptional count of Corollary 1 for `2x^k` vanish once
`N^{1/k} ≥ 2`. -/
theorem goldExc_F2_eq_zero_of_binaryGoldbach (h : BinaryGoldbach) {k : ℕ} (hk : 1 ≤ k)
    {N H lo : ℝ} (hlo : 2 ≤ lo) : goldExc (F2 k) N H lo = 0 := by
  unfold goldExc nRange
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨_, hng⟩
  simp only [Finset.mem_Icc] at hn
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ n := le_trans hlo (Nat.ceil_le.mp hn.1)
    exact_mod_cast this
  rw [F2_Fn] at hng
  have hpow : 2 ≤ n ^ k :=
    le_trans hn2 (by simpa using Nat.pow_le_pow_right (by omega : 0 < n) hk)
  exact hng (h _ (even_two_mul _) (by omega))

/-- Pintz 2021's `perelli_two_of_theorem5` gave (5.4) at `k = 2` from Theorem 5; Perelli's
Corollary 1 gives it at every `k`, and both agree at `k = 2`. -/
theorem perelli54_two_both (h5 : LeanLab.ExceptionalSet.Pintz2021.Theorem5)
    (h1 : Corollary1b (F2 2)) : PolyLogPowerSaving 2 ∧ PolyLogPowerSaving 2 :=
  ⟨LeanLab.ExceptionalSet.Pintz2021.perelli_two_of_theorem5 h5,
    polyLog_of_corollary1b (by norm_num) h1⟩

end LeanLab.Perelli1996.EncA

open LeanLab.Perelli1996.EncA in
section
#print axioms excCount_mul_le_of_sum
#print axioms corollary1a_of_theorem1
#print axioms corollary1a
#print axioms excCount_mono
#print axioms goldExc_mono
#print axioms Sing_odd
#print axioms SingConst_pos
#print axioms sing_factor
#print axioms rhoF_le
#print axioms rhoF_one
#print axioms rhoF_two
#print axioms two_dvd_eval_iff
#print axioms pair_count
#print axioms card_AF_even
#print axioms card_AF_bounds
#print axioms F2_natDegree
#print axioms F2_leadingCoeff
#print axioms F2_admissible
#print axioms F2_eval
#print axioms F2_Fn
#print axioms F2_rho
#print axioms EPoly_le_split
#print axioms polyLog_of_dyadic
#print axioms log_rpow_le_self
#print axioms dyadic_of_corollary1b
#print axioms polyLog_of_corollary1b
#print axioms perelli54
#print axioms exp9_log
#print axioms exp9_q
#print axioms exp10
#print axioms exp13
#print axioms exp25_base
#print axioms exp25
#print axioms exp25_value
#print axioms huxley_threshold1
#print axioms huxley_threshold2
#print axioms exp26
#print axioms exp32
#print axioms ranges_order
#print axioms ranges_nonempty
#print axioms exp22_question
#print axioms goldExc_F2_eq_zero_of_binaryGoldbach
#print axioms perelli54_two_both
end
