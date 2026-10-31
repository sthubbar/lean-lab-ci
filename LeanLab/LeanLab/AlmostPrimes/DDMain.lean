/-
AI-written Lean code, Claude, 2026-10-21, run 20261020T2303Z-14596, unit U-1304.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
re-read this run on arxiv.org/html/2602.22720, v4. Theorem 3.3 and Theorem 1.2 assembled.

The sieve objects of Section 1 for the sequence `aₙ` of Section 2, all primes sifted:
`Sc N z` is `S(A, z)`, `Xc N = N - 1` is `X = |A|`, `V N z` is `V(z)`, `rd N s` is `r_d(A)` for
`d = ∏ s`, `R4 N z D` is `R₄(A, D) = Σ_{d ∣ P(z), d < D} τ₄(d) |r_d(A)|`, a squarefree `d ∣ P(z)`
being a set `s` of primes below `z` with `τ₄(d) = 4^{|s|}`.

Inputs, each a named `Prop`, every one cited and none proved here:
* `GapTable1476`: Oliveira e Silva, Herzog, Pardi, the prime gap bound used by Lemma 3.1.
* `VerifySScript`: the paper's verifyS.jl check, Theorem 3.3 Case 2, `S(A, N^{1/20}) > 0` for
  `4 · 10^18 < N < 10^200`.
* `DDLemma21All.RSHyp`: Rosser-Schoenfeld Theorem 5 in the form Lemma 2.1 Case 1 uses.
* `RSRecip`: Rosser-Schoenfeld (3.20), `Σ_{p < z} 1/p < log log z + 0.2634` for `z ≥ 10^10`,
  used by Lemmas 2.2 and 2.3; it is the paper's `log log z - 0.2366` over odd primes.
* `NathansonRd`: `|r_d(A)| ≤ τ(d) = 2^{ω(d)}`, proof of Nathanson's Theorem 7.2.
* `SelbergThm13`: Theorem 1.3, Friedlander-Iwaniec Theorem 7.7, for this sequence, `κ = 2`.
PROVED here from them: Lemma 2.1 for real `w`, the adapter `dimCond_of_RS`; Lemma 2.2,
`lemma2_2_of`, from `RSRecip` only; Lemma 2.3 in its `R₄` form, `lemma2_3_of`; Case 3,
`sifted_large`; `theorem3_3_large` for `N ≥ 10^200` without the gap table or the script; and
`theorem3_3`, `theorem1_2` for every `N ≥ 2`. Vacuity checks at the end. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDCase2
import LeanLab.AlmostPrimes.DDCase3
import LeanLab.AlmostPrimes.DDConst
import LeanLab.AlmostPrimes.RSLogSum

open Real Finset
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21

noncomputable section
namespace LeanLab.AlmostPrimes.DDMain

/-! ### The sieve objects -/

/-- `X = |A| = N - 1`. -/
def Xc (N : ℕ) : ℝ := ((N - 1 : ℕ) : ℝ)

/-- `S(A, z)`: the `1 ≤ n ≤ N - 1` with no prime `p < z` dividing `aₙ`. -/
def Sc (N : ℕ) (z : ℝ) : ℕ :=
  ((Icc 1 (N - 1)).filter (fun n => ∀ p ∈ primesIn 2 z, ¬ p ∣ Campbell2026.aSeq N n)).card

/-- `g(d)` for `d = ∏ s`. -/
def gd (N : ℕ) (s : Finset ℕ) : ℝ := ∏ p ∈ s, g N p

/-- `|A_d|`. -/
def Ad (N d : ℕ) : ℕ := ((Icc 1 (N - 1)).filter (fun n => d ∣ Campbell2026.aSeq N n)).card

/-- `r_d(A) = |A_d| - X g(d)` for `d = ∏ s`. -/
def rd (N : ℕ) (s : Finset ℕ) : ℝ := (Ad N (∏ p ∈ s, p) : ℝ) - Xc N * gd N s

/-- `R₄(A, D) = Σ_{d ∣ P(z), d < D} τ₄(d) |r_d(A)|`. -/
def R4 (N : ℕ) (z D : ℝ) : ℝ :=
  ∑ s ∈ (primesIn 2 z).powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < D),
    (4 : ℝ) ^ s.card * |rd N s|

/-- `V(z) = ∏_{p < z} (1 - g(p))`. -/
def V (N : ℕ) (z : ℝ) : ℝ := ∏ p ∈ primesIn 2 z, (1 - g N p)

/-- The factor `1 - (s+3)/(2e^k) (2ek/(s-3))^{(s-3)/2}` of Theorem 1.3. -/
def Fsk (s k : ℝ) : ℝ := 1 - (s + 3) / (2 * exp k) * (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2)

/-- Condition (2) with `κ = 2`, for all real `z > w ≥ 2`. -/
def DimCond (N : ℕ) (K : ℝ) : Prop := ∀ w z : ℝ, 2 ≤ w → w < z →
  ∏ p ∈ primesIn w z, (1 - g N p)⁻¹ ≤ K * (log z / log w) ^ 2

/-! ### The cited inputs -/

/-- **Theorem 1.3**, Friedlander-Iwaniec Theorem 7.7, the `Λ⁻Λ²` lower bound sieve, for this
sequence: with `s = log D / log z`, `k = 2 + log K` and `s ≥ 2k + 3`,
`S(A, z) ≥ X V(z) F(s, k) - 2 R₄(A, D)`. Cited. -/
def SelbergThm13 : Prop := ∀ N : ℕ, 2 ≤ N → ∀ z D K : ℝ, 2 ≤ z → 1 ≤ K → DimCond N K →
  2 * (2 + log K) + 3 ≤ log D / log z →
  Xc N * V N z * Fsk (log D / log z) (2 + log K) - 2 * R4 N z D ≤ (Sc N z : ℝ)

/-- Rosser-Schoenfeld 1962 (3.20) at `z ≥ 10^10`: `Σ_{p < z} 1/p < log log z + 0.2634`. Cited. -/
def RSRecip : Prop := ∀ z : ℝ, 10 ^ 10 ≤ z →
  ∑ p ∈ primesIn 2 z, (1 : ℝ) / p < log (log z) + 0.2634

/-- Nathanson, proof of Theorem 7.2: `|r_d(A)| ≤ 2^{ω(d)}` for squarefree `d`. Cited. -/
def NathansonRd : Prop := ∀ (N : ℕ) (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
  |rd N s| ≤ (2 : ℝ) ^ s.card

/-- Theorem 3.3 Case 2, the paper's verifyS.jl computation. Cited. -/
def VerifySScript : Prop := ∀ N : ℕ, 4 * 10 ^ 18 < N → (N : ℝ) < 10 ^ 200 →
  Campbell2026.SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ)))

/-! ### Lemma 2.1 for real `w`: the adapter -/

/-- **Lemma 2.1 with `K = 3` for every real `z > w ≥ 2`**, condition (2) as Theorem 1.3 takes it.
CONDITIONAL ON `RSHyp` only. From `DDCase2.lemma2_1_of_RS`, integer `w`, at `⌈w⌉`. -/
theorem dimCond_of_RS (hRS : DDLemma21All.RSHyp) (N : ℕ) : DimCond N 3 := by
  intro w z hw hwz
  set m := ⌈w⌉₊ with hm
  have hwm : w ≤ (m : ℝ) := Nat.le_ceil w
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := le_trans hw hwm
    exact_mod_cast this
  have hset : primesIn w z = primesIn (m : ℝ) z := by
    ext p
    simp only [primesIn, mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have : m ≤ p := Nat.ceil_le.mpr h3
      exact ⟨h1, h2, by exact_mod_cast this, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, le_trans hwm h3, h4⟩
  have hlw : 0 < log w := log_pos (by linarith)
  have hlm : log w ≤ log (m : ℝ) := log_le_log (by linarith) hwm
  have hlz : log w < log z := log_lt_log (by linarith) hwz
  rw [hset]
  by_cases hmz : (m : ℝ) < z
  · have h := DDCase2.lemma2_1_of_RS N hRS m hm2 z hmz
    have : (log z / log (m : ℝ)) ^ 2 ≤ (log z / log w) ^ 2 := by
      apply pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith))
      exact div_le_div_of_nonneg_left (by linarith) hlw hlm
    linarith
  · push Not at hmz
    have he : primesIn (m : ℝ) z = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [primesIn, mem_filter] at hp
      linarith [hp.2.2.1, hp.2.2.2]
    rw [he, prod_empty]
    have : 1 ≤ log z / log w := by rw [le_div_iff₀ hlw]; linarith
    nlinarith

/-! ### Lemma 2.2 from `RSRecip` -/

/-- `Σ_{j < J} 1/((2j+3)(2j+1)) = 1/2 - 1/(2(2J+1))`. -/
lemma odd_tele (J : ℕ) :
    ∑ j ∈ range J, (1 : ℝ) / ((2 * j + 3) * (2 * j + 1)) = 1 / 2 - 1 / (2 * (2 * J + 1)) := by
  induction J with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- Over the odd primes below `z`, `Σ 1/(p(p-2)) ≤ 1/2`, by telescoping over odd `n ≥ 3`. -/
lemma sum_pp2_le (z : ℝ) : ∑ p ∈ primesIn 3 z, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 1 / 2 := by
  set S := primesIn 3 z with hS
  set H : ℕ → ℝ := fun j => (1 : ℝ) / ((2 * j + 3) * (2 * j + 1)) with hH
  have hodd : ∀ p ∈ S, p = 2 * ((p - 3) / 2) + 3 := by
    intro p hp
    simp only [hS, primesIn, mem_filter] at hp
    have h3 : (3 : ℝ) ≤ p := hp.2.2.1
    have h3' : 3 ≤ p := by exact_mod_cast h3
    rcases hp.2.1.eq_two_or_odd with h | h <;> omega
  have himg : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) =
      ∑ j ∈ S.image (fun p => (p - 3) / 2), H j := by
    rw [sum_image]
    · apply sum_congr rfl
      intro p hp
      obtain ⟨j, hj⟩ : ∃ j, p = 2 * j + 3 := ⟨_, hodd p hp⟩
      subst hj
      have e : (2 * j + 3 - 3) / 2 = j := by omega
      rw [e, hH]
      push_cast
      congr 1
      ring
    · intro x hx y hy hxy
      have := hodd x (Finset.mem_coe.mp hx)
      have := hodd y (Finset.mem_coe.mp hy)
      simp only at hxy
      omega
  have hsub : S.image (fun p => (p - 3) / 2) ⊆ range ⌈z⌉₊ := by
    intro j hj
    rw [mem_image] at hj
    obtain ⟨p, hp, rfl⟩ := hj
    simp only [hS, primesIn, mem_filter, mem_range] at hp ⊢
    omega
  rw [himg]
  calc ∑ j ∈ S.image (fun p => (p - 3) / 2), H j ≤ ∑ j ∈ range ⌈z⌉₊, H j :=
        sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by rw [hH]; positivity)
    _ = 1 / 2 - 1 / (2 * (2 * (⌈z⌉₊ : ℝ) + 1)) := odd_tele _
    _ ≤ 1 / 2 := by
        have : 0 ≤ 1 / (2 * (2 * (⌈z⌉₊ : ℝ) + 1)) := by positivity
        linarith

/-- **Dudek-Dunn Lemma 2.2**, `V(z) ≥ 0.2749 / log² z` for `z ≥ 10^10`. CONDITIONAL ON
`RSRecip` only. The odd prime sum `Σ 1/(p(p-2)) ≤ 1/2` replaces the paper's `0.5357`. -/
theorem lemma2_2_of (hRec : RSRecip) (N : ℕ) (z : ℝ) (hz : 10 ^ 10 ≤ z) :
    0.2749 / (log z) ^ 2 ≤ V N z := by
  rcases DDLemma21All.primesIn_two z with he | hz2
  swap; · linarith
  have hn : (2 : ℕ) ∉ primesIn 3 z := by
    simp only [primesIn, Finset.mem_filter]; intro h; norm_num at h
  have hR := hRec z hz
  rw [he, sum_insert hn] at hR
  unfold V
  rw [he, prod_insert hn]
  have hg : (1 - g N 2) = 1 / 2 := by unfold g; norm_num
  rw [hg]
  set S := primesIn 3 z with hS
  have h3 : ∀ p ∈ S, 3 ≤ p := fun p hp => by
    simp only [hS, primesIn, mem_filter] at hp
    exact_mod_cast hp.2.2.1
  have hfac : ∀ p ∈ S, exp (-(2 / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 2)))) ≤ 1 - g N p := by
    intro p hp
    have hp' : (3 : ℝ) ≤ p := by exact_mod_cast h3 p hp
    obtain ⟨hpos, hle⟩ := one_sub_g_pos N p (h3 p hp)
    calc exp (-(2 / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 2))))
        ≤ exp (log (1 - 2 / (p : ℝ))) := by
          apply exp_le_exp.mpr
          have := neg_log_one_sub_two_div hp'
          linarith
      _ = 1 - 2 / (p : ℝ) := exp_log hpos
      _ ≤ 1 - g N p := hle
  have hprod : ∏ p ∈ S, exp (-(2 / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
      ∏ p ∈ S, (1 - g N p) :=
    Finset.prod_le_prod₀ (fun p _ => (exp_pos _).le) hfac
  rw [← Real.exp_sum, Finset.sum_neg_distrib, Finset.sum_add_distrib] at hprod
  have hsum1 : ∑ p ∈ S, 2 / (p : ℝ) = 2 * ∑ p ∈ S, (1 : ℝ) / p := by
    rw [Finset.mul_sum]; congr 1; ext p; ring
  have hsum2 : ∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 2)) =
      2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
    rw [Finset.mul_sum]; congr 1; ext p; ring
  rw [hsum1, hsum2] at hprod
  have hpp : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 1 / 2 := sum_pp2_le z
  have hz1 : (1 : ℝ) < z := by linarith
  have hL : 0 < log z := log_pos hz1
  set L := log z with hLdef
  -- the exponent is at least `0.4732 - 1 - 2 log L`
  have hexp : 2 * 0.2366 - 2 * 0.5357 - 2 * log L ≤
      -(2 * ∑ p ∈ S, (1 : ℝ) / p + 2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))) := by
    push_cast at hR
    linarith
  have hE : exp (2 * 0.2366 - 2 * 0.5357 - 2 * log L) =
      exp (2 * 0.2366 - 2 * 0.5357) / L ^ 2 := by
    rw [exp_sub]
    congr 1
    rw [show 2 * log L = log L + log L by ring, exp_add, exp_log hL]; ring
  have hlow : exp (2 * 0.2366 - 2 * 0.5357) / L ^ 2 ≤ ∏ p ∈ S, (1 - g N p) := by
    rw [← hE]; exact le_trans (exp_le_exp.mpr hexp) hprod
  have hc := DDConst.lemma2_2_const
  have hL2 : 0 < L ^ 2 := by positivity
  calc 0.2749 / L ^ 2 ≤ (1 / 2 * exp (2 * 0.2366 - 2 * 0.5357)) / L ^ 2 :=
        div_le_div_of_nonneg_right hc hL2.le
    _ = 1 / 2 * (exp (2 * 0.2366 - 2 * 0.5357) / L ^ 2) := by ring
    _ ≤ 1 / 2 * ∏ p ∈ S, (1 - g N p) := by gcongr

/-! ### Lemma 2.3 in its `R₄` form -/

/-- **Dudek-Dunn Lemma 2.3**, `R₄(A, z^{18.4}) < 0.591 z^{18.4} log⁸ z` for `z ≥ 10^10`.
CONDITIONAL ON `RSRecip` and `NathansonRd`; Rankin's trick is `DDLemma23.rankin_sum_lt` and
the `Σ log p / p` input is `RSLogSum`, both PROVED. -/
theorem lemma2_3_of (hRec : RSRecip) (hNat : NathansonRd) (N : ℕ) (z : ℝ) (hz : 10 ^ 10 ≤ z) :
    R4 N z (z ^ (18.4 : ℝ)) < 0.591 * z ^ (18.4 : ℝ) * log z ^ 8 := by
  have hP : ∀ p ∈ primesIn 2 z, p.Prime ∧ (p : ℝ) < z := fun p hp => by
    simp only [primesIn, mem_filter] at hp; exact ⟨hp.2.1, hp.2.2.2⟩
  refine lt_of_le_of_lt ?_ (RSLogSum.rankin_sum_lt_of_RS1 z hz _ hP (hRec z hz))
  unfold R4
  apply sum_le_sum
  intro s hs
  have hsub : s ⊆ primesIn 2 z := mem_powerset.mp (mem_filter.mp hs).1
  have h := hNat N s (fun p hp => (hP p (hsub hp)).1)
  calc (4 : ℝ) ^ s.card * |rd N s| ≤ 4 ^ s.card * 2 ^ s.card := by gcongr
    _ = 8 ^ s.card := by rw [← mul_pow]; norm_num

/-! ### Theorem 3.3, Case 3 -/

lemma sifted_of_Sc {N : ℕ} {z : ℝ} (h : 0 < Sc N z) : Campbell2026.SiftedExists N z := by
  obtain ⟨n, hn⟩ := Finset.card_pos.mp h
  rw [mem_filter, mem_Icc] at hn
  refine ⟨n, hn.1.1, hn.1.2, fun p hp hdvd => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hn.2 p _ hdvd
  simp only [primesIn, mem_filter, mem_range]
  exact ⟨Nat.lt_ceil.mpr hlt, hp, by exact_mod_cast hp.two_le, hlt⟩

/-- **Theorem 3.3, Case 3**: `S(A, N^{1/20}) > 0` for every `N ≥ 10^200`. CONDITIONAL ON `RSHyp`,
`RSRecip`, `NathansonRd` and `SelbergThm13`. Theorem 1.3 at `s = 18.4`, `K = 3`, with Lemmas 2.1,
2.2, 2.3 as above and the arithmetic `DDConst.case3_main`, `DDConst.case3_s_cond`,
`DDCase3.case3_all`. -/
theorem sifted_large (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    Campbell2026.SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ))) := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
    exact_mod_cast this
  set z := (N : ℝ) ^ (1 / (20 : ℝ)) with hzdef
  have hz10 : (10 : ℝ) ^ 10 ≤ z := by
    have e : ((10 : ℝ) ^ 200) ^ (1 / (20 : ℝ)) = 10 ^ 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← e]
    exact rpow_le_rpow (by positivity) hN (by norm_num)
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz10
  set L := log (N : ℝ) with hLdef
  have hL : 0 < L := log_pos (lt_of_lt_of_le (by norm_num) hN)
  have hlz : log z = L / 20 := by rw [hzdef, Real.log_rpow hN0]; ring
  set D := z ^ (18.4 : ℝ) with hD
  have hlD : log D = 18.4 * log z := by rw [hD, Real.log_rpow hz0]
  have hs : log D / log z = 18.4 := by
    rw [hlD]; field_simp [show log z ≠ 0 by rw [hlz]; positivity]
  have hDN : D = (N : ℝ) ^ (0.92 : ℝ) := by
    rw [hD, hzdef, ← Real.rpow_mul hN0.le]; norm_num
  have hcond : 2 * (2 + log 3) + 3 ≤ log D / log z := by
    rw [hs]; exact DDConst.case3_s_cond
  have hS := hSel N hN2 z D 3 (by linarith [show (2 : ℝ) ≤ 10 ^ 10 by norm_num]) (by norm_num)
    (dimCond_of_RS hRS N) hcond
  rw [hs] at hS
  have hF : 0.0364 < Fsk 18.4 (2 + log 3) := by unfold Fsk; exact DDConst.case3_F
  have hM : 4 ≤ 0.2749 * 400 * Fsk 18.4 (2 + log 3) := by unfold Fsk; exact DDConst.case3_main
  have hV := lemma2_2_of hRec N z hz10
  rw [hlz] at hV
  have hR := lemma2_3_of hRec hNat N z hz10
  rw [← hD, hlz, hDN] at hR
  have hX : Xc N = (N : ℝ) - 1 := by
    unfold Xc; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hX0 : 0 ≤ (N : ℝ) - 1 := by linarith [show (1 : ℝ) ≤ 10 ^ 200 by norm_num]
  rw [hX] at hS
  have hfin := DDCase3.case3_all N hN
  rw [← hLdef] at hfin
  -- the main term
  have hV' : 0.2749 * 400 / L ^ 2 ≤ V N z := by
    have : 0.2749 / (L / 20) ^ 2 = 0.2749 * 400 / L ^ 2 := by field_simp; ring
    linarith
  have hmain : 4 * ((N : ℝ) - 1) / L ^ 2 ≤ ((N : ℝ) - 1) * V N z * Fsk 18.4 (2 + log 3) := by
    have hL2 : 0 < L ^ 2 := by positivity
    have h1 : ((N : ℝ) - 1) * (0.2749 * 400 / L ^ 2) * Fsk 18.4 (2 + log 3) ≤
        ((N : ℝ) - 1) * V N z * Fsk 18.4 (2 + log 3) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hV' hX0
    have h2 : 4 * ((N : ℝ) - 1) / L ^ 2 ≤
        ((N : ℝ) - 1) * (0.2749 * 400 / L ^ 2) * Fsk 18.4 (2 + log 3) := by
      rw [show ((N : ℝ) - 1) * (0.2749 * 400 / L ^ 2) * Fsk 18.4 (2 + log 3) =
          (0.2749 * 400 * Fsk 18.4 (2 + log 3)) * (((N : ℝ) - 1) / L ^ 2) by ring,
        show 4 * ((N : ℝ) - 1) / L ^ 2 = 4 * (((N : ℝ) - 1) / L ^ 2) by ring]
      exact mul_le_mul_of_nonneg_right hM (by positivity)
    linarith
  -- the error term
  have herr : 2 * R4 N z D < (1.182 / 20 ^ 8) * (N : ℝ) ^ (0.92 : ℝ) * L ^ 8 := by
    rw [hDN]
    have : 2 * (0.591 * (N : ℝ) ^ (0.92 : ℝ) * (L / 20) ^ 8) =
        (1.182 / 20 ^ 8) * (N : ℝ) ^ (0.92 : ℝ) * L ^ 8 := by ring
    linarith
  have hpos : (0 : ℝ) < Sc N z := by linarith
  exact sifted_of_Sc (by exact_mod_cast hpos)

/-! ### Theorem 3.3 and Theorem 1.2 -/

/-- **Theorem 3.3 for `N ≥ 10^200`**, no gap table and no script: `N = a + b` with
`Ω(ab) ≤ 39` for even `N`, `≤ 40` for odd `N`. CONDITIONAL ON `RSHyp`, `RSRecip`,
`NathansonRd`, `SelbergThm13`. -/
theorem theorem3_3_large (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 := by
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := le_trans (by norm_num) hN
    exact_mod_cast this
  obtain ⟨a, b, ha, hb, hab, he, ho⟩ :=
    Campbell2026.lemma5_2 hN2 (by norm_num : (1 : ℝ) < 20) (sifted_large hRS hRec hNat hSel N hN)
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · intro hE
    have := he hE
    have : (bigOmega (a * b) : ℝ) < 40 := by linarith
    have : bigOmega (a * b) < 40 := by exact_mod_cast this
    omega
  · by_cases hE : Even N
    · have := he hE
      have : (bigOmega (a * b) : ℝ) < 41 := by linarith
      have : bigOmega (a * b) < 41 := by exact_mod_cast this
      omega
    · have := ho hE
      have : (bigOmega (a * b) : ℝ) < 41 := by linarith
      have : bigOmega (a * b) < 41 := by exact_mod_cast this
      omega

/-- `S(A, N^{1/20}) > 0` for every `N > 4 · 10^18`: the `hS` input of
`DudekDunn2026.theorem3_3_of`, from the script below `10^200` and Case 3 above. -/
theorem sifted_all (hV : VerifySScript) (hRS : DDLemma21All.RSHyp) (hRec : RSRecip)
    (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 4 * 10 ^ 18 < N → Campbell2026.SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ))) := by
  intro N hN
  by_cases h : (N : ℝ) < 10 ^ 200
  · exact hV N hN h
  · push Not at h
    exact sifted_large hRS hRec hNat hSel N h

/-- **Dudek-Dunn Theorem 3.3**: every `N ≥ 2` is `a + b`, positive, with `Ω(ab) ≤ 39` for even
`N` and `≤ 40` for odd `N`. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RSHyp`, `RSRecip`,
`NathansonRd`, `SelbergThm13`. -/
theorem theorem3_3 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  DudekDunn2026.theorem3_3_of hG (sifted_all hV hRS hRec hNat hSel)

/-- **Dudek-Dunn Theorem 1.2**, the statement `dudek_dunn` of Statements.lean. Same inputs. -/
theorem theorem1_2 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N :=
  DudekDunn2026.dudek_dunn_of hG (sifted_all hV hRS hRec hNat hSel)

/-! ### Vacuity checks -/

/-- The sieve premise `s ≥ 2k + 3` of Theorem 1.3 holds at the paper's `s = 18.4`, `K = 3`, so
`SelbergThm13` really fires in `sifted_large`. -/
theorem premise_fires : 2 * (2 + log 3) + 3 ≤ (18.4 : ℝ) := DDConst.case3_s_cond

/-- `SelbergThm13` holds at its degenerate instance `z = 2`, where nothing is sifted, for every
`N ≥ 2`, `D` and `K` meeting its premises: the cited input is consistent there. -/
theorem selberg_at_two (N : ℕ) (hN : 2 ≤ N) (D K : ℝ) (hK : 1 ≤ K)
    (hc : 2 * (2 + log K) + 3 ≤ log D / log 2) :
    Xc N * V N 2 * Fsk (log D / log 2) (2 + log K) - 2 * R4 N 2 D ≤ (Sc N 2 : ℝ) := by
  have he : primesIn 2 2 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp; simp only [primesIn, mem_filter] at hp; linarith [hp.2.2.1, hp.2.2.2]
  have hV1 : V N 2 = 1 := by unfold V; rw [he, prod_empty]
  have hSc : Sc N 2 = N - 1 := by
    unfold Sc
    rw [Finset.filter_true_of_mem (fun n _ p hp => by rw [he] at hp; simp at hp)]
    simp
  have hR0 : 0 ≤ R4 N 2 D := by
    unfold R4; apply sum_nonneg; intro s _; positivity
  have hlK : 0 ≤ log K := log_nonneg hK
  set s := log D / log 2
  have hs3 : 0 < s - 3 := by linarith
  have hF : Fsk s (2 + log K) ≤ 1 := by
    unfold Fsk
    have : 0 ≤ (s + 3) / (2 * exp (2 + log K)) *
        (2 * exp 1 * (2 + log K) / (s - 3)) ^ ((s - 3) / 2) := by
      apply mul_nonneg (div_nonneg (by linarith) (by positivity))
      apply Real.rpow_nonneg
      apply div_nonneg _ hs3.le
      have := exp_pos 1
      positivity
    linarith
  rw [hV1, hSc]
  have hX : Xc N = ((N - 1 : ℕ) : ℝ) := rfl
  rw [hX]
  have hX0 : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The sifted-existence statement the chain consumes is a real constraint: it fails at
`N = 4`, `z = 4`, where `a₁ = 3`, `a₂ = 4`, `a₃ = 3`. -/
theorem sifted_not_trivial : ¬ Campbell2026.SiftedExists 4 4 := by
  rintro ⟨n, h1, h2, h⟩
  have h4 : Even 4 := ⟨2, rfl⟩
  interval_cases n
  · have := h 3 Nat.prime_three (by simp [Campbell2026.aSeq, h4])
    norm_num at this
  · have := h 2 Nat.prime_two (by simp [Campbell2026.aSeq, h4])
    norm_num at this
  · have := h 3 Nat.prime_three (by simp [Campbell2026.aSeq, h4])
    norm_num at this

lemma bigOmega_three_pow (k : ℕ) : bigOmega (3 ^ k) = k := by
  induction k with
  | zero => simp [bigOmega]
  | succ n ih =>
    rw [pow_succ, Campbell2026.bigOmega_mul (by positivity) (by norm_num),
      Campbell2026.bigOmega_prime Nat.prime_three, ih]

/-- The conclusion is not the trivial split: at the even `N = 3^40 + 1`, the split
`1 + 3^40` has `Ω(ab) = 40 > 39`. -/
theorem trivial_split_fails : Even (3 ^ 40 + 1) ∧ bigOmega (1 * 3 ^ 40) = 40 := by
  refine ⟨by decide, ?_⟩
  rw [one_mul, bigOmega_three_pow]

#print axioms dimCond_of_RS
#print axioms lemma2_2_of
#print axioms lemma2_3_of
#print axioms sifted_large
#print axioms theorem3_3_large
#print axioms theorem3_3
#print axioms theorem1_2
#print axioms selberg_at_two
#print axioms sifted_not_trivial
#print axioms trivial_split_fails

end LeanLab.AlmostPrimes.DDMain
