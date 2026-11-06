/-
Split of the singular series tail `singular_tail357` into three steps, with one
further ingredient supporting the third step. Nothing here changes the
statement: `singular_tail357_split` states it character for character and proves
it from the leaves below, which record, in order, (1) the Euler product identity
for the full Ramanujan weight series, (2) the finite Ramanujan sum up to N to the
one tenth against the product of the local factors at the primes up to that
point, and (3) that finite product against the full series, whose size is
controlled by (4) the tail of the reciprocal squares of p minus one.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357l
import LeanLab.HeathBrown1985.SingularSeries

namespace LeanLab.Linnik1951

set_option backward.isDefEq.respectTransparency false

open Finset
open scoped Topology BigOperators

/-! ### Leaf 4: the prime reciprocal square tail -/

/-- The tail function on the natural numbers, `1/(m-1)²` past the cut off, is summable:
it is dominated by `4/m²`, and `m ≤ 2(m-1)` for `m ≥ 2`. -/
private lemma primeTailTermLe357 (x m : ℕ) :
    (if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0) ≤ 4 / (m : ℝ) ^ 2 := by
  by_cases hxm : x < m
  · rw [if_pos hxm]
    have hm1 : 1 ≤ m := by omega
    rcases Nat.eq_or_lt_of_le hm1 with h | h
    · subst h
      norm_num
    · have hm2 : 2 ≤ m := h
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have hpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hpos' : (0 : ℝ) < ((m : ℝ) - 1) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hpos' (by positivity)]
      nlinarith [sq_nonneg ((m : ℝ) - 1)]
  · rw [if_neg hxm]
    positivity

private lemma primeTailSummable357 (x : ℕ) :
    Summable (fun m : ℕ => if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0) := by
  have hpow : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hG : Summable (fun m : ℕ => 4 / (m : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using hpow.mul_left 4
  refine Summable.of_nonneg_of_le (f := fun m : ℕ => 4 / (m : ℝ) ^ 2) ?_ ?_ hG
  · intro m
    split_ifs <;> positivity
  · exact fun m => primeTailTermLe357 x m

/-- The sum over the primes is at most the sum over the natural numbers, since the
latter dominates term by term. -/
private lemma primeTailTsumLe357 (x : ℕ) :
    (∑' p : Nat.Primes,
        (if x < (p : ℕ) then 1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0)) ≤
      ∑' m : ℕ, (if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0) :=
  (primeTailSummable357 x).tsum_subtype_le
    (fun m : ℕ => if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0) {q : ℕ | q.Prime}
    (fun m => by split_ifs <;> positivity)

/-- Telescoping: the difference of consecutive reciprocal shifts sums to the first
term. -/
private lemma hasSum_shift_diff357 (a : ℝ) (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1)) (1 / a) := by
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1))
        = 1 / a - 1 / ((n : ℝ) + a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((n : ℝ) + a) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + a + 1) ≠ 0 := by positivity
      have h3 : (((n + 1 : ℕ) : ℝ) + a) = (n : ℝ) + a + 1 := by push_cast; ring
      rw [h3]
      field_simp
      ring
  have hnn : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + a := by positivity
    have hk' : (0 : ℝ) < (k : ℝ) + a + 1 := by positivity
    have : 1 / ((k : ℝ) + a + 1) ≤ 1 / ((k : ℝ) + a) :=
      one_div_le_one_div_of_le hk (by linarith)
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / a - 1 / ((n : ℝ) + a))
      Filter.atTop (nhds (1 / a)) := by
    have hinf : Filter.Tendsto (fun n : ℕ => (n : ℝ) + a) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + a)) Filter.atTop (nhds 0) := by
      simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hinf
    simpa using tendsto_const_nhds.sub h0
  refine (hasSum_iff_tendsto_nat_of_nonneg hnn (1 / a)).mpr ?_
  simpa only [hpart] using hlim

/-- The tail is the sum of `1/(k+x)²` over `k`, with the cut off removed. -/
private lemma tailShift357 (x : ℕ) :
    (∑' m : ℕ, (if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0))
      = ∑' k : ℕ, 1 / ((k : ℝ) + (x : ℝ)) ^ 2 := by
  have hS := primeTailSummable357 x
  have hzero : ∑ i ∈ Finset.range (x + 1),
      (if x < i then 1 / ((i : ℝ) - 1) ^ 2 else 0) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact if_neg (by omega)
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun m : ℕ => if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0) (x + 1) hS
  rw [hzero, zero_add] at hsplit
  rw [← hsplit]
  refine tsum_congr (fun k => ?_)
  have hlt : x < k + (x + 1) := by omega
  have hcast : (((k + (x + 1) : ℕ)) : ℝ) - 1 = (k : ℝ) + (x : ℝ) := by push_cast; ring
  show (if x < k + (x + 1) then 1 / (((k + (x + 1) : ℕ) : ℝ) - 1) ^ 2 else 0)
      = 1 / ((k : ℝ) + (x : ℝ)) ^ 2
  rw [if_pos hlt, hcast]

/-- The full natural-number tail is at most `2/x` for `x ≥ 2`. -/
private lemma primeTailNatLe357 (x : ℕ) (hx : 2 ≤ x) :
    (∑' m : ℕ, (if x < m then 1 / ((m : ℝ) - 1) ^ 2 else 0)) ≤ 2 / (x : ℝ) := by
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [tailShift357 x]
  have ha : (0 : ℝ) < (x : ℝ) - 1 := by linarith
  have htel := hasSum_shift_diff357 ((x : ℝ) - 1) ha
  have hsumtel : Summable (fun k : ℕ =>
      1 / ((k : ℝ) + ((x : ℝ) - 1)) - 1 / ((k : ℝ) + ((x : ℝ) - 1) + 1)) := htel.summable
  have hpoint : ∀ k : ℕ, 1 / ((k : ℝ) + (x : ℝ)) ^ 2 ≤
      1 / ((k : ℝ) + ((x : ℝ) - 1)) - 1 / ((k : ℝ) + ((x : ℝ) - 1) + 1) := by
    intro k
    have ht : (2 : ℝ) ≤ (k : ℝ) + (x : ℝ) := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hd : (0 : ℝ) < (k : ℝ) + (x : ℝ) - 1 := by linarith
    have hd' : (0 : ℝ) < (k : ℝ) + (x : ℝ) := by linarith
    have hkey : 1 / ((k : ℝ) + (x : ℝ) - 1) - 1 / ((k : ℝ) + (x : ℝ))
        = 1 / (((k : ℝ) + (x : ℝ) - 1) * ((k : ℝ) + (x : ℝ))) := by
      field_simp
      ring
    have hden : (0 : ℝ) < ((k : ℝ) + (x : ℝ) - 1) * ((k : ℝ) + (x : ℝ)) := by positivity
    have hstep : 1 / ((k : ℝ) + (x : ℝ)) ^ 2
        ≤ 1 / (((k : ℝ) + (x : ℝ) - 1) * ((k : ℝ) + (x : ℝ))) := by
      rw [div_le_div_iff₀ (by positivity) hden]
      nlinarith
    calc 1 / ((k : ℝ) + (x : ℝ)) ^ 2
        ≤ 1 / (((k : ℝ) + (x : ℝ) - 1) * ((k : ℝ) + (x : ℝ))) := hstep
      _ = 1 / ((k : ℝ) + (x : ℝ) - 1) - 1 / ((k : ℝ) + (x : ℝ)) := hkey.symm
      _ = 1 / ((k : ℝ) + ((x : ℝ) - 1)) - 1 / ((k : ℝ) + ((x : ℝ) - 1) + 1) := by
          ring_nf
  have hsumlhs : Summable (fun k : ℕ => 1 / ((k : ℝ) + (x : ℝ)) ^ 2) :=
    Summable.of_nonneg_of_le (g := fun k : ℕ => 1 / ((k : ℝ) + (x : ℝ)) ^ 2) (fun k => by positivity)
      hpoint hsumtel
  have hle := Summable.tsum_le_tsum (L := SummationFilter.unconditional ℕ) hpoint hsumlhs hsumtel
  rw [htel.tsum_eq] at hle
  refine hle.trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith : (0 : ℝ) < (x : ℝ))]
  linarith

/-! ### The Ramanujan weight of the singular series as the Heath-Brown coefficient -/

private lemma primePowNotSquarefree357 {p i : ℕ} (hp : p.Prime) (hi : 2 ≤ i) :
    ¬ Squarefree (p ^ i) := by
  intro hsq
  have hd : p * p ∣ p ^ i := by
    rw [← pow_two]
    exact pow_dvd_pow p hi
  exact hp.not_isUnit (hsq p hd)

/-- The Ramanujan weight is multiplicative across coprime moduli, in `ℂ`. -/
private lemma ramWeightMul357 (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    (((ArithmeticFunction.moebius (a * b) : ℝ) ^ 2 / (((a * b).totient : ℝ)) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum (a * b) n =
      ((((ArithmeticFunction.moebius a : ℝ) ^ 2 / ((a.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum a n) *
        ((((ArithmeticFunction.moebius b : ℝ) ^ 2 / ((b.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum b n) := by
  rw [LeanLab.Perelli1996.Ramanujan103.ramanujanSum_mul a b n ha hb hcop, Nat.totient_mul hcop,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  push_cast
  ring

/-- At a prime modulus the Ramanujan weight is the local factor of the singular series. -/
private lemma ramWeightPrime357 (n p : ℕ) (hp : p.Prime) :
    (((ArithmeticFunction.moebius p : ℝ) ^ 2 / ((p.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum p n
      = (LeanLab.HeathBrown1985.vloc n p : ℂ) := by
  have hφ : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    norm_num
  have hμ : ((ArithmeticFunction.moebius p : ℝ)) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hreal : (1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ n then ((p : ℝ) - 1) else -1)
      = LeanLab.HeathBrown1985.vloc n p := by
    unfold LeanLab.HeathBrown1985.vloc LeanLab.HeathBrown1985.Ecop
    by_cases hd : p ∣ n
    · have hnc : ¬ Nat.Coprime n p := by
        intro hc
        have h1' : Nat.gcd n p = 1 := hc.gcd_eq_one
        have h2' : Nat.gcd n p = p := by
          rw [Nat.gcd_comm]; exact Nat.gcd_eq_left hd
        rw [h2'] at h1'
        exact hp.ne_one h1'
      rw [if_pos hd, if_neg hnc]
      field_simp
      ring
    · have hc : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).mpr hd).symm
      rw [if_neg hd, if_pos hc]
      field_simp
      ring
  rw [LeanLab.Perelli1996.Ramanujan103.ramanujanSum_prime p n hp, hμ, hφ]
  have hstep : ((if p ∣ n then ((p : ℂ) - 1) else -1))
      = (((if p ∣ n then ((p : ℝ) - 1) else -1) : ℝ) : ℂ) := by
    by_cases hd : p ∣ n
    · rw [if_pos hd, if_pos hd]; push_cast; ring
    · rw [if_neg hd, if_neg hd]; norm_num
  have hreal' : (((1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ n then ((p : ℝ) - 1) else -1) : ℝ) : ℂ)
      = ((LeanLab.HeathBrown1985.vloc n p : ℝ) : ℂ) := by rw [hreal]
  rw [hstep, show ((-1 : ℝ) ^ 2) = 1 by norm_num, ← Complex.ofReal_mul]
  exact hreal'

/-- The Ramanujan weight of the singular series is the Heath-Brown coefficient `g_n`. -/
private lemma ramWeightEqGm357 (n q : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.moebius q : ℝ) ^ 2 / ((q.totient : ℝ)) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re
      = LeanLab.HeathBrown1985.gm n q := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ArithmeticFunction ℂ, ∀ q : ℕ,
      F q = ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / ((q.totient : ℝ)) ^ 2 : ℝ)) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n :=
    ⟨⟨fun q : ℕ => (((ArithmeticFunction.moebius q : ℝ) ^ 2 / ((q.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n, by
          simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]⟩, fun q => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ArithmeticFunction ℂ, ∀ q : ℕ,
      G q = ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ) :=
    ⟨⟨fun q : ℕ => ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ), by
        simp [LeanLab.HeathBrown1985.gm_zero]⟩, fun q => rfl⟩
  have hFm : F.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · rw [hF 1]
      norm_num [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
    · intro a b hab
      rw [hF (a * b), hF a, hF b]
      rcases Nat.eq_zero_or_pos a with h0 | ha
      · subst h0
        have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
        subst hb
        simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
      rcases Nat.eq_zero_or_pos b with h0 | hb
      · subst h0
        have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
        subst ha1
        simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
      · exact ramWeightMul357 n a b ha hb hab
  have hGm : G.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · rw [hG 1]
      norm_num [LeanLab.HeathBrown1985.gm_one]
    · intro a b hab
      rw [hG (a * b), hG a, hG b, LeanLab.HeathBrown1985.gm_mul n hab]
      push_cast
      ring
  have hpp : ∀ p i : ℕ, Nat.Prime p → F (p ^ i) = G (p ^ i) := by
    intro p i hp
    rw [hF (p ^ i), hG (p ^ i)]
    rcases Nat.eq_zero_or_pos i with h0 | hi
    · subst h0
      norm_num [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e,
        LeanLab.HeathBrown1985.gm_one]
    rcases Nat.lt_or_ge 1 i with h2 | h1
    · have hns : ¬ Squarefree (p ^ i) := primePowNotSquarefree357 hp h2
      have hμ0 : ArithmeticFunction.moebius (p ^ i) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
      have hgm0 : LeanLab.HeathBrown1985.gm n (p ^ i) = 0 := by
        rw [LeanLab.HeathBrown1985.gm_eq, if_neg hns]
      rw [hμ0, hgm0]
      norm_num
    · have hi1 : i = 1 := by omega
      subst hi1
      have hgmp : LeanLab.HeathBrown1985.gm n p = LeanLab.HeathBrown1985.vloc n p := by
        rw [LeanLab.HeathBrown1985.gm_eq, if_pos hp.squarefree, Nat.Prime.primeFactors hp,
          Finset.prod_singleton]
      rw [pow_one, hgmp]
      exact ramWeightPrime357 n p hp
  have heq := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers F hFm G hGm).mpr hpp
  have hq : F q = G q := DFunLike.congr_fun heq q
  rw [hF q, hG q] at hq
  have h2 := congrArg Complex.re hq
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
  simpa using h2

/-! ### Leaf 1: the Euler product identity -/

/-- The Ramanujan weight is multiplicative on coprime moduli, in `ℝ`. -/
private lemma ramWeightMulReal357 (n a b : ℕ) (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    (ArithmeticFunction.moebius (a * b) : ℝ) ^ 2 / (((a * b).totient : ℝ)) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum (a * b) n).re
      = ((ArithmeticFunction.moebius a : ℝ) ^ 2 / ((a.totient : ℝ)) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum a n).re) *
        ((ArithmeticFunction.moebius b : ℝ) ^ 2 / ((b.totient : ℝ)) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum b n).re) := by
  rw [ramWeightEqGm357 n (a * b) hn, ramWeightEqGm357 n a hn, ramWeightEqGm357 n b hn,
    LeanLab.HeathBrown1985.gm_mul n hcop]

/-- The Ramanujan weight is summable in absolute value, because it is the Heath-Brown
coefficient `g_n` and `Σ_q |g_n(q)|` converges. -/
private lemma ramWeightSummable357 (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ =>
      ‖(ArithmeticFunction.moebius q : ℝ) ^ 2 / ((q.totient : ℝ)) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re‖) := by
  have h := LeanLab.HeathBrown1985.summable_abs_gm n hn
  refine h.congr (fun q => ?_)
  rw [ramWeightEqGm357 n q hn]

/-- At a prime modulus the local factor of the Euler product is the singular-series factor. -/
private lemma ramWeightLocalFactor357 (n p : ℕ) (hp : p.Prime) :
    1 + (ArithmeticFunction.moebius p : ℝ) ^ 2 / ((p.totient : ℝ)) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum p n).re
      = (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hφ : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    norm_num
  have hμ : ((ArithmeticFunction.moebius p : ℝ)) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hne : ((p : ℝ) - 1) ≠ 0 := h1.ne'
  have hc : (((p : ℂ) - 1)).re = (p : ℝ) - 1 := by
    rw [show ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring]
    simp
  rw [hμ, hφ, LeanLab.Perelli1996.Ramanujan103.ramanujanSum_prime p n hp,
    show ((-1 : ℝ) ^ 2) = 1 by norm_num, one_div, one_div]
  by_cases hd : p ∣ n
  · simp only [if_pos hd, hc]
    field_simp
  · simp only [if_neg hd]
    norm_num
    field_simp
    ring
private lemma succLeTwoPow357 (a : ℕ) :
    (a : ℝ) + 1 ≤ (2 : ℝ) ^ (50 : ℕ) * (2 : ℝ) ^ ((a : ℝ) / 50) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.lt_or_ge a 50 with h | h
    · have ha : (a : ℝ) + 1 ≤ 50 := by
        have : a + 1 ≤ 50 := by omega
        exact_mod_cast this
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) / 50) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) := one_le_pow₀ (by norm_num)
      nlinarith
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 50 := ⟨a - 50, by omega⟩
      have hb := ih b (by omega)
      have hsplit : ((b + 50 : ℕ) : ℝ) / 50 = (b : ℝ) / 50 + 1 := by push_cast; ring
      rw [hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((b : ℝ) / 50) := by positivity
      have h50 : (50 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) := by norm_num
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) / 50) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hB : (50 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) * (2 : ℝ) ^ ((b : ℝ) / 50) := by
        calc (50 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) * 1 := by rw [mul_one]; exact h50
          _ ≤ (2 : ℝ) ^ (50 : ℕ) * (2 : ℝ) ^ ((b : ℝ) / 50) :=
              mul_le_mul_of_nonneg_left hone (by positivity)
      push_cast
      nlinarith

/-- `a + 1 ≤ 2 ^ a`. -/
private lemma succLeTwoPowNat357 (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

/-- A pointwise divisor bound: `d(n) ≤ C n^(1/50)`. Small primes are handled by
`succLeTwoPow357`, large primes by `2^a ≤ p^(a/50)` for `p > 2^50`. -/
private lemma divisorBound357 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 50 : ℝ) := by
  classical
  refine ⟨(2 : ℝ) ^ (50 * (2 ^ 50 + 1) : ℕ), by positivity, fun n hn => ?_⟩
  rw [Nat.card_divisors hn]
  push_cast
  have hper : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      (if p ≤ 2 ^ 50 then (2 : ℝ) ^ (50 : ℕ) else 1) *
        (p : ℝ) ^ ((n.factorization p : ℝ) / 50) := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    by_cases hle : p ≤ 2 ^ 50
    · simp only [if_pos hle]
      have h1 := succLeTwoPow357 (n.factorization p)
      have h2 : (2 : ℝ) ^ ((n.factorization p : ℝ) / 50) ≤
          (p : ℝ) ^ ((n.factorization p : ℝ) / 50) :=
        Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
      have h3 : (0 : ℝ) < (2 : ℝ) ^ (50 : ℕ) := by positivity
      nlinarith
    · simp only [if_neg hle]
      have hp50 : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 50 : ℝ) := by
        have h1 : ((2 : ℝ) ^ (50 : ℕ)) ^ (1 / 50 : ℝ) = (2 : ℝ) := by
          rw [← Real.rpow_natCast (2 : ℝ) 50]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [show (((50 : ℕ)) : ℝ) * (1 / 50 : ℝ) = 1 by norm_num, Real.rpow_one]
        rw [← h1]
        refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
        have h2 : (2 : ℝ) ^ (50 : ℕ) ≤ (p : ℝ) := by
          have h3 : 2 ^ 50 ≤ p := le_of_lt (not_le.mp hle)
          exact_mod_cast h3
        linarith
      have hnat : ((n.factorization p : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n.factorization p : ℕ) := by
        have := succLeTwoPowNat357 (n.factorization p)
        exact_mod_cast this
      have hstep : (2 : ℝ) ^ (n.factorization p : ℕ) ≤
          ((p : ℝ) ^ (1 / 50 : ℝ)) ^ (n.factorization p : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hp50 _
      have hcomb : ((p : ℝ) ^ (1 / 50 : ℝ)) ^ (n.factorization p : ℕ) =
          (p : ℝ) ^ ((n.factorization p : ℝ) / 50) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ (1 / 50 : ℝ)) (n.factorization p)]
        rw [← Real.rpow_mul (le_of_lt hp0)]
        congr 1
        push_cast
        ring
      rw [← hcomb]
      linarith
  have hprod : (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1))
      ≤ ∏ p ∈ n.primeFactors,
          ((if p ≤ 2 ^ 50 then (2 : ℝ) ^ (50 : ℕ) else 1) *
            (p : ℝ) ^ ((n.factorization p : ℝ) / 50)) := by
    refine Finset.prod_le_prod₀ (fun p hp => by positivity) hper
  rw [Finset.prod_mul_distrib] at hprod
  have hcard : (n.primeFactors.filter (fun p => p ≤ 2 ^ 50)).card ≤ 2 ^ 50 + 1 := by
    have hsub : n.primeFactors.filter (fun p => p ≤ 2 ^ 50) ⊆ Finset.range (2 ^ 50 + 1) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      simp only [Finset.mem_range]
      omega
    calc (n.primeFactors.filter (fun p => p ≤ 2 ^ 50)).card
        ≤ (Finset.range (2 ^ 50 + 1)).card := Finset.card_le_card hsub
      _ = 2 ^ 50 + 1 := Finset.card_range _
  have hconst : (∏ p ∈ n.primeFactors, if p ≤ 2 ^ 50 then (2 : ℝ) ^ (50 : ℕ) else 1)
      = ((2 : ℝ) ^ (50 : ℕ)) ^ (n.primeFactors.filter (fun p => p ≤ 2 ^ 50)).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hbase : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ)) = (n : ℝ) := by
    have hcast2 : ((n : ℝ)) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
      rw [Nat.cast_prod]
      simp only [Nat.cast_pow]
    exact hcast2.symm
  have hpow : (∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) / 50))
      = (n : ℝ) ^ (1 / 50 : ℝ) := by
    have hpt : ∀ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) / 50) =
        ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 50 : ℝ) := by
      intro p hp
      rw [← Real.rpow_natCast (p : ℝ) (n.factorization p)]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
      congr 1
      push_cast
      ring
    calc (∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) / 50))
        = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 50 : ℝ) :=
          Finset.prod_congr rfl hpt
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 50 : ℝ) :=
          Real.finsetProd_rpow _ _ (fun p hp => by positivity) _
      _ = (n : ℝ) ^ (1 / 50 : ℝ) := by rw [hbase]
  have hM : (0 : ℝ) < (2 : ℝ) ^ (50 : ℕ) := by positivity
  have hnpos : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 50 : ℝ) := by positivity
  calc (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1))
      ≤ (∏ p ∈ n.primeFactors, (if p ≤ 2 ^ 50 then (2 : ℝ) ^ (50 : ℕ) else 1)) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) / 50) := hprod
    _ = ((2 : ℝ) ^ (50 : ℕ)) ^ (n.primeFactors.filter (fun p => p ≤ 2 ^ 50)).card *
          (n : ℝ) ^ (1 / 50 : ℝ) := by rw [hconst, hpow]
    _ ≤ ((2 : ℝ) ^ (50 : ℕ)) ^ (2 ^ 50 + 1) * (n : ℝ) ^ (1 / 50 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hnpos
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ)) hcard
    _ = (2 : ℝ) ^ (50 * (2 ^ 50 + 1) : ℕ) * (n : ℝ) ^ (1 / 50 : ℝ) := by
        rw [← pow_mul]

/-- The local Euler factor: only the exponents `0` and `1` contribute. -/
private lemma ramWeightLocalTsum357 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) :
    (∑' e : ℕ, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (p ^ e))
      = (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hvan : ∀ e : ℕ, 2 ≤ e →
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (p ^ e) = 0 := by
    intro e he
    have hns : ¬ Squarefree (p ^ e) := primePowNotSquarefree357 hp he
    have hμ0 : ArithmeticFunction.moebius (p ^ e) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    simp [hμ0]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    have h0 : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (p ^ 0) = 1 := by
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
    have h1 : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (p ^ 1)
        = (ArithmeticFunction.moebius p : ℝ) ^ 2 / ((p.totient : ℝ)) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum p n).re := by
      rw [pow_one]
    rw [h0, h1]
    simpa using ramWeightLocalFactor357 n p hp
  · intro e he
    rw [Finset.mem_range, not_lt] at he
    exact hvan e he

/-- The tail of the Ramanujan weight series beyond `F`, dominated by the
Heath-Brown tail bound. -/
private lemma ramWeightTailLe357 (n F : ℕ) (hn : 1 ≤ n) (hF : 1 ≤ F) :
    (∑' q : ℕ, if F < q then
        ‖(ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re‖ else 0)
      ≤ 4 * ((6 + 2 * Real.log (F : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (F : ℝ)) := by
  have hnn : ∀ q : ℕ, 0 ≤ (if F < q then
      ‖(ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re‖ else 0) := by
    intro q; split_ifs <;> positivity
  refine Real.tsum_le_of_sum_range_le hnn (fun m => ?_)
  have hset : (Finset.range m).filter (fun i => F < i) = Finset.Ioc F (m - 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]; omega
  have hstep : ∑ i ∈ Finset.range m, (if F < i then
      ‖(ArithmeticFunction.moebius i : ℝ) ^ 2 / (i.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum i n).re‖ else 0)
      = ∑ i ∈ Finset.Ioc F (m - 1), ‖LeanLab.HeathBrown1985.gm n i‖ := by
    rw [← Finset.sum_filter, hset]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ramWeightEqGm357 n i hn]
  rw [hstep]
  have hb := LeanLab.HeathBrown1985.sum_abs_gm_Ioc_le n F (m - 1) hn hF
  simpa [Real.norm_eq_abs] using hb


/-- The Ramanujan weight is `1` at `1` and `0` at `0`. -/
private lemma ramWeightOne357 (n : ℕ) :
    (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) 1 = 1 := by
  norm_num [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]

private lemma ramWeightZero357 (n : ℕ) :
    (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) 0 = 0 := by
  simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]

/-- The Ramanujan weight is multiplicative on coprime moduli. -/
private lemma ramWeightCoprime357 (n : ℕ) (hn : 1 ≤ n) {a b : ℕ} (hab : Nat.Coprime a b) :
    (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (a * b) =
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) a *
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) b := by
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0
    have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb
    simp [ramWeightZero357, ramWeightOne357]
  rcases Nat.eq_zero_or_pos b with h0 | hb
  · subst h0
    have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    simp [ramWeightZero357, ramWeightOne357]
  · exact ramWeightMulReal357 n a b hn ha hb hab


private lemma ramWeightSubtypeLe357 (n x : ℕ) (hn : 1 ≤ n)
    (T : Set ℕ) (hT : ∀ m : ℕ, m ∈ T → ‖(fun q : ℕ =>
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ =
      (if x < m then ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ else 0)) :
    ‖∑' m : ↑T, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
      (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖
      ≤ ∑' q : ℕ, if x < q then
          ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0 := by
  have hnormsum : Summable (fun m : ↑T => ‖(fun q : ℕ =>
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖) :=
    (ramWeightSummable357 n hn).subtype _
  have htailsumm : Summable (fun q : ℕ => if x < q then
      ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity)
      (fun q => by split_ifs <;> [exact le_rfl; positivity]) (ramWeightSummable357 n hn)
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  have heq : (∑' m : ↑T, ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖)
      = ∑' m : ↑T, (if x < (m : ℕ) then ‖(fun q : ℕ =>
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖ else 0) := by
    exact tsum_congr (fun m => hT (m : ℕ) m.2)
  rw [heq]
  exact htailsumm.tsum_subtype_le
    (fun q : ℕ => if x < q then ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 /
      (r.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0)
    T (fun q => by split_ifs <;> positivity)

/-- LEAF. Step 1 of 3: the Euler product identity. The weight sending q to the
square of the Moebius function at q over the square of the totient of q, times
the real part of the Ramanujan sum of q at n, is multiplicative across coprime
moduli and is supported on squarefree q, so the series over all q converges and
its sum is the Euler product over the primes that defines the singular series.
This is the identity alone: it carries no truncation, no rate and no uniformity
in N. -/
theorem singular_series_has_sum357 (n : ℕ) (hn : 2 ≤ n) :
    HasSum (fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (singularSeries111 n) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hsumm : Summable (fun q : ℕ => ‖(ArithmeticFunction.moebius q : ℝ) ^ 2 /
      (q.totient : ℝ) ^ 2 * (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re‖) :=
    ramWeightSummable357 n hn1
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) (a * b) =
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) a *
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) b := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with h0 | ha
    · subst h0
      have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
      subst hb
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
    rcases Nat.eq_zero_or_pos b with h0 | hb
    · subst h0
      have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
      subst ha1
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
    · exact ramWeightMulReal357 n a b hn1 ha hb hab
  have hone : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) 1 = 1 := by
    norm_num [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
  have hzero : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
      (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) 0 = 0 := by
    simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
  have hloc : ∀ p : Nat.Primes,
      (∑' e : ℕ, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
          (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ e))
        = (if (p : ℕ) ∣ n then 1 + 1 / (((p : ℕ) : ℝ) - 1)
            else 1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) := by
    intro p
    have hp : Nat.Prime (p : ℕ) := p.2
    have hvan : ∀ e : ℕ, 2 ≤ e →
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ e) = 0 := by
      intro e he
      have hns : ¬ Squarefree ((p : ℕ) ^ e) := primePowNotSquarefree357 hp he
      have hμ0 : ArithmeticFunction.moebius ((p : ℕ) ^ e) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
      simp [hμ0]
    rw [tsum_eq_sum (s := Finset.range 2)]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have h0 : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ 0) = 1 := by
        simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
      have h1 : (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ 1)
          = (ArithmeticFunction.moebius (p : ℕ) : ℝ) ^ 2 / (((p : ℕ).totient : ℝ)) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum (p : ℕ) n).re := by
        rw [pow_one]
      rw [h0, h1]
      simpa using ramWeightLocalFactor357 n (p : ℕ) hp
    · intro e he
      rw [Finset.mem_range, not_lt] at he
      exact hvan e he
  have hprod : (∏' p : Nat.Primes, ∑' e : ℕ,
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ e))
      = ∑' q : ℕ, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
          (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) q := by
    exact EulerProduct.eulerProduct_tprod hone hmul hsumm hzero
  have hmain : HasSum (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
      (q.totient : ℝ) ^ 2 * (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)
      (∏' p : Nat.Primes, ∑' e : ℕ,
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ((p : ℕ) ^ e)) := by
    rw [hprod]
    exact hsumm.of_norm.hasSum
  rw [funext hloc] at hmain
  exact hmain


set_option maxHeartbeats 1000000 in
/-- LEAF. Step 2 of 3: the truncated sum against the finite product of local
factors. The finite Ramanujan sum over the moduli from one to N to the one tenth
differs from the product over the primes up to N to the one tenth of the local
factor 1 plus 1 over p minus 1 at a prime dividing n and 1 minus the inverse
square of p minus 1 at a prime not dividing n, by at most an absolute constant
times N to the minus one hundredth. The content is the divisor expansion of the
Ramanujan sum, which makes the squarefree weight multiplicative, together with
the bound on the squarefree moduli beyond the cut off. The saving one hundredth
is far weaker than the one tenth power of the cut off that the argument leaves
free. -/
theorem truncated_sum_euler_error357 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n -
          (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  classical
  obtain ⟨C1, hC1pos, hC1⟩ := divisorBound357
  refine ⟨1376 * C1 ^ 2, by positivity, 1024, ?_⟩
  intro N hN n hn2 hnN hev
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  set x : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hxdef
  set s : Finset ℕ := (Finset.Icc 1 x).filter Nat.Prime with hsdef
  have hNR : (1025 : ℝ) ≤ (N : ℝ) := by
    have h : (1025 : ℕ) ≤ N := by omega
    exact_mod_cast h
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hx2 : 2 ≤ x := by
    have h1024 : (1024 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) := by
      rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num]
      rw [← Real.rpow_natCast (2 : ℝ) 10]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show ((10 : ℕ) : ℝ) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hstep : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := h1024.symm
        _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    exact Nat.le_floor hstep
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxhalf : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (x : ℝ) := by
    have hstep : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      have h1024 : (1024 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) := by
        rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num]
        rw [← Real.rpow_natCast (2 : ℝ) 10]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [show ((10 : ℕ) : ℝ) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := h1024.symm
        _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    have h3 : (N : ℝ) ^ (1 / 10 : ℝ) < (x : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hxle : (x : ℝ) ≤ (N : ℝ) := by
    have h3 : (x : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (le_of_lt (by positivity : (0:ℝ) < (N:ℝ) ^ (1 / 10 : ℝ)))
    have h4 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) := by
      have h := (Real.rpow_le_rpow_left_iff (by linarith : (1:ℝ) < (N:ℝ)) :
        (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) ↔ (1 / 10 : ℝ) ≤ 1).mpr (by norm_num)
      simpa using h
    linarith
  have hlogx : Real.log (x : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hxpos hxle
  -- the truncated sum is the sum over `1 ≤ q ≤ x` of the weight
  have hA : truncatedSingular357 N n
      = ∑ q ∈ Finset.Icc 1 x,
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) q := by
    show (∑ q ∈ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re = _
    rw [← hxdef, Complex.re_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  -- the product is the sum over the `x`-smooth numbers
  have hprodeq : (∏ p ∈ s, (if p ∣ n then 1 + 1 / ((p : ℝ) - 1)
        else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      = ∑' m : ↑(Nat.factoredNumbers s),
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m := by
    rw [Finset.prod_congr rfl (fun p hp =>
      (ramWeightLocalTsum357 n p hn1 (Finset.mem_filter.mp hp).2).symm)]
    have h := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers
      (f := fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)
      (ramWeightOne357 n) (fun {a b} hab => ramWeightCoprime357 n hn1 hab)
      (ramWeightSummable357 n hn1) s
    have hs' : s.filter Nat.Prime = s :=
      Finset.filter_true_of_mem (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [hs'] at h
    exact h
  have hSf : Summable (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
      (q.totient : ℝ) ^ 2 * (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) :=
    (ramWeightSummable357 n hn1).of_norm
  -- the two complementary pieces
  have hsplitA := hSf.sum_add_tsum_subtype_compl (Finset.Icc 1 x)
  have hsplitB := hSf.tsum_subtype_add_tsum_subtype_compl (Nat.factoredNumbers s)
  -- membership: `1 ≤ m ≤ x` implies `x`-smooth
  have hmem : ∀ m : ℕ, 1 ≤ m → m ≤ x → m ∈ Nat.factoredNumbers s := by
    intro m hm1 hmx
    rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    have hpl : p ≤ m := Nat.le_of_dvd (by omega) hpd
    simp only [hsdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  -- the complement of the truncated range
  have hkeyA : ∀ m : ℕ, m ∉ Finset.Icc 1 x →
      ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ =
      (if x < m then ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ else 0) := by
    intro m hm
    by_cases hxm : x < m
    · rw [if_pos hxm]
    · rw [if_neg hxm]
      have hm0 : m = 0 := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hm
        omega
      subst hm0
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
  -- the complement of the smooth numbers
  have hkeyB : ∀ m : ℕ, m ∉ Nat.factoredNumbers s →
      ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ =
      (if x < m then ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ else 0) := by
    intro m hm
    by_cases hxm : x < m
    · rw [if_pos hxm]
    · rw [if_neg hxm]
      have hm0 : m = 0 := by
        by_contra hne
        exact hm (hmem m (by omega) (by omega))
      subst hm0
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
  have hboundA := ramWeightSubtypeLe357 n x hn1 {m : ℕ | m ∉ Finset.Icc 1 x}
    (fun m hm => hkeyA m hm)
  have hboundB := ramWeightSubtypeLe357 n x hn1 (Nat.factoredNumbers s)ᶜ
    (fun m hm => hkeyB m hm)
  have htail := ramWeightTailLe357 n x hn1 (by omega)
  -- the difference
  have hD : (∑ q ∈ Finset.Icc 1 x,
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) q)
      - (∑' m : ↑(Nat.factoredNumbers s),
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)
      = (∑' m : ↑(Nat.factoredNumbers s)ᶜ,
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)
        - (∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m) := by
    linarith [hsplitA, hsplitB]
  have hD2 : (n.divisors.card : ℝ) ≤ C1 * (n : ℝ) ^ (1 / 50 : ℝ) := hC1 n hn0
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hlogN : Real.log (N : ℝ) ≤ 40 * (N : ℝ) ^ (1 / 40 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hNpos) (show (0:ℝ) < 1/40 by norm_num)
    calc Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) / (1 / 40 : ℝ) := h
      _ = 40 * (N : ℝ) ^ (1 / 40 : ℝ) := by
          rw [div_eq_mul_inv, show ((1:ℝ)/40)⁻¹ = 40 by norm_num]
          ring
  -- the numerical chain, with a factor two
  have hchain : 2 * (4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)))
      ≤ 1376 * C1 ^ 2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
    have hnum : (6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2
        ≤ (6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ)) := by
      have hD2' : (n.divisors.card : ℝ) ^ 2 ≤ C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ) := by
        have h1 : (n.divisors.card : ℝ) ^ 2 ≤ (C1 * (n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hD2 2
        have h2 : (C1 * (n : ℝ) ^ (1 / 50 : ℝ)) ^ 2
            = C1 ^ 2 * ((n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 := by ring
        have h3 : ((n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 50 : ℝ)) 2]
          rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
          congr 1
          norm_num
        have hnn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have h4 : (n : ℝ) ^ (1 / 25 : ℝ) ≤ (N : ℝ) ^ (1 / 25 : ℝ) :=
          Real.rpow_le_rpow (le_of_lt hnn0) hnN (by norm_num)
        rw [h2, h3] at h1
        nlinarith [hC1pos]
      have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      have h6log : 0 ≤ 6 + 2 * Real.log (x : ℝ) := by
        have := Real.log_nonneg hx1
        linarith
      have h6log' : 6 + 2 * Real.log (x : ℝ) ≤ 6 + 2 * Real.log (N : ℝ) := by linarith
      have hY2 : (0 : ℝ) ≤ 6 + 2 * Real.log (N : ℝ) := by
        have := Real.log_nonneg hN1
        linarith
      exact mul_le_mul h6log' hD2' (by positivity) hY2
    have hinv : 1 / (x : ℝ) ≤ 2 / (N : ℝ) ^ (1 / 10 : ℝ) := by
      rw [div_le_div_iff₀ hxpos (by positivity)]
      have hP : (0:ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by positivity
      nlinarith
    have h1 : 2 * (4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)))
        = 8 * (((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2) *
            (1 / (x : ℝ))) := by ring
    rw [h1]
    have h2 : 8 * (((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2) * (1 / (x : ℝ)))
        ≤ 8 * (((6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ))) *
          (2 / (N : ℝ) ^ (1 / 10 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hY : (0 : ℝ) ≤ (6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ)) := by
        have hlog0 := Real.log_nonneg hN1
        have hC1s : (0 : ℝ) ≤ C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ) := by positivity
        nlinarith
      exact mul_le_mul hnum hinv (by positivity) hY
    refine h2.trans ?_
    have h3 : 8 * (((6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ))) *
        (2 / (N : ℝ) ^ (1 / 10 : ℝ)))
        = 16 * C1 ^ 2 * ((6 + 2 * Real.log (N : ℝ)) * ((N : ℝ) ^ (1 / 25 : ℝ) *
            (N : ℝ) ^ (-(1 / 10 : ℝ)))) := by
      rw [show (2 / (N : ℝ) ^ (1 / 10 : ℝ)) = 2 * (N : ℝ) ^ (-(1 / 10 : ℝ)) by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        ring]
      ring
    rw [h3]
    have h4 : (N : ℝ) ^ (1 / 25 : ℝ) * (N : ℝ) ^ (-(1 / 10 : ℝ))
        = (N : ℝ) ^ (-(1 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      norm_num
    rw [h4]
    have h5 : (16 : ℝ) * C1 ^ 2 * ((6 + 2 * Real.log (N : ℝ)) *
        ((N : ℝ) ^ (-(1 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 100 : ℝ))))
        = ((16 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))) *
            (N : ℝ) ^ (-(1 / 100 : ℝ))) * C1 ^ 2 := by ring
    rw [h5]
    have h6 : 16 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1376 := by
      have hB : (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN1 (by norm_num))
      have hC : (N : ℝ) ^ (-(1 / 40 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN1 (by norm_num))
      have hD' : (N : ℝ) ^ (1 / 40 : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          = (N : ℝ) ^ (-(1 / 40 : ℝ)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
      have step1 : 16 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          ≤ 16 * (6 + 2 * (40 * (N : ℝ) ^ (1 / 40 : ℝ))) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
        have hpos : (0:ℝ) ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) := by positivity
        nlinarith [hlogN, hpos]
      refine step1.trans ?_
      rw [show 16 * (6 + 2 * (40 * (N : ℝ) ^ (1 / 40 : ℝ))) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          = 96 * (N : ℝ) ^ (-(1 / 20 : ℝ)) +
            1280 * ((N : ℝ) ^ (1 / 40 : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))) by ring]
      rw [hD']
      nlinarith [hB, hC]
    have h7 : (0:ℝ) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := by positivity
    have h8 : (0:ℝ) ≤ C1 ^ 2 := by positivity
    calc (16 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))) *
          (N : ℝ) ^ (-(1 / 100 : ℝ)) * C1 ^ 2
        ≤ 1376 * (N : ℝ) ^ (-(1 / 100 : ℝ)) * C1 ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ h8
          exact mul_le_mul_of_nonneg_right h6 h7
      _ = 1376 * C1 ^ 2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by ring
  -- conclusion
  have hX : |∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m|
      ≤ 4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)) := by
    rw [← Real.norm_eq_abs]
    exact hboundA.trans htail
  have hY : |∑' m : ↑(Nat.factoredNumbers s)ᶜ,
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m|
      ≤ 4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)) := by
    rw [← Real.norm_eq_abs]
    exact hboundB.trans htail
  rw [hA, hprodeq, hD, abs_sub_comm]
  calc |(∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)
      - (∑' m : ↑(Nat.factoredNumbers s)ᶜ,
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)|
      = |(∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)
        + (-(∑' m : ↑(Nat.factoredNumbers s)ᶜ,
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m))| := by ring_nf
    _ ≤ |(∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)|
        + |-(∑' m : ↑(Nat.factoredNumbers s)ᶜ,
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)| := abs_add_le _ _
    _ = |(∑' m : {m : ℕ // m ∉ Finset.Icc 1 x},
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)|
        + |(∑' m : ↑(Nat.factoredNumbers s)ᶜ,
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)| := by rw [abs_neg]
    _ ≤ 4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)) +
        4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ)) :=
        add_le_add hX hY
    _ = 2 * (4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ))) := by ring
    _ ≤ 1376 * C1 ^ 2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := hchain

set_option maxHeartbeats 1000000 in
/-- LEAF. Step 3 of 3: the finite product against the full series. The product
over the primes up to N to the one tenth of the same local factors differs from
the sum of the full Ramanujan weight series by at most an absolute constant
times N to the minus one hundredth. The content is that every local factor is at
most 1 plus the reciprocal square of p minus 1, so the product over the primes
beyond the cut off differs from one by at most the tail of those reciprocal
squares, which is the fourth leaf below. -/
theorem prime_product_series_tail357 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |(∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
            (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
          (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  classical
  obtain ⟨C1, hC1pos, hC1⟩ := divisorBound357
  refine ⟨688 * C1 ^ 2, by positivity, 1024, ?_⟩
  intro N hN n hn2 hnN hev
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  set x : ℕ := ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ with hxdef
  set s : Finset ℕ := (Finset.Icc 1 x).filter Nat.Prime with hsdef
  have hNR : (1025 : ℝ) ≤ (N : ℝ) := by
    have h : (1025 : ℕ) ≤ N := by omega
    exact_mod_cast h
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hx2 : 2 ≤ x := by
    have h1024 : (1024 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) := by
      rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num]
      rw [← Real.rpow_natCast (2 : ℝ) 10]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show ((10 : ℕ) : ℝ) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hstep : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := h1024.symm
        _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    exact Nat.le_floor hstep
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxhalf : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (x : ℝ) := by
    have hstep : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      have h1024 : (1024 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) := by
        rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num]
        rw [← Real.rpow_natCast (2 : ℝ) 10]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [show ((10 : ℕ) : ℝ) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := h1024.symm
        _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    have h3 : (N : ℝ) ^ (1 / 10 : ℝ) < (x : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hxle : (x : ℝ) ≤ (N : ℝ) := by
    have h3 : (x : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (le_of_lt (by positivity : (0:ℝ) < (N:ℝ) ^ (1 / 10 : ℝ)))
    have h4 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) := by
      have h := (Real.rpow_le_rpow_left_iff (by linarith : (1:ℝ) < (N:ℝ)) :
        (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) ↔ (1 / 10 : ℝ) ≤ 1).mpr (by norm_num)
      simpa using h
    linarith
  have hlogx : Real.log (x : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hxpos hxle
  -- the product equals the sum over the `x`-smooth numbers
  have hprodeq : (∏ p ∈ s, (if p ∣ n then 1 + 1 / ((p : ℝ) - 1)
        else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      = ∑' m : ↑(Nat.factoredNumbers s),
          (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m := by
    rw [Finset.prod_congr rfl (fun p hp =>
      (ramWeightLocalTsum357 n p hn1 (Finset.mem_filter.mp hp).2).symm)]
    have h := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers
      (f := fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)
      (ramWeightOne357 n) (fun {a b} hab => ramWeightCoprime357 n hn1 hab)
      (ramWeightSummable357 n hn1) s
    have hs' : s.filter Nat.Prime = s :=
      Finset.filter_true_of_mem (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [hs'] at h
    exact h
  -- split off the non-smooth part
  have hSf : Summable (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
      (q.totient : ℝ) ^ 2 * (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) :=
    (ramWeightSummable357 n hn1).of_norm
  have hsplit := hSf.tsum_subtype_add_tsum_subtype_compl (Nat.factoredNumbers s)
  have hkey : ∀ m : ℕ, m ∉ Nat.factoredNumbers s →
      ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ =
      (if x < m then ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
        (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) m‖ else 0) := by
    intro m hm
    by_cases hxm : x < m
    · rw [if_pos hxm]
    · rw [if_neg hxm]
      have hm0 : m = 0 := by
        by_contra hne
        refine hm (Nat.mem_factoredNumbers'.mpr (fun p hp hpd => ?_))
        have hpl : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpd
        simp only [hsdef, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp.one_le, by omega⟩, hp⟩
      subst hm0
      simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]
  have hnormsum : Summable (fun m : ↑(Nat.factoredNumbers s)ᶜ =>
      ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖) :=
    (ramWeightSummable357 n hn1).subtype _
  have htailsumm : Summable (fun q : ℕ => if x < q then
      ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity)
      (fun q => by split_ifs <;> [exact le_rfl; positivity]) (ramWeightSummable357 n hn1)
  have hcompl : ‖∑' m : ↑(Nat.factoredNumbers s)ᶜ,
      (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖
      ≤ ∑' q : ℕ, if x < q then
          ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0 := by
    refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
    have heq : (∑' m : ↑(Nat.factoredNumbers s)ᶜ,
        ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖)
        = ∑' m : ↑(Nat.factoredNumbers s)ᶜ,
          (if x < (m : ℕ) then ‖(fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
            (q.totient : ℝ) ^ 2 *
            (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m‖ else 0) := by
      exact tsum_congr (fun m => hkey (m : ℕ) m.2)
    rw [heq]
    exact htailsumm.tsum_subtype_le
      (fun q : ℕ => if x < q then ‖(fun r : ℕ => (ArithmeticFunction.moebius r : ℝ) ^ 2 /
        (r.totient : ℝ) ^ 2 *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum r n).re) q‖ else 0)
      (Nat.factoredNumbers s)ᶜ (fun q => by split_ifs <;> positivity)
  -- the difference is the non-smooth part
  have hdiff : (∑' m : ↑(Nat.factoredNumbers s),
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m)
      - (∑' q : ℕ, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
          (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) q)
      = -(∑' m : ↑(Nat.factoredNumbers s)ᶜ,
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m) := by
    linarith [hsplit]
  -- the tail bound
  have htail := ramWeightTailLe357 n x hn1 (by omega)
  have hD : (n.divisors.card : ℝ) ≤ C1 * (n : ℝ) ^ (1 / 50 : ℝ) := hC1 n hn0
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hlogN : Real.log (N : ℝ) ≤ 40 * (N : ℝ) ^ (1 / 40 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hNpos) (show (0:ℝ) < 1/40 by norm_num)
    calc Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) / (1 / 40 : ℝ) := h
      _ = 40 * (N : ℝ) ^ (1 / 40 : ℝ) := by
          rw [div_eq_mul_inv, show ((1:ℝ)/40)⁻¹ = 40 by norm_num]
          ring
  -- numerator bound
  have hnum : (6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2
      ≤ (6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ)) := by
    have hD2 : (n.divisors.card : ℝ) ^ 2 ≤ C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ) := by
      have h1 : (n.divisors.card : ℝ) ^ 2 ≤ (C1 * (n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
        exact pow_le_pow_left₀ h0 hD 2
      have h2 : (C1 * (n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 = C1 ^ 2 * ((n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 := by
        ring
      have h3 : ((n : ℝ) ^ (1 / 50 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 25 : ℝ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 50 : ℝ)) 2]
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
        congr 1
        norm_num
      have hnn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have h4 : (n : ℝ) ^ (1 / 25 : ℝ) ≤ (N : ℝ) ^ (1 / 25 : ℝ) :=
        Real.rpow_le_rpow (le_of_lt hnn0) hnN (by norm_num)
      rw [h2, h3] at h1
      nlinarith [hC1pos]
    have h6log : 0 ≤ 6 + 2 * Real.log (x : ℝ) := by
      have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      have := Real.log_nonneg hx1
      linarith
    have h6log' : 6 + 2 * Real.log (x : ℝ) ≤ 6 + 2 * Real.log (N : ℝ) := by linarith
    have hY2 : (0 : ℝ) ≤ 6 + 2 * Real.log (N : ℝ) := by
      have := Real.log_nonneg hN1
      linarith
    exact mul_le_mul h6log' hD2 (by positivity) hY2
  -- reciprocal bound
  have hinv : 1 / (x : ℝ) ≤ 2 / (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [div_le_div_iff₀ hxpos (by positivity)]
    have h := hxhalf
    have hP : (0:ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by positivity
    nlinarith [hP]
  -- assemble the numerical chain
  have hchain : 4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ))
      ≤ 688 * C1 ^ 2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
    have h1 : 4 * ((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2 / (x : ℝ))
        = 4 * (((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2) * (1 / (x : ℝ))) := by
      ring
    rw [h1]
    have h2 : 4 * (((6 + 2 * Real.log (x : ℝ)) * (n.divisors.card : ℝ) ^ 2) * (1 / (x : ℝ)))
        ≤ 4 * (((6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ))) *
          (2 / (N : ℝ) ^ (1 / 10 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hY : (0 : ℝ) ≤ (6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ)) := by
        have hlog0 := Real.log_nonneg hN1
        have hC1s : (0 : ℝ) ≤ C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ) := by positivity
        nlinarith
      exact mul_le_mul hnum hinv (by positivity) hY
    refine h2.trans ?_
    have h3 : 4 * (((6 + 2 * Real.log (N : ℝ)) * (C1 ^ 2 * (N : ℝ) ^ (1 / 25 : ℝ))) *
        (2 / (N : ℝ) ^ (1 / 10 : ℝ)))
        = 8 * C1 ^ 2 * ((6 + 2 * Real.log (N : ℝ)) * ((N : ℝ) ^ (1 / 25 : ℝ) *
            (N : ℝ) ^ (-(1 / 10 : ℝ)))) := by
      rw [show (2 / (N : ℝ) ^ (1 / 10 : ℝ)) = 2 * (N : ℝ) ^ (-(1 / 10 : ℝ)) by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        ring]
      ring
    rw [h3]
    have h4 : (N : ℝ) ^ (1 / 25 : ℝ) * (N : ℝ) ^ (-(1 / 10 : ℝ))
        = (N : ℝ) ^ (-(1 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      norm_num
    rw [h4]
    have h5 : (8 : ℝ) * C1 ^ 2 * ((6 + 2 * Real.log (N : ℝ)) *
        ((N : ℝ) ^ (-(1 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 100 : ℝ))))
        = ((8 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))) *
            (N : ℝ) ^ (-(1 / 100 : ℝ))) * C1 ^ 2 := by ring
    rw [h5]
    have h6 : 8 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 688 := by
      have hA : (0:ℝ) < (N : ℝ) ^ (1 / 40 : ℝ) := by positivity
      have hB : (N : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN1 (by norm_num))
      have hC : (N : ℝ) ^ (-(1 / 40 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (le_of_lt hNpos)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hN1 (by norm_num))
      have hD' : (N : ℝ) ^ (1 / 40 : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          = (N : ℝ) ^ (-(1 / 40 : ℝ)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
      have step1 : 8 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          ≤ 8 * (6 + 2 * (40 * (N : ℝ) ^ (1 / 40 : ℝ))) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
        have hpos : (0:ℝ) ≤ (N : ℝ) ^ (-(1 / 20 : ℝ)) := by positivity
        nlinarith [hlogN, hpos]
      refine step1.trans ?_
      rw [show 8 * (6 + 2 * (40 * (N : ℝ) ^ (1 / 40 : ℝ))) * (N : ℝ) ^ (-(1 / 20 : ℝ))
          = 48 * (N : ℝ) ^ (-(1 / 20 : ℝ)) +
            640 * ((N : ℝ) ^ (1 / 40 : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))) by ring]
      rw [hD']
      nlinarith [hB, hC]
    have h7 : (0:ℝ) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := by positivity
    have h8 : (0:ℝ) ≤ C1 ^ 2 := by positivity
    calc (8 * (6 + 2 * Real.log (N : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ))) *
          (N : ℝ) ^ (-(1 / 100 : ℝ)) * C1 ^ 2
        ≤ 688 * (N : ℝ) ^ (-(1 / 100 : ℝ)) * C1 ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ h8
          exact mul_le_mul_of_nonneg_right h6 h7
      _ = 688 * C1 ^ 2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by ring
  -- conclusion
  have hneg : (∏ p ∈ s, (if p ∣ n then 1 + 1 / ((p : ℝ) - 1)
        else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      - (∑' q : ℕ, (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 /
          (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) q)
      = -(∑' m : ↑(Nat.factoredNumbers s)ᶜ,
        (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) ↑m) := by
    rw [hprodeq]
    exact hdiff
  rw [hprodeq, hdiff, abs_neg]
  exact (hcompl.trans htail).trans hchain


/-- LEAF. Ingredient of step 3: the prime reciprocal square tail. Beyond some
point the sum of the reciprocal squares of p minus 1 over the primes larger than
N to the one tenth is at most twice the reciprocal of the integer cut off. This
is an elementary estimate on primes alone: it names no singular series, no
Ramanujan sum and no even integer, and it is the only place where the cut off is
compared with a convergent prime series. -/
theorem prime_reciprocal_square_tail357 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      (∑' p : Nat.Primes,
        if ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ < (p : ℕ) then
          1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤
        2 / ((⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ)) := by
  refine ⟨1024, ?_⟩
  intro N hN
  have hNR : (1025 : ℝ) ≤ (N : ℝ) := by
    have : (1025 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have h1024 : (1024 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num]
    rw [← Real.rpow_natCast (2 : ℝ) 10]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((10 : ℕ) : ℝ) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
  have hstep : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := h1024.symm
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hx : 2 ≤ ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ := Nat.le_floor hstep
  exact (primeTailTsumLe357 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).trans
    (primeTailNatLe357 _ hx)


/-- Assembly of `singular_tail357` from the leaves above: write the singular
series as the sum of the full Ramanujan weight series through step 1, insert the
finite product of local factors as an intermediate term, and bound the two
halves by step 2 and step 3, with the two constants added. No step uses
`singular_tail357` itself. -/
theorem singular_tail357_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨C1, hC1, N1, h1⟩ := truncated_sum_euler_error357
  obtain ⟨C2, hC2, N2, h2⟩ := prime_product_series_tail357
  refine ⟨C1 + C2, by positivity, max N1 N2, ?_⟩
  intro N hN n hn2 hnN hev
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos_nat : 0 < N := lt_of_le_of_lt (Nat.zero_le N1) hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hx : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := (Real.rpow_pos_of_pos hNpos _).le
  have hb1 := h1 N hN1 n hn2 hnN hev
  have hb2 := h2 N hN2 n hn2 hnN hev
  have hsum := singular_series_has_sum357 n hn2
  have htsum : (∑' q : ℕ,
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
        (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re) = singularSeries111 n :=
    hsum.tsum_eq
  rw [← htsum]
  calc
    |truncatedSingular357 N n -
        (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
          (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)|
        = |(truncatedSingular357 N n -
            (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))) +
            ((∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
              (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
                (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re))| := by
          congr 1
          ring
    _ ≤ |truncatedSingular357 N n -
            (∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2))| +
          |(∏ p ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊).filter Nat.Prime,
              (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
            (∑' q : ℕ, ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) *
              (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re)| :=
        abs_add_le _ _
    _ ≤ C1 * (N : ℝ) ^ (-(1 / 100 : ℝ)) + C2 * (N : ℝ) ^ (-(1 / 100 : ℝ)) :=
        add_le_add hb1 hb2
    _ = (C1 + C2) * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
        ring

end LeanLab.Linnik1951
