/-
P0069 R. C. Baker, G. Harman, J. Pintz 1997, The exceptional set for Goldbach's problem in short
intervals. Unit U-1518, run 20261025T1603Z-10248, track T1, type DECOMPOSE.

Splits the sieve bookkeeping in the proofs of three cited lemmas of Section 4 into small OPEN
leaves, checked against the page images of `papers/P0069-original.pdf`, book pages 26 to 30:

* Lemma 12, p. 26: the reduction "It now suffices to prove (4.10), (4.11), (4.12)" after
  Heath-Brown's truncation of the Moebius sum, `γ = x^{ε/12}`.
* Lemma 13, p. 28 to 30: `c_k = d_k - e_k` by (4.14), `d_k` by Lemma 12 through (4.9), `e_k`
  split at `p = x^{0.225}` into `e'_k` and `e''_k`; the case `N > x^{0.375}` by Lemma 4.
* Lemma 14, p. 30: `c_k = h_k - j_k` by (4.14), `h_k` by Lemma 12 through (4.8), `j_k` in the
  range `p < x^{1.1}/M² ≤ x^{0.18}` of Theorem 4.

The analytic inputs, the Theorem 4 and Lemma 4 transfers and the Lemma 10, 11 and Hildebrand
estimates behind (4.10) to (4.12), enter as named hypotheses of the assembly theorems; they are
not leaves. The assembly theorems have real proofs from the leaves and those hypotheses.

AI wrote this Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress
on it.
-/
import LeanLab.BakerHarmanPintz1997.Buchstab
import LeanLab.BakerHarmanPintz1997.SequenceAlgebra
import LeanLab.BakerHarmanPintz1997.MoebiusSieve
import LeanLab.BakerHarmanPintz1997.TailBound

namespace LeanLab.BakerHarmanPintz1997.Decomp1518
open Finset ArithmeticFunction
open LeanLab.BakerHarmanPintz1997
attribute [local instance] Classical.propDecidable

/-! ### Definitions of the auxiliary sums -/

/-- `j_k = Σ_{mnph = k, m ~ M, n ~ N, w ≤ p < z} a_m b_n ψ(h, p)`, the subtracted sum of (4.14)
applied to `conv2`, p. 28 for Lemma 13 and p. 30 for Lemma 14. -/
noncomputable def jsum (a b : ℕ → ℂ) (M N w z : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n *
      ∑ p ∈ (k / (m * n)).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        psi (k / (m * n) / p) (p : ℝ)
    else 0

/-- The truncated Moebius sum `Σ_{d | l, d | P(w), d < γ} μ(d)`, p. 26. -/
noncomputable def psiTrunc (l : ℕ) (w γ : ℝ) : ℂ :=
  ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (moebius d : ℂ)

/-- The error count `Σ_{d | l, d | P(w), γ ≤ d < γw} 1`, p. 26. -/
noncomputable def psiErr (l : ℕ) (w γ : ℝ) : ℝ :=
  (((siftingProduct w).divisors.filter
    (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ)

/-- `c'_k = Σ_{mnl = k} a_m b_n Σ_{d | l, d | P(w), d < γ} μ(d)`, p. 26. -/
noncomputable def conv2T (a b : ℕ → ℂ) (M N w γ : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n * psiTrunc (k / (m * n)) w γ else 0

/-- `c''_k = Σ† |a_m b_n|`, `†` meaning `d | P(w)`, `γ ≤ d < wγ`, `d | l`, `mnl = k`, p. 26. -/
noncomputable def conv2E (a b : ℕ → ℂ) (M N w γ : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then ‖a m‖ * ‖b n‖ * psiErr (k / (m * n)) w γ else 0

/-! ### OPEN leaves -/

/-- (4.14), p. 27, summed over `m ~ M`, `n ~ N`: for `k ≥ 1` and `w ≤ z`,
`Σ a_m b_n ψ(l, z) = Σ a_m b_n ψ(l, w) - Σ_{w ≤ p < z} a_m b_n ψ(h, p)`, the first display of
the proofs of Lemma 13, p. 28, and Lemma 14, p. 30. Unit U-1518. -/
theorem conv2_buchstab (a b : ℕ → ℂ) (M N : ℝ) {w z : ℝ} {k : ℕ} (hk : 0 < k) (hwz : w ≤ z) :
    conv2 a b M N z k = conv2 a b M N w k - jsum a b M N w z k := by
  simp only [conv2, jsum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  by_cases hd : m * n ∣ k
  · simp only [if_pos hd]
    rw [buchstab_identity (Nat.div_pos (Nat.le_of_dvd hk hd) (by
      have : m * n ≠ 0 := by intro he; simp [he] at hd; omega
      omega)) hwz]
    ring
  · simp [hd]

/-- Splitting the range `w ≤ p < z` of `j_k` at `t`, as (4.19) splits `e_k` at `x^{0.225}`,
p. 28 to 30: `[w, z) = [w, min(z,t)) ∪ [t, max(z,t))` for `w ≤ t`. Unit U-1518. -/
theorem jsum_split_min_max (a b : ℕ → ℂ) (M N : ℝ) {w z t : ℝ} (k : ℕ) (hwz : w ≤ z)
    (hwt : w ≤ t) :
    jsum a b M N w z k = jsum a b M N w (min z t) k + jsum a b M N t (max z t) k := by
  simp only [jsum, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  by_cases hd : m * n ∣ k
  · simp only [if_pos hd, ← mul_add]
    congr 1
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases hzt : z ≤ t
    · simp only [min_eq_left hzt, max_eq_right hzt]
      have hfalse : ¬ (t ≤ (p : ℝ) ∧ (p : ℝ) < t) := by rintro ⟨ha, hb⟩; linarith
      simp [hfalse]
    · have htz : t ≤ z := le_of_not_ge hzt
      simp only [min_eq_right htz, max_eq_left htz]
      by_cases hpt : (p : ℝ) < t
      · simp [hpt, not_le.mpr hpt, hpt.trans_le htz]
      · have htp : t ≤ (p : ℝ) := le_of_not_gt hpt
        simp [hpt, htp, hwt.trans htp]
  · simp [hd]


/-- (4.2) depends only on `c_k` for `k ≥ 1` and large `x`: the sums in (4.2) run over
`k ∈ I` and `k ∈ I₁`, all positive. Unit U-1518. -/
theorem holds42_congr_ev {ε : ℝ} {c d : ℝ → ℕ → ℂ}
    (hcd : Ev fun x => ∀ k : ℕ, 0 < k → c x k = d x k) (hc : Holds42 ε c) : Holds42 ε d := by
  obtain ⟨X, hX⟩ := hcd
  intro A hA
  obtain ⟨C, X0, hC⟩ := hc A hA
  refine ⟨C, max X X0, fun x hx q hq hqA χ => ?_⟩
  have heq : ∀ S : Finset ℕ, (∀ k ∈ S, 0 < k) →
      (∑ k ∈ S, d x k * χ (k : ZMod q)) = ∑ k ∈ S, c x k * χ (k : ZMod q) := by
    intro S hS
    apply sum_congr rfl
    intro k hk
    rw [hX x ((le_max_left _ _).trans hx) k (hS k hk)]
  rw [heq (Iset ε x) (fun k hk => by have := (mem_Ioc.mp hk).1; omega),
    heq (Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊) (fun k hk => by have := (mem_Ioc.mp hk).1; omega)]
  exact hC x ((le_max_right _ _).trans hx) q hqA χ


/-- Lemma 12, p. 26, with its range condition (4.8) or (4.9) required only for large `x`, the
form in which the proofs of Lemmas 13 and 14 use it. Unit U-1518. -/
theorem lemma12_ev (h : Lemma12) : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    Sieve42 ε fun M N z => (∀ x, z x = wof x) ∧
      Ev (fun x => max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun ε hε hε0 B a b M N z ha hb hcond => ?_⟩
  obtain ⟨hz, X, hX⟩ := hcond
  let M' : ℝ → ℝ := fun x => if X ≤ x then M x else x ^ (0.46 + ε / 8)
  let N' : ℝ → ℝ := fun x => if X ≤ x then N x else x ^ (0.46 + ε / 8)
  have hc : Holds42 ε fun x k => conv2 (a x) (b x) (M' x) (N' x) (wof x) k := by
    apply h ε hε hε0 B a b M' N' wof ha hb
    intro x
    refine ⟨rfl, ?_⟩
    by_cases hx : X ≤ x
    · simpa [M', N', hx] using hX x hx
    · exact Or.inr (by simp [M', N', hx])
  apply holds42_congr_ev (c := fun x k => conv2 (a x) (b x) (M' x) (N' x) (wof x) k) _ hc
  exact ⟨X, fun x hx k _ => by simp [M', N', hx, hz x]⟩


/-- Lemma 14, p. 30, "The case (4.6) of Lemma 12 covers `h_k`": (4.22) gives (4.8),
`max(x^{0.45}, M) max(x^{0.225}, N) ≤ x^{0.775}`, for `x ≥ 1`. Unit U-1518. -/
theorem cond422_range48 {x M N : ℝ} (hx : 1 ≤ x) (hM : x ^ (0.46 : ℝ) < M)
    (hM' : M ≤ x ^ (0.5 : ℝ)) (hMN : M * N ≤ x ^ (0.775 : ℝ)) :
    max (x ^ (0.45 : ℝ)) M * max (x ^ (0.225 : ℝ)) N ≤ x ^ (0.775 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [max_eq_right ((Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (0.45 : ℝ) ≤ 0.46)).trans hM.le)]
  rcases le_total N (x ^ (0.225 : ℝ)) with hN | hN
  · rw [max_eq_left hN]
    calc M * x ^ (0.225 : ℝ) ≤ x ^ (0.5 : ℝ) * x ^ (0.225 : ℝ) :=
        mul_le_mul_of_nonneg_right hM' (Real.rpow_nonneg hx0.le _)
      _ = x ^ (0.725 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  · rwa [max_eq_right hN]

/-- Lemma 14, p. 30: in `j_k`, `p < z ≤ x^{1.1}/M² < x^{0.18}` from `zM² ≤ x^{1.1}` and
`M > x^{0.46}`. Unit U-1518. -/
theorem cond422_z_le {x M z : ℝ} (hx : 0 < x) (hM : x ^ (0.46 : ℝ) < M)
    (hz : z * M ^ 2 ≤ x ^ (1.1 : ℝ)) : z ≤ x ^ (0.18 : ℝ) := by
  have hxp : 0 < x ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hx _
  have hM0 : 0 < M := hxp.trans hM
  have hsq : x ^ (0.92 : ℝ) < M ^ 2 := by
    have heq : x ^ (0.92 : ℝ) = (x ^ (0.46 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    rw [heq]
    nlinarith
  have hid : x ^ (1.1 : ℝ) = x ^ (0.18 : ℝ) * x ^ (0.92 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have hp : 0 < x ^ (0.18 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [hid] at hz
  nlinarith


/-- Lemma 13, p. 28, "Lemma 12 covers `d_k`": (4.18) gives (4.9),
`max(M, N) ≤ x^{0.46+ε/8}`, for `x ≥ 1`, `ε ≥ 0`. Unit U-1518. -/
theorem cond418_range49 {x M N ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) (hM : M ≤ x ^ (0.46 : ℝ))
    (hN : N ≤ x ^ (0.46 : ℝ)) : max M N ≤ x ^ (0.46 + ε / 8) := by
  apply le_trans (max_le hM hN)
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- `w = exp(log^{9/10} x) ≤ x^c` for large `x`, any fixed `c > 0`; used with `c = 0.225` to
split `e_k` at (4.19), p. 28. Unit U-1518. -/
theorem wof_le_rpow_ev (c : ℝ) (hc : 0 < c) : Ev fun x => wof x ≤ x ^ c := by
  refine ⟨Real.exp (max 1 ((1 / c) ^ (10 : ℝ))), fun x hx => ?_⟩
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl : max 1 ((1 / c) ^ (10 : ℝ)) ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  have hl1 : 1 ≤ Real.log x := (le_max_left _ _).trans hl
  have hlpos : 0 < Real.log x := zero_lt_one.trans_le hl1
  have hroot : 1 / c ≤ Real.log x ^ (0.1 : ℝ) := by
    have heq : ((1 / c) ^ (10 : ℝ)) ^ (0.1 : ℝ) = 1 / c := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    rw [← heq]
    exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hl) (by norm_num)
  have hmul : 1 ≤ c * Real.log x ^ (0.1 : ℝ) := by
    have := (div_le_iff₀ hc).mp hroot
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hmul
    (Real.rpow_nonneg hlpos.le (0.9 : ℝ))
  have hid : Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hlpos]; norm_num
  change Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ x ^ c
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  norm_num at hprod ⊢
  nlinarith [hid]


/-- Lemma 13, p. 30: "`e''_k` runs over primes `h` since `mnp³ ≥ mp³ > x`". If `m > x^{0.4}`,
`p > x^{0.225}`, `n ≥ 1`, `mnph ≤ x`, `h ≥ 2` and `h` has no prime factor below `p`, then `h`
is prime. Unit U-1518. -/
theorem e2_cofactor_prime {x : ℝ} {m n p h : ℕ} (hx : 1 ≤ x) (hm : x ^ (0.4 : ℝ) < m)
    (hp : x ^ (0.225 : ℝ) < p) (hn : 1 ≤ n) (hk : ((m * n * p * h : ℕ) : ℝ) ≤ x) (hh : 2 ≤ h)
    (hr : Rough h p) : h.Prime := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hm0 : 0 < (m : ℝ) := (Real.rpow_pos_of_pos hx0 _).trans hm
  have hp0 : 0 < (p : ℝ) := (Real.rpow_pos_of_pos hx0 _).trans hp
  apply prime_of_rough_of_lt_sq hh (by positivity) _ hr
  by_contra hs
  have hs : (p : ℝ) ^ 2 ≤ h := le_of_not_gt hs
  have hpower : x ^ (1.075 : ℝ) < (m : ℝ) * (p : ℝ) ^ 3 := by
    rw [show (1.075 : ℝ) = 0.4 + 0.225 * 3 by norm_num,
      Real.rpow_add hx0, Real.rpow_mul hx0.le, Real.rpow_ofNat]
    gcongr
  have hbound : (m : ℝ) * (p : ℝ) ^ 3 ≤ (m : ℝ) * n * p * h := by
    calc (m : ℝ) * (p : ℝ) ^ 3 = ((m : ℝ) * p) * (p : ℝ) ^ 2 := by ring
      _ ≤ ((m : ℝ) * p) * h := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (m : ℝ) * 1 * p * h := by ring
      _ ≤ _ := by gcongr; exact_mod_cast hn
  have hxx : x ≤ x ^ (1.075 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 1.075)
  push_cast at hk
  linarith


/-- Heath-Brown [11], Lemma 15, as quoted on p. 26, in the exact form: for `γ > 1`,
`|Σ_{d | l, d | P(w), d ≥ γ} μ(d)| ≤ #{d | l, d | P(w), γ ≤ d < γw}`. Group the `d ≥ γ` by the
shortest product of their largest primes that reaches `γ`. Unit U-1518. -/
theorem moebius_tail_le (l : ℕ) (w : ℝ) {γ : ℝ} (hγ : 1 < γ) :
    ‖∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ γ ≤ (d : ℝ), (moebius d : ℂ)‖ ≤
      psiErr l w γ := by
  let G := Nat.gcd (siftingProduct w) l
  have hG : G ≠ 0 := by
    intro h
    exact siftingProduct_ne_zero w ((Nat.gcd_eq_zero_iff.mp h).1)
  have hcommon : (siftingProduct w).divisors.filter (fun d => d ∣ l) = G.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, G]
    constructor
    · rintro ⟨⟨hd, _⟩, hl⟩
      exact ⟨⟨hd, hl⟩, hG⟩
    · rintro ⟨⟨hd, hl⟩, _⟩
      exact ⟨⟨hd, siftingProduct_ne_zero w⟩, hl⟩
  have hprimes : (siftingProduct w).primeFactors = primesBelow w :=
    Nat.primeFactors_prod (fun p hp => (mem_primesBelow.mp hp).1)
  have hsq : Squarefree G := by
    apply Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left (siftingProduct w) l)
    apply moebius_ne_zero_iff_squarefree.mp
    rw [siftingProduct, moebius_prime_product _ (fun p hp => (mem_primesBelow.mp hp).1)]
    exact pow_ne_zero _ (by norm_num)
  have hprod : (∏ p ∈ G.primeFactors, p) = G := Nat.prod_primeFactors_of_squarefree hsq
  have hP : ∀ p ∈ G.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hPw : ∀ p ∈ G.primeFactors, 1 ≤ p ∧ (p : ℝ) < w := by
    intro p hp
    refine ⟨(hP p hp).one_le, ?_⟩
    have hd : p ∣ siftingProduct w := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_left _ _)
    have hm := (hP p hp).mem_primeFactors hd (siftingProduct_ne_zero w)
    rw [hprimes] at hm
    exact (mem_primesBelow.mp hm).2
  have htail : (∑ d ∈ G.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), (moebius d : ℂ)) =
      ∑ T ∈ G.primeFactors.powerset,
        if γ ≤ ((∏ p ∈ T, p : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0 := by
    rw [sum_filter]
    nth_rw 1 [← hprod]
    rw [sum_divisors_prime_product _ hP]
    apply sum_congr rfl
    intro T hT
    rw [moebius_prime_product T (fun p hp => hP p ((mem_powerset.mp hT) hp))]
    push_cast
    rfl
  have hcount : ((G.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) =
      ∑ T ∈ G.primeFactors.powerset, if γ ≤ ((∏ p ∈ T, p : ℕ) : ℝ) ∧
        ((∏ p ∈ T, p : ℕ) : ℝ) < γ * w then (1 : ℝ) else 0 := by
    have he := sum_divisors_prime_product G.primeFactors hP
      (fun d => if γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w then (1 : ℂ) else 0)
    rw [hprod] at he
    have hre := congrArg Complex.re he
    simpa using hre
  have htailset : (siftingProduct w).divisors.filter (fun d => d ∣ l ∧ γ ≤ (d : ℝ)) =
      G.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)) := by
    rw [← hcommon, filter_filter]
  have hcountset : (siftingProduct w).divisors.filter
      (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) =
      G.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) := by
    rw [← hcommon, filter_filter]
  rw [htailset, htail, psiErr, hcountset, hcount]
  exact powerset_tail_bound _ w hPw hγ


/-- A dominated difference of coefficients gives a dominated character sum, `|χ| ≤ 1`, p. 26,
the `O(Σ_{x-y<k≤x} c''_k)` term. Unit U-1518. -/
theorem norm_sum_sub_char_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (f g : ℕ → ℂ) (e : ℕ → ℝ) (h : ∀ k ∈ S, ‖f k - g k‖ ≤ e k) :
    ‖∑ k ∈ S, f k * χ (k : ZMod q) - ∑ k ∈ S, g k * χ (k : ZMod q)‖ ≤ ∑ k ∈ S, e k := by
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ k ∈ S, ‖f k * χ (k : ZMod q) - g k * χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      rw [← sub_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)).trans (h k hk)

/-- (4.11) used at `q = 1`, `χ = χ₀`: `Σ_{k ∈ I} c''_k ≤ (Y/y₁) Σ_{k ∈ I₁} c''_k + O(Y𝓛^{-A})`,
p. 26. Unit U-1518. -/
theorem holds42_real_upper {ε : ℝ} {e : ℝ → ℕ → ℝ} (h : Holds42 ε fun x k => (e x k : ℂ)) :
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∑ k ∈ Iset ε x, e x k ≤
        Yof ε x / y1 x * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, e x k + C * Yof ε x / L x ^ A := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  refine ⟨C, max X0 (Real.exp 1), fun x hx => ?_⟩
  have hxexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxexp
  have hlog : 1 ≤ L x := by
    simpa [L] using Real.log_le_log (Real.exp_pos 1) hxexp
  have he := hC x ((le_max_left _ _).trans hx) 1
    (by simpa using Real.one_le_rpow hlog hA.le) (1 : DirichletCharacter ℂ 1)
  have hχ : ∀ k : ℕ, (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 := by
    intro k
    apply MulChar.one_apply
    exact ⟨1, Subsingleton.elim _ _⟩
  simp only [hχ, mul_one] at he
  have hre := (Complex.re_le_norm _).trans he
  simp at hre
  linarith


/-! ### PROVED small facts -/

/-- `Y = x^{θ₁} ≥ 0` for `x ≥ 0`. Unit U-1518. -/
theorem Yof_nonneg (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Yof ε x := Real.rpow_nonneg hx _

/-- `y₁ = x exp(-3 log^{1/3} x) > 0` for `x > 0`, p. 24. Unit U-1518. -/
theorem y1_pos {x : ℝ} (hx : 0 < x) : 0 < y1 x := mul_pos hx (Real.exp_pos _)

/-- The Moebius sum over `d | l`, `d | P(w)` minus its truncation at `d < γ` is the tail
`d ≥ γ`; with `moebius_tail_le` this is Heath-Brown's Lemma 15 as used on p. 26:
`|ψ(l, w) - Σ_{d < γ} μ(d)| ≤ Σ_{γ ≤ d < γw} 1`. Unit U-1518. -/
theorem psi_sub_trunc_le (l : ℕ) (w : ℝ) {γ : ℝ} (hγ : 1 < γ) :
    ‖psi l w - psiTrunc l w γ‖ ≤ psiErr l w γ := by
  have hsplit : (∑ d ∈ (siftingProduct w).divisors with d ∣ l, (moebius d : ℂ)) =
      psiTrunc l w γ +
        ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ γ ≤ (d : ℝ), (moebius d : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      ((siftingProduct w).divisors.filter (fun d => d ∣ l)) (fun d => (d : ℝ) < γ)]
    simp only [Finset.filter_filter, not_lt, psiTrunc]
  rw [psi_eq_moebius_sum, hsplit, add_sub_cancel_left]
  exact moebius_tail_le l w hγ

/-- The pointwise bound `|c_k - c'_k| ≤ c''_k` behind the display "leading to" on p. 26, from
`psi_sub_trunc_le` and the triangle inequality, `γ > 1`. Unit U-1518. -/
theorem conv2_sub_trunc_le (a b : ℕ → ℂ) (M N w : ℝ) {γ : ℝ} (hγ : 1 < γ) (k : ℕ) :
    ‖conv2 a b M N w k - conv2T a b M N w γ k‖ ≤ conv2E a b M N w γ k := by
  simp only [conv2, conv2T, conv2E, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  by_cases hd : m * n ∣ k
  · simp only [ite_eq_left hd, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (psi_sub_trunc_le (k / (m * n)) w hγ) (by positivity)
  · simp [hd]



/-! ### ASSEMBLY: Lemma 12, the reduction to (4.10), (4.11), (4.12), p. 26 -/

/-- If `c'` satisfies (4.2), the nonnegative majorant `c''` satisfies (4.2), (4.11), and
`Σ_{k ∈ I₁} c''_k = O(y₁𝓛^{-A})`, (4.12), and `|c_k - c'_k| ≤ c''_k` for large `x`, then `c`
satisfies (4.2): "It now suffices to prove (4.10), (4.11), (4.12)", p. 26. Unit U-1518. -/
theorem holds42_of_dominated {ε : ℝ} {c c' : ℝ → ℕ → ℂ} {e : ℝ → ℕ → ℝ}
    (h410 : Holds42 ε c') (h411 : Holds42 ε fun x k => (e x k : ℂ))
    (h412 : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, e x k ≤ C * y1 x / L x ^ A)
    (hdom : Ev fun x => ∀ k : ℕ, ‖c x k - c' x k‖ ≤ e x k) : Holds42 ε c := by
  intro A hA
  obtain ⟨C1, X1, h1⟩ := h410 A hA
  obtain ⟨C2, X2, h2⟩ := h412 A hA
  obtain ⟨X3, h3⟩ := hdom
  obtain ⟨C4, X4, h4⟩ := holds42_real_upper h411 A hA
  refine ⟨C1 + C4 + 2 * C2, max (max X1 X2) (max X3 (max X4 1)), ?_⟩
  intro x hx q _ hq χ
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : X4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hxone : (1 : ℝ) ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have hy1 : 0 < y1 x := y1_pos hxpos
  have hr : 0 ≤ Yof ε x / y1 x := div_nonneg (Yof_nonneg ε hxpos.le) hy1.le
  have key : ∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) -
      ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q) =
      (∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q) -
        ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q)) +
      (∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) - ∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q)) -
      ((Yof ε x / y1 x : ℝ) : ℂ) *
        (∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q) -
          ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q)) := by ring
  rw [key]
  have hA1 := h1 x hx1 q hq χ
  have hB := norm_sum_sub_char_le χ (Iset ε x) (c x) (c' x) (e x) (fun k _ => h3 x hx3 k)
  have hC := norm_sum_sub_char_le χ (Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊) (c x) (c' x) (e x)
    (fun k _ => h3 x hx3 k)
  have hD := h4 x hx4
  have hE := h2 x hx2
  have hF : Yof ε x / y1 x * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, e x k ≤ C2 * Yof ε x / L x ^ A := by
    have e1 : Yof ε x / y1 x * (C2 * y1 x / L x ^ A) = C2 * Yof ε x / L x ^ A := by
      rw [show Yof ε x / y1 x * (C2 * y1 x / L x ^ A) =
        (Yof ε x / y1 x * y1 x) * C2 / L x ^ A by ring, div_mul_cancel₀ _ hy1.ne']
      ring
    calc Yof ε x / y1 x * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, e x k ≤
        Yof ε x / y1 x * (C2 * y1 x / L x ^ A) := mul_le_mul_of_nonneg_left hE hr
      _ = _ := e1
  have hnorm : ‖((Yof ε x / y1 x : ℝ) : ℂ) *
      (∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q) -
        ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q))‖ ≤
      Yof ε x / y1 x * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, e x k := by
    rw [norm_mul, Complex.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hC hr
  have htot : (C1 + C4 + 2 * C2) * Yof ε x / L x ^ A =
      C1 * Yof ε x / L x ^ A + C4 * Yof ε x / L x ^ A + 2 * (C2 * Yof ε x / L x ^ A) := by ring
  rw [htot]
  calc _ ≤ ‖(∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q) -
        ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q)) +
      (∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) - ∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q))‖ +
      ‖((Yof ε x / y1 x : ℝ) : ℂ) *
        (∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q) -
          ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q))‖ := norm_sub_le _ _
    _ ≤ _ := by
      have := norm_add_le (∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q) -
        ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c' x k * χ (k : ZMod q))
        (∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) - ∑ k ∈ Iset ε x, c' x k * χ (k : ZMod q))
      linarith

/-- Lemma 12, p. 26, reduced to (4.10), (4.11), (4.12) for the explicit `c'_k = conv2T` and
`c''_k = conv2E` at `z = w`, any cutoff `γ > 1`; the paper takes `γ = x^{ε/12}`. The three
inputs are the analytic content, from Lemmas 10, 11 and Hildebrand [13]. Unit U-1518. -/
theorem lemma12_of_410_411_412 {ε : ℝ} (a b : ℝ → ℕ → ℂ) (M N γ : ℝ → ℝ)
    (hγ : ∀ x, 1 < γ x)
    (h410 : Holds42 ε fun x k => conv2T (a x) (b x) (M x) (N x) (wof x) (γ x) k)
    (h411 : Holds42 ε fun x k => ((conv2E (a x) (b x) (M x) (N x) (wof x) (γ x) k : ℝ) : ℂ))
    (h412 : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, conv2E (a x) (b x) (M x) (N x) (wof x) (γ x) k ≤
        C * y1 x / L x ^ A) :
    Holds42 ε fun x k => conv2 (a x) (b x) (M x) (N x) (wof x) k :=
  holds42_of_dominated (e := fun x k => conv2E (a x) (b x) (M x) (N x) (wof x) (γ x) k)
    h410 h411 h412
    ⟨0, fun x _ k => conv2_sub_trunc_le (a x) (b x) (M x) (N x) (wof x) (hγ x) k⟩

/-! ### ASSEMBLY: Lemma 14, p. 30 -/

/-- Lemma 14, p. 30, for `z ≥ w`, from Lemma 12 in its eventual form and the Theorem 4 input
for `j_k` in the range of p. 30, `x^{0.46} < M ≤ x^{0.5}`, `MN ≤ x^{0.775}`, `zM² ≤ x^{1.1}`,
`w ≤ z ≤ x^{0.18}`. The paper uses `z ≥ w` without comment. Unit U-1518. -/
theorem lemma14_core {ε : ℝ}
    (h12 : Sieve42 ε fun M N z => (∀ x, z x = wof x) ∧
      Ev (fun x => max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)))
    (hJ : ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      Ev (fun x => x ^ (0.46 : ℝ) < M x ∧ M x ≤ x ^ (0.5 : ℝ) ∧ M x * N x ≤ x ^ (0.775 : ℝ) ∧
        z x * M x ^ 2 ≤ x ^ (1.1 : ℝ) ∧ wof x ≤ z x ∧ z x ≤ x ^ (0.18 : ℝ)) →
      Holds42 ε fun x k => jsum (a x) (b x) (M x) (N x) (wof x) (z x) k) :
    Sieve42 ε fun M N z => Cond422 M N z ∧ ∀ x, wof x ≤ z x := by
  intro B a b M N z ha hb hcond
  obtain ⟨⟨X1, hX1⟩, hw⟩ := hcond
  have hd : Holds42 ε fun x k => conv2 (a x) (b x) (M x) (N x) (wof x) k := by
    refine h12 B a b M N wof ha hb ⟨fun _ => rfl, max X1 1, fun x hx => Or.inl ?_⟩
    have h := hX1 x (le_trans (le_max_left _ _) hx)
    exact cond422_range48 (le_trans (le_max_right _ _) hx) h.1 h.2.1 h.2.2.1
  have hj := hJ B a b M N z ha hb ⟨max X1 1, fun x hx => by
    have h := hX1 x (le_trans (le_max_left _ _) hx)
    have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hw x, cond422_z_le hx0 h.1 h.2.2.2⟩⟩
  refine holds42_congr_ev ⟨0, fun x _ k hk => ?_⟩ (holds42_sub hd hj)
  simp only [Pi.sub_apply]
  exact (conv2_buchstab (a x) (b x) (M x) (N x) hk (hw x)).symm

/-- Lemma 14 for `z ≥ w`, CONDITIONAL ON Lemma 12 and the Theorem 4 input `hJ` of
`lemma14_core`. Unit U-1518. -/
theorem lemma14_of_lemma12 (h12 : Lemma12)
    (hJ : ∀ ε : ℝ, 0 < ε → ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      Ev (fun x => x ^ (0.46 : ℝ) < M x ∧ M x ≤ x ^ (0.5 : ℝ) ∧ M x * N x ≤ x ^ (0.775 : ℝ) ∧
        z x * M x ^ 2 ≤ x ^ (1.1 : ℝ) ∧ wof x ≤ z x ∧ z x ≤ x ^ (0.18 : ℝ)) →
      Holds42 ε fun x k => jsum (a x) (b x) (M x) (N x) (wof x) (z x) k) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      Sieve42 ε fun M N z => Cond422 M N z ∧ ∀ x, wof x ≤ z x := by
  obtain ⟨ε0, h0, h⟩ := lemma12_ev h12
  exact ⟨ε0, h0, fun ε he he0 => lemma14_core (h ε he he0) (hJ ε he)⟩

/-! ### ASSEMBLY: Lemma 13, pp. 28 to 30 -/

/-- Lemma 13, pp. 28 to 30, for `z ≥ w` and `N` eventually on one side of `x^{0.375}`: the case
`N > x^{0.375}` is the Lemma 4 input `hBig`; for `N ≤ x^{0.375}`, `c_k = d_k - e'_k - e''_k`
with `d_k` from Lemma 12 through (4.9), `e'_k` the part `p < x^{0.225}`, input `hE1`, and `e''_k`
the part `p ≥ x^{0.225}`, input `hE2`. Unit U-1518. -/
theorem lemma13_core {ε : ℝ} (hε : 0 ≤ ε)
    (h12 : Sieve42 ε fun M N z => (∀ x, z x = wof x) ∧
      Ev (fun x => max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)))
    (hBig : Sieve42 ε fun M N z =>
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.46 : ℝ) ∧ N x ≤ x ^ (0.46 : ℝ)) ∧
        LL z (fun x => x / (M x * N x))) ∧ Ev (fun x => x ^ (0.375 : ℝ) < N x))
    (hE1 : ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.46 : ℝ) ∧ N x ≤ x ^ (0.46 : ℝ)) ∧
        LL z (fun x => x / (M x * N x))) → (∀ x, wof x ≤ z x) →
      Ev (fun x => N x ≤ x ^ (0.375 : ℝ)) →
      Holds42 ε fun x k =>
        jsum (a x) (b x) (M x) (N x) (wof x) (min (z x) (x ^ (0.225 : ℝ))) k)
    (hE2 : ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.46 : ℝ) ∧ N x ≤ x ^ (0.46 : ℝ)) ∧
        LL z (fun x => x / (M x * N x))) → (∀ x, wof x ≤ z x) →
      Ev (fun x => N x ≤ x ^ (0.375 : ℝ)) →
      Holds42 ε fun x k =>
        jsum (a x) (b x) (M x) (N x) (x ^ (0.225 : ℝ)) (max (z x) (x ^ (0.225 : ℝ))) k) :
    Sieve42 ε fun M N z =>
      (Ev (fun x => x ^ (0.4 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.46 : ℝ) ∧ N x ≤ x ^ (0.46 : ℝ)) ∧
        LL z (fun x => x / (M x * N x))) ∧ (∀ x, wof x ≤ z x) ∧
      (Ev (fun x => N x ≤ x ^ (0.375 : ℝ)) ∨ Ev (fun x => x ^ (0.375 : ℝ) < N x)) := by
  intro B a b M N z ha hb ⟨h13, hw, hcase⟩
  rcases hcase with hsmall | hbig
  · obtain ⟨X1, hX1⟩ := h13.1
    have hd : Holds42 ε fun x k => conv2 (a x) (b x) (M x) (N x) (wof x) k := by
      refine h12 B a b M N wof ha hb ⟨fun _ => rfl, max X1 1, fun x hx => Or.inr ?_⟩
      have h := hX1 x (le_trans (le_max_left _ _) hx)
      exact cond418_range49 (le_trans (le_max_right _ _) hx) hε h.2.1 h.2.2
    have he1 := hE1 B a b M N z ha hb h13 hw hsmall
    have he2 := hE2 B a b M N z ha hb h13 hw hsmall
    obtain ⟨X2, hX2⟩ := wof_le_rpow_ev (0.225 : ℝ) (by norm_num)
    refine holds42_congr_ev ⟨X2, fun x hx k hk => ?_⟩
      (holds42_sub (holds42_sub hd he1) he2)
    simp only [Pi.sub_apply]
    rw [conv2_buchstab (a x) (b x) (M x) (N x) hk (hw x),
      jsum_split_min_max (a x) (b x) (M x) (N x) k (hw x) (hX2 x hx)]
    ring
  · exact hBig B a b M N z ha hb ⟨h13, hbig⟩

/-! ### Vacuity witnesses, PROVED -/

/-- The hypotheses of `cond418_range49` hold at `x = 1`, `ε = 0`, `M = N = 1`. Unit U-1518. -/
theorem cond418_range49_vacuity :
    (1 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℝ) ≤ (1 : ℝ) ^ (0.46 : ℝ) ∧ (1 : ℝ) ≤ (1 : ℝ) ^ (0.46 : ℝ) := by
  simp

/-- The hypotheses of `cond422_range48` hold at `x = 16`, `M = 4 = 16^{1/2}`, `N = 0`.
Unit U-1518. -/
theorem cond422_range48_vacuity :
    (1 : ℝ) ≤ 16 ∧ (16 : ℝ) ^ (0.46 : ℝ) < 4 ∧ (4 : ℝ) ≤ (16 : ℝ) ^ (0.5 : ℝ) ∧
      (4 : ℝ) * 0 ≤ (16 : ℝ) ^ (0.775 : ℝ) := by
  have h4 : (16 : ℝ) ^ (0.5 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨by norm_num, ?_, h4.ge, by rw [mul_zero]; positivity⟩
  rw [← h4]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

end LeanLab.BakerHarmanPintz1997.Decomp1518

open LeanLab.BakerHarmanPintz1997.Decomp1518 in
section
#print axioms conv2_sub_trunc_le
#print axioms moebius_tail_le
#print axioms e2_cofactor_prime
#print axioms lemma12_ev
#print axioms wof_le_rpow_ev
#print axioms holds42_real_upper
#print axioms jsum_split_min_max
#print axioms conv2_buchstab
#print axioms holds42_congr_ev
#print axioms norm_sum_sub_char_le
#print axioms cond422_z_le
#print axioms cond422_range48
#print axioms cond418_range49
#print axioms Yof_nonneg
#print axioms y1_pos
#print axioms psi_sub_trunc_le
#print axioms holds42_of_dominated
#print axioms lemma12_of_410_411_412
#print axioms lemma14_core
#print axioms lemma14_of_lemma12
#print axioms lemma13_core
#print axioms cond418_range49_vacuity
#print axioms cond422_range48_vacuity
end
