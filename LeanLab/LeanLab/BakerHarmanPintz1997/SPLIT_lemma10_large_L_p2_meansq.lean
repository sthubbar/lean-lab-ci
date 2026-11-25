/-
Second split for the mean square leaves of Lemma 10, P0069 page 24, `leaf_large_mean_square` in
SPLIT_lemma10_large_L and `leaf_338_mean_M` in SPLIT_lemma10_small_L_338.

The paper bounds ||M||_2^2 by Lemma 1, (3.3), ||M||_2^2 << L (qT + M) G(M), and G(M) << L^B'' by
(3.1). Here:
Piece 1, the divisor harmonic moment sum_{n <= X} tau(n)^r / n <= (1 + log X)^(2^r), PROVED, the
argument of Akeno2026 DecompJ267 `divisorHarmonic_log_bound221`, restated locally so the
BakerHarmanPintz1997 folder does not import Akeno2026.
Piece 2, G(F) <= (1 + log floor(c2 X))^(2^r) for a polynomial of length F <= X with (3.1), PROVED.
Piece 3, the mean square bound ||P||_2 <= K L^E (qT + F)^(1/2) for x large, CONDITIONAL ON the
cited Lemma 1, passed as a hypothesis, PROVED from it. It allows F below 2 by enlarging the
length to max(F, 2) with c1 replaced by min(c1, 1/4), and F up to Y x by applying Lemma 1 at Y x.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompJ381

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- The divisor harmonic sum `Σ_{1 ≤ n ≤ M} τ(n)^r / n`. -/
noncomputable def divHarmP2 (r M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ r / n

/-- Proved helper: `τ(n)^(r+1) ≤ Σ_{d | n} τ(d)^r τ(n/d)^r`. -/
theorem divMomentConvP2 (r n : ℕ) :
    (n.divisors.card : ℝ) ^ (r + 1) ≤
      ∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ r * ((n / d).divisors.card : ℝ) ^ r := by
  classical
  calc
    _ = ∑ d ∈ n.divisors, (n.divisors.card : ℝ) ^ r := by
      simp [pow_succ, mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdn := Nat.dvd_of_mem_divisors hd
      have hτ : n.divisors.card ≤ d.divisors.card * (n / d).divisors.card := by
        calc
          _ = (d * (n / d)).divisors.card := by rw [Nat.mul_div_cancel' hdn]
          _ ≤ _ := by rw [Nat.divisors_mul]; exact Finset.card_mul_le
      have hτR : (n.divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * ((n / d).divisors.card : ℝ) := by
        exact_mod_cast hτ
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n.divisors.card) hτR r

/-- Proved helper: the moment recurrence `D(r+1, M) ≤ D(r, M)^2`. -/
theorem divHarmRecP2 (r M : ℕ) : divHarmP2 (r + 1) M ≤ divHarmP2 r M ^ 2 := by
  classical
  let s := (Finset.Icc 1 M).sigma (fun n => n.divisors)
  let t := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  let e : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2, p.1 / p.2)
  have hmul : ∀ p ∈ s, p.2 * (p.1 / p.2) = p.1 := by
    intro p hp
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2)
  have hinj : Set.InjOn e (s : Set (Σ _ : ℕ, ℕ)) := by
    intro p hp q hq he
    have hd : p.2 = q.2 := congrArg Prod.fst he
    have hquot : p.1 / p.2 = q.1 / q.2 := congrArg Prod.snd he
    have hn : p.1 = q.1 := by
      calc
        p.1 = p.2 * (p.1 / p.2) := (hmul p hp).symm
        _ = q.2 * (q.1 / q.2) := by rw [hquot, hd]
        _ = q.1 := hmul q hq
    exact Sigma.ext hn (heq_of_eq hd)
  have hmap : Finset.image e s ⊆ t := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hn := Finset.mem_Icc.mp (Finset.mem_sigma.mp hp).1
    have hd := (Finset.mem_sigma.mp hp).2
    have hqpos : 1 ≤ p.1 / p.2 := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro he
      have hh := hmul p hp
      rw [he, mul_zero] at hh
      omega
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hn.2⟩,
      Finset.mem_Icc.mpr ⟨hqpos, (Nat.div_le_self _ _).trans hn.2⟩⟩
  have hsum : (∑ p ∈ s, (p.2.divisors.card : ℝ) ^ r * ((p.1 / p.2).divisors.card : ℝ) ^ r / p.1) ≤
      ∑ p ∈ t, ((p.1.divisors.card : ℝ) ^ r / p.1) * ((p.2.divisors.card : ℝ) ^ r / p.2) := by
    apply Finset.sum_le_sum_of_injOn e hinj hmap
    · intro p hp
      dsimp only [e]
      rw [div_mul_div_comm, ← Nat.cast_mul, hmul p hp]
    · intro p hp hn
      positivity
  unfold divHarmP2
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ r * ((n / d).divisors.card : ℝ) ^ r) / n := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_right (divMomentConvP2 r n) (Nat.cast_nonneg _)
    _ = ∑ p ∈ s, (p.2.divisors.card : ℝ) ^ r * ((p.1 / p.2).divisors.card : ℝ) ^ r / p.1 := by
      simp_rw [Finset.sum_div]
      exact Finset.sum_sigma' _ _ _
    _ ≤ _ := hsum
    _ = _ := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- LEAF: page 24, the divisor sum behind G(F) << L^B'' from (3.1), in the moment form
`Σ_{n ≤ M} τ(n)^r / n ≤ (1 + log M)^(2^r)`. EASY. PROVED by induction on r. -/
theorem divHarmLogP2 (r M : ℕ) : divHarmP2 r M ≤ (1 + Real.log M) ^ (2 ^ r) := by
  induction r with
  | zero =>
    simpa only [divHarmP2, pow_zero, pow_one, one_div,
      harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log M
  | succ r ih =>
    apply (divHarmRecP2 r M).trans
    calc
      divHarmP2 r M ^ 2 ≤ ((1 + Real.log M) ^ (2 ^ r)) ^ 2 :=
        pow_le_pow_left₀ (by unfold divHarmP2; positivity) ih 2
      _ = _ := by rw [← pow_mul, pow_succ]

/-- LEAF: page 24 with Lemma 1, the bound G(F) << L^B'' for a polynomial of length F <= X with
coefficients satisfying (3.1). EASY. PROVED from `divHarmLogP2`.
Non-vacuity: the unit polynomial on one integer in (c1 F, c2 F). -/
theorem dpG_le_P2 (P : DP) (B c1 c2 F X : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hlen : P.HasLen F c1 c2) (hcoef : P.Coef31 B) (hFX : F ≤ X) :
    P.G ≤ (1 + Real.log ⌊c2 * X⌋₊) ^ (2 ^ ⌈2 * max B 0⌉₊) := by
  set r := ⌈2 * max B 0⌉₊
  have hmem : ∀ n ∈ P.supp, 1 ≤ n ∧ n ≤ ⌊c2 * X⌋₊ := by
    intro n hn
    obtain ⟨h1, h2⟩ := hlen n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hF : 0 < F := by
      by_contra hF
      push_neg at hF
      have : c2 * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2.le hF
      linarith
    have hpos : (0 : ℝ) < n := lt_of_le_of_lt (mul_pos hc1 hF).le h1
    refine ⟨?_, ?_⟩
    · have : 0 < n := by exact_mod_cast hpos
      omega
    · apply Nat.le_floor
      exact h2.le.trans (mul_le_mul_of_nonneg_left hFX hc2.le)
  have hsub : P.supp ⊆ Finset.Icc 1 ⌊c2 * X⌋₊ := fun n hn =>
    Finset.mem_Icc.mpr (hmem n hn)
  unfold DP.G
  calc ∑ n ∈ P.supp, ‖P.coef n‖ ^ 2 / n
      ≤ ∑ n ∈ P.supp, (n.divisors.card : ℝ) ^ r / n := by
        apply Finset.sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        have hn1 := (hmem n hn).1
        have htau : tau n = (n.divisors.card : ℝ) := by
          simp [tau, ArithmeticFunction.sigma_zero_apply]
        have hτ1 : (1 : ℝ) ≤ n.divisors.card := by
          have : 1 ≤ n.divisors.card :=
            Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
          exact_mod_cast this
        have hτ0 : (0 : ℝ) ≤ n.divisors.card := by linarith
        have h1 : ‖P.coef n‖ ≤ (n.divisors.card : ℝ) ^ (max B 0) := by
          have := hcoef n hn
          rw [htau] at this
          exact this.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (le_max_left _ _))
        have h2 : ‖P.coef n‖ ^ 2 ≤ ((n.divisors.card : ℝ) ^ (max B 0)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        have h3 : ((n.divisors.card : ℝ) ^ (max B 0)) ^ 2 =
            (n.divisors.card : ℝ) ^ (2 * max B 0) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0]
          congr 1
          push_cast
          ring
        have h4 : (n.divisors.card : ℝ) ^ (2 * max B 0) ≤ (n.divisors.card : ℝ) ^ ((r : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτ1 (Nat.le_ceil _)
        rw [Real.rpow_natCast] at h4
        linarith
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊c2 * X⌋₊, (n.divisors.card : ℝ) ^ r / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ _ := divHarmLogP2 r _

/-- LEAF: page 24, ||P||_2 << L^E (qT + F)^(1/2) for a polynomial of length F with (3.1), by
Lemma 1, (3.3), and G(F) << L^B''. MEDIUM. PROVED, CONDITIONAL ON the cited Lemma 1 given as the
hypothesis `h1`. The length may be below 2 and up to Y x for a fixed Y >= 1.
Non-vacuity: Y = 1 and F = x^(1/2) with any well spaced configuration. -/
theorem meanSquare_of_lemma1_P2 (h1 : Lemma1) (B c1 c2 Y : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2)
    (hY : 1 ≤ Y) :
    ∃ E K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ (F : ℝ) (P : DP) (c : Cfg),
      P.HasLen F c1 c2 → P.Coef31 B → c.Std x → F ≤ Y * x →
      pnorm P c 2 ≤ K * (L x ^ E * (c.q * c.T + max F 0) ^ (1 / 2 : ℝ)) := by
  set c1' := min c1 (1 / 4) with hc1'
  have hc1'pos : 0 < c1' := lt_min hc1 (by norm_num)
  have hc2pos : 0 < c2 := by linarith
  obtain ⟨K1, hK1⟩ := h1 B c1' c2 hc1'pos (lt_of_le_of_lt (min_le_left _ _) hc2)
  set r := ⌈2 * max B 0⌉₊
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  set a := |Real.log (c2 * Y)| + Real.log Y + 1 with ha
  set K2 := max K1 0 * 4 * 2 ^ (2 ^ r) with hK2
  have hK2n : 0 ≤ K2 := by positivity
  refine ⟨((1 + 2 ^ r : ℕ) : ℝ) / 2, Real.sqrt K2, max 2 (Real.exp a), Real.sqrt_nonneg _, ?_⟩
  intro x hx F P c hlen hcoef hstd hFY
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLa : a ≤ L x := (Real.le_log_iff_exp_le hx0).2 ((le_max_right _ _).trans hx)
  have habs := abs_nonneg (Real.log (c2 * Y))
  have hL1 : 1 ≤ L x := by linarith
  have hL0 : 0 ≤ L x := by linarith
  set F' := max F 2 with hF'
  have hlen' : P.HasLen F' c1' c2 := by
    intro n hn
    obtain ⟨h1n, h2n⟩ := hlen n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hFpos : 0 < F := by
      by_contra hF
      push_neg at hF
      have : c2 * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2pos.le hF
      linarith
    have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (mul_pos hc1 hFpos).le h1n
    have hn1 : (1 : ℝ) ≤ n := by
      have : 0 < n := by exact_mod_cast hnpos
      exact_mod_cast this
    refine ⟨?_, ?_⟩
    · rcases le_total F 2 with h | h
      · rw [hF', max_eq_right h]
        have : c1' ≤ 1 / 4 := min_le_right _ _
        linarith
      · rw [hF', max_eq_left h]
        have : c1' * F ≤ c1 * F := mul_le_mul_of_nonneg_right (min_le_left _ _) hFpos.le
        linarith
    · exact lt_of_lt_of_le h2n (mul_le_mul_of_nonneg_left (le_max_left _ _) hc2pos.le)
  have hxY : x ≤ Y * x := le_mul_of_one_le_left hx0.le hY
  have hF'x' : F' ≤ Y * x := max_le hFY (hx2.trans hxY)
  have h2F' : 2 ≤ F' := le_max_right _ _
  obtain ⟨hws, hq1, hqx, hT2, hTx⟩ := hstd
  have hstd' : c.Std (Y * x) := ⟨hws, hq1, hqx.trans hxY, hT2, hTx.trans (by linarith)⟩
  obtain ⟨hms, -⟩ := hK1 (Y * x) F' h2F' hF'x' P hlen' hcoef c hstd'
  have hG := dpG_le_P2 P B c1' c2 F' (Y * x) hc1'pos hc2pos hlen' hcoef hF'x'
  have hG0 : 0 ≤ P.G := by unfold DP.G; positivity
  have hq1' : (1 : ℝ) ≤ c.q := by exact_mod_cast hq1
  have hqT : 2 ≤ (c.q : ℝ) * c.T := by nlinarith
  -- the logarithm of the enlarged range
  have hLx' : L (Y * x) ≤ 2 * L x := by
    unfold L
    rw [Real.log_mul (by linarith) hx0.ne']
    unfold L at hLa
    linarith
  have hLx'0 : 0 ≤ L (Y * x) := Real.log_nonneg (by nlinarith)
  have hlogfl : 1 + Real.log ⌊c2 * (Y * x)⌋₊ ≤ 2 * L x := by
    have hb : Real.log ⌊c2 * (Y * x)⌋₊ ≤ |Real.log (c2 * Y)| + L x := by
      rcases Nat.eq_zero_or_pos ⌊c2 * (Y * x)⌋₊ with h0 | hpos
      · rw [h0]
        simp
        linarith
      · have hp : (0 : ℝ) < ⌊c2 * (Y * x)⌋₊ := by exact_mod_cast hpos
        have hcY : 0 < c2 * Y := by positivity
        calc Real.log ⌊c2 * (Y * x)⌋₊ ≤ Real.log (c2 * (Y * x)) :=
              Real.log_le_log hp (Nat.floor_le (by positivity))
          _ = Real.log (c2 * Y) + L x := by
              rw [← mul_assoc, Real.log_mul hcY.ne' hx0.ne']
              rfl
          _ ≤ _ := by linarith [le_abs_self (Real.log (c2 * Y))]
    linarith
  have hlogfl0 : 0 ≤ 1 + Real.log ⌊c2 * (Y * x)⌋₊ := by
    have := Real.log_natCast_nonneg ⌊c2 * (Y * x)⌋₊
    linarith
  have hGb : P.G ≤ 2 ^ (2 ^ r) * L x ^ (2 ^ r) := by
    calc P.G ≤ (1 + Real.log ⌊c2 * (Y * x)⌋₊) ^ (2 ^ r) := hG
      _ ≤ (2 * L x) ^ (2 ^ r) := pow_le_pow_left₀ hlogfl0 hlogfl _
      _ = _ := mul_pow _ _ _
  set w := (c.q : ℝ) * c.T + max F 0 with hw
  have hw0 : 0 ≤ w := by
    have := le_max_right F 0
    linarith
  have hqF : (c.q : ℝ) * c.T + F' ≤ 2 * w := by
    have : F' ≤ max F 0 + 2 := max_le (by linarith [le_max_left F 0]) (by linarith [le_max_right F 0])
    linarith
  have hqF0 : 0 ≤ (c.q : ℝ) * c.T + F' := by linarith
  have hsq : pnorm P c 2 ^ 2 ≤ K2 * (L x ^ (1 + 2 ^ r) * w) := by
    have hk : K1 * L (Y * x) * ((c.q : ℝ) * c.T + F') * P.G ≤
        max K1 0 * L (Y * x) * ((c.q : ℝ) * c.T + F') * P.G := by
      have := mul_le_mul_of_nonneg_right (le_max_left K1 0)
        (mul_nonneg (mul_nonneg hLx'0 hqF0) hG0)
      linarith [this]
    have hm0 : 0 ≤ max K1 0 := le_max_right _ _
    calc pnorm P c 2 ^ 2 ≤ K1 * L (Y * x) * ((c.q : ℝ) * c.T + F') * P.G := hms
      _ ≤ max K1 0 * L (Y * x) * ((c.q : ℝ) * c.T + F') * P.G := hk
      _ ≤ max K1 0 * (2 * L x) * (2 * w) * (2 ^ (2 ^ r) * L x ^ (2 ^ r)) := by
          apply mul_le_mul _ hGb hG0 (by positivity)
          apply mul_le_mul _ hqF hqF0 (by positivity)
          exact mul_le_mul_of_nonneg_left hLx' hm0
      _ = K2 * (L x ^ (1 + 2 ^ r) * w) := by
          rw [hK2, pow_add, pow_one]
          ring
  have hp0 : 0 ≤ pnorm P c 2 :=
    Real.rpow_nonneg (sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hsqrt : pnorm P c 2 ≤ Real.sqrt (K2 * (L x ^ (1 + 2 ^ r) * w)) := by
    rw [← Real.sqrt_sq hp0]
    exact Real.sqrt_le_sqrt hsq
  have hLE : Real.sqrt (L x ^ (1 + 2 ^ r)) = L x ^ (((1 + 2 ^ r : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    congr 1
    ring
  calc pnorm P c 2 ≤ Real.sqrt (K2 * (L x ^ (1 + 2 ^ r) * w)) := hsqrt
    _ = Real.sqrt K2 * (Real.sqrt (L x ^ (1 + 2 ^ r)) * Real.sqrt w) := by
        rw [Real.sqrt_mul hK2n (L x ^ (1 + 2 ^ r) * w),
          Real.sqrt_mul (pow_nonneg hL0 _) w]
    _ = _ := by rw [hLE, Real.sqrt_eq_rpow w]

#print axioms divMomentConvP2
#print axioms divHarmRecP2
#print axioms divHarmLogP2
#print axioms dpG_le_P2
#print axioms meanSquare_of_lemma1_P2

end LeanLab.BakerHarmanPintz1997
