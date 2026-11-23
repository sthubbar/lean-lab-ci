import LeanLab.Zhan1991.SingSeries1122
import LeanLab.Zhan1991.RamanujanSum1122

/-!
P0068 Zhan 1991, page 271, the singular series identity `Σ_q μ(q) c_q(N)/φ(q)³ = 𝔖(N)`,
the LEAF `singSeriesIdentity_leaf` of SingSeries1122.lean. Route: `c_q(N)` is multiplicative in
`q` by the Chinese remainder theorem, so `singTerm N` is multiplicative; its prime values are
`-c_p(N)/(p-1)³` with `c_p(N) = p - 1` or `-1`, it vanishes on higher prime powers, and it is
absolutely summable by the Euler product over smooth numbers. Mathlib's Euler product then gives
the identity. The identity holds for every `N`, odd or not.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Finset
open scoped ArithmeticFunction.Moebius

/-- The number of reduced residues below `q` is `φ(q)`. -/
theorem card_coprime_id1122d (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
  rw [Nat.totient]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact Nat.coprime_comm

/-- `|c_q(N)| ≤ φ(q)`. -/
theorem abs_ramanujanC_le_id1122d (q N : ℕ) : |ramanujanC q N| ≤ Nat.totient q := by
  unfold ramanujanC
  calc _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        |Real.cos (2 * π * (a : ℝ) * N / q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => Real.abs_cos_le_one _)
    _ = Nat.totient q := by rw [Finset.sum_const, card_coprime_id1122d]; simp

theorem ramanujanC_one_id1122d (N : ℕ) : ramanujanC 1 N = 1 := by
  unfold ramanujanC
  simp

/-- The full sum of `e(aN/q)` over `a mod q`, real part. -/
theorem sum_cos_range_id1122d (q N : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ Finset.range q, Real.cos (2 * π * (a : ℝ) * N / q) = if q ∣ N then (q : ℝ) else 0 := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    exact this.ne'
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have : ∀ a ∈ Finset.range q,
        Real.cos (2 * π * (a : ℝ) * ((q * k : ℕ) : ℝ) / q) = 1 := by
      intro a _
      have e : 2 * π * (a : ℝ) * ((q * k : ℕ) : ℝ) / q = ((a * k : ℕ) : ℝ) * (2 * π) := by
        push_cast; field_simp
      rw [e, Real.cos_nat_mul_two_pi]
    rw [Finset.sum_congr rfl this]; simp
  · set ζ : ℂ := Complex.exp (2 * π * Complex.I * N / q) with hζ
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have hpow : ∀ a : ℕ,
        ζ ^ a = Complex.exp (((2 * π * (a : ℝ) * N / q : ℝ) : ℂ) * Complex.I) := by
      intro a
      rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hre : ∑ a ∈ Finset.range q, Real.cos (2 * π * (a : ℝ) * N / q) =
        (∑ a ∈ Finset.range q, ζ ^ a).re := by
      rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro a _
      rw [hpow, Complex.exp_ofReal_mul_I_re]
    have hq1 : ζ ^ q = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (q : ℂ) * (2 * π * Complex.I * N / q) = (N : ℂ) * (2 * π * Complex.I) := by
        field_simp
      rw [this, Complex.exp_nat_mul_two_pi_mul_I]
    have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have e1 : (N : ℂ) = k * q := by
        have e2 : (N : ℂ) = (2 * π * Complex.I * N / q) * q / (2 * π * Complex.I) := by
          field_simp
        rw [e2, hk]; field_simp
      apply h
      have e3 : (N : ℤ) = k * q := by exact_mod_cast e1
      exact Int.natCast_dvd_natCast.mp ⟨k, by rw [e3]; ring⟩
    rw [hre, geom_sum_eq hne, hq1]; simp

/-- Page 271, `c_p(N) = p - 1` if `p ∣ N` and `-1` otherwise. -/
theorem ramanujanC_prime_id1122d (p N : ℕ) (hp : p.Prime) :
    ramanujanC p N = if p ∣ N then (p : ℝ) - 1 else -1 := by
  have hp1 := hp.one_le
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range p)
    (fun a => Nat.Coprime a p) (fun a : ℕ => Real.cos (2 * π * (a : ℝ) * N / p))
  have hnot : (Finset.range p).filter (fun a => ¬ Nat.Coprime a p) = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩
      by_contra h0
      apply hc
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
      omega
    · rintro rfl
      exact ⟨hp.pos, by simp [hp.ne_one]⟩
  rw [hnot, Finset.sum_singleton, sum_cos_range_id1122d p N hp1] at hsplit
  unfold ramanujanC
  have h0 : Real.cos (2 * π * ((0 : ℕ) : ℝ) * N / p) = 1 := by simp
  rw [h0] at hsplit
  split_ifs at hsplit ⊢ <;> linarith

/-- The Ramanujan sum is multiplicative in `q`, by the Chinese remainder theorem. -/
theorem ramanujanC_mul_id1122d (m n N : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    ramanujanC (m * n) N = ramanujanC m N * ramanujanC n N := by
  set A := (Finset.range m).filter (fun a => Nat.Coprime a m) with hA
  set B := (Finset.range n).filter (fun b => Nat.Coprime b n) with hB
  set C := (Finset.range (m * n)).filter (fun c => Nat.Coprime c (m * n)) with hC
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have hcm : ramanujanC m N = ∑ a ∈ A, Real.cos (2 * π * (a : ℝ) * N / m) := rfl
  have hcn : ramanujanC n N = ∑ b ∈ B, Real.cos (2 * π * (b : ℝ) * N / n) := rfl
  have hcmn : ramanujanC (m * n) N =
      ∑ c ∈ C, Real.cos (2 * π * (c : ℝ) * N / ((m * n : ℕ) : ℝ)) := rfl
  have hs : ∑ a ∈ A, Real.sin (2 * π * (a : ℝ) * N / m) = 0 := ramanujan_sin_zero m N hm
  have hR : ramanujanC m N * ramanujanC n N =
      ∑ x ∈ A ×ˢ B, Real.cos (2 * π * (x.1 : ℝ) * N / m + 2 * π * (x.2 : ℝ) * N / n) := by
    rw [hcm, hcn, Finset.sum_product, Finset.sum_mul_sum]
    have : ∀ a ∈ A, ∑ b ∈ B, Real.cos (2 * π * (a : ℝ) * N / m) *
          Real.cos (2 * π * (b : ℝ) * N / n)
        = ∑ b ∈ B, Real.cos (2 * π * (a : ℝ) * N / m + 2 * π * (b : ℝ) * N / n)
          + Real.sin (2 * π * (a : ℝ) * N / m) *
            ∑ b ∈ B, Real.sin (2 * π * (b : ℝ) * N / n) := by
      intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _; rw [Real.cos_add]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, hs, zero_mul,
      add_zero]
  rw [hR, hcmn]
  let i : ℕ × ℕ → ℕ := fun x => (x.1 * n + x.2 * m) % (m * n)
  have hmnpos : 0 < m * n := by positivity
  have hi : ∀ x ∈ A ×ˢ B, i x ∈ C := by
    intro x hx
    rw [Finset.mem_product] at hx
    have ha := (Finset.mem_filter.mp hx.1).2
    have hb := (Finset.mem_filter.mp hx.2).2
    rw [hC, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hmnpos, ?_⟩
    have h1 : Nat.Coprime m (x.1 * n + x.2 * m) := by
      rw [Nat.coprime_add_mul_right_right]
      exact Nat.Coprime.mul_right ha.symm hmn
    have h2 : Nat.Coprime n (x.1 * n + x.2 * m) := by
      rw [add_comm, Nat.coprime_add_mul_right_right]
      exact Nat.Coprime.mul_right hb.symm hmn.symm
    have h3 : Nat.Coprime (m * n) (x.1 * n + x.2 * m) :=
      (Nat.Coprime.mul_right h1.symm h2.symm).symm
    unfold Nat.Coprime
    rw [← Nat.gcd_rec]
    exact h3
  have hinj : Set.InjOn i (A ×ˢ B : Finset (ℕ × ℕ)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hx hy
    have ha1 := Finset.mem_range.mp (Finset.mem_filter.mp hx.1).1
    have hb1 := Finset.mem_range.mp (Finset.mem_filter.mp hx.2).1
    have ha2 := Finset.mem_range.mp (Finset.mem_filter.mp hy.1).1
    have hb2 := Finset.mem_range.mp (Finset.mem_filter.mp hy.2).1
    have hE : x.1 * n + x.2 * m ≡ y.1 * n + y.2 * m [MOD m * n] := hxy
    have hEm := hE.of_mul_right n
    have hEn := hE.of_mul_left m
    have e1 : x.1 * n ≡ y.1 * n [MOD m] := by
      unfold Nat.ModEq at hEm ⊢
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at hEm
    have e2 : x.2 * m ≡ y.2 * m [MOD n] := by
      unfold Nat.ModEq at hEn ⊢
      rwa [add_comm, Nat.add_mul_mod_self_right, add_comm,
        Nat.add_mul_mod_self_right] at hEn
    have f1 := Nat.ModEq.cancel_right_of_coprime hmn e1
    have f2 := Nat.ModEq.cancel_right_of_coprime hmn.symm e2
    unfold Nat.ModEq at f1 f2
    rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2] at f1
    rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at f2
    exact Prod.ext f1 f2
  have himg : (A ×ˢ B).image i = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      exact hi x hx
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, hA, hB, hC,
        card_coprime_id1122d, card_coprime_id1122d, card_coprime_id1122d, Nat.totient_mul hmn]
  rw [← himg, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro x _
  set c := x.1 * n + x.2 * m with hc
  have hdiv := Nat.mod_add_div c (m * n)
  have hcast : ((c % (m * n) : ℕ) : ℝ) = (c : ℝ) - (m * n : ℝ) * ((c / (m * n) : ℕ) : ℝ) := by
    have : ((c % (m * n) : ℕ) : ℝ) + ((m * n : ℕ) : ℝ) * ((c / (m * n) : ℕ) : ℝ) = (c : ℝ) := by
      exact_mod_cast hdiv
    push_cast at this ⊢
    linarith
  have e : 2 * π * (x.1 : ℝ) * N / m + 2 * π * (x.2 : ℝ) * N / n =
      2 * π * ((c % (m * n) : ℕ) : ℝ) * N / ((m * n : ℕ) : ℝ) +
        ((c / (m * n) * N : ℕ) : ℝ) * (2 * π) := by
    rw [hcast, hc]; push_cast; field_simp; ring
  rw [e, Real.cos_add_nat_mul_two_pi]

/-- `singTerm N` is multiplicative on coprime arguments. -/
theorem singTerm_mul_id1122d (N : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    singTerm N (m * n) = singTerm N m * singTerm N n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [singTerm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [singTerm]
  have hmn : m * n ≠ 0 := by positivity
  simp only [singTerm, hmn, hm.ne', hn.ne', ite_false]
  rw [ramanujanC_mul_id1122d m n N hm hn h, Nat.totient_mul h,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast; ring

theorem singTerm_one_id1122d (N : ℕ) : singTerm N 1 = 1 := by
  simp [singTerm, ramanujanC_one_id1122d]

theorem singTerm_prime_pow_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 2 ≤ e) :
    singTerm N (p ^ e) = 0 := by
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [singTerm, hne, ite_false]
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  have : e ≠ 1 := by omega
  simp [this]

/-- Page 271, the value at a prime: `μ(p) c_p(N)/φ(p)³ = -c_p(N)/(p-1)³`. -/
theorem singTerm_prime_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
    singTerm N p = -ramanujanC p N / ((p : ℝ) - 1) ^ 3 := by
  simp only [singTerm, hp.ne_zero, ite_false]
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le]
  push_cast; ring

/-- `|μ(q) c_q(N)/φ(q)³| ≤ 1/φ(q)²`. -/
theorem abs_singTerm_le_id1122d (N q : ℕ) (hq : 1 ≤ q) :
    |singTerm N q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
  have hq0 : q ≠ 0 := by omega
  have ht : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  simp only [singTerm, hq0, ite_false]
  rw [abs_mul, abs_div, abs_pow, abs_of_pos ht]
  have hmu : |((μ q : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := q)
    exact_mod_cast this
  have hc := abs_ramanujanC_le_id1122d q N
  calc |((μ q : ℤ) : ℝ)| / (Nat.totient q : ℝ) ^ 3 * |ramanujanC q N|
      ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hc (abs_nonneg _)
          (by positivity)
    _ = 1 / (Nat.totient q : ℝ) ^ 2 := by field_simp

theorem abs_singTerm_prime_le_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
    |singTerm N p| ≤ 4 / (p : ℝ) ^ 2 := by
  have h := abs_singTerm_le_id1122d N p hp.one_le
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] at h
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine h.trans ?_
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- An Euler factor of a function vanishing on prime powers `p^e`, `e ≥ 2`. -/
theorem tsum_prime_pow_id1122d (g : ℕ → ℝ) (hg1 : g 1 = 1) {p : ℕ}
    (hpe : ∀ e, 2 ≤ e → g (p ^ e) = 0) : ∑' e : ℕ, g (p ^ e) = 1 + g p := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, hg1]
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    exact hpe e he

theorem summable_four_div_sq_id1122d : Summable (fun m : ℕ => 4 / (m : ℝ) ^ 2) := by
  have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 4
  exact this.congr (fun m => by ring)

/-- Partial sums of a nonnegative multiplicative function, bounded by its Euler product over
smooth numbers. -/
theorem sum_range_le_of_mult_id1122d (g : ℕ → ℝ) (hg1 : g 1 = 1)
    (hgmul : ∀ {m n : ℕ}, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg0 : ∀ q, 0 ≤ g q) (hgz : g 0 = 0)
    (hpsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖g (p ^ e)‖)) (n : ℕ) :
    ∑ i ∈ Finset.range n, g i ≤ ∏ p ∈ n.primesBelow, ∑' e, g (p ^ e) := by
  obtain ⟨_, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg1 hgmul hpsum n
  have hind := hasSum_subtype_iff_indicator.mp hhas
  have heq : ∑ i ∈ Finset.range n, g i =
      ∑ i ∈ Finset.range n, (Set.indicator (Nat.smoothNumbers n) g) i := by
    apply Finset.sum_congr rfl; intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hgz]; by_cases h0 : (0 : ℕ) ∈ Nat.smoothNumbers n
      · rw [Set.indicator_of_mem h0, hgz]
      · rw [Set.indicator_of_notMem h0]
    · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (Finset.mem_range.mp hi))]
  rw [heq]
  exact sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => hg0 j) i) hind

theorem prod_primesBelow_le_id1122d (g : ℕ → ℝ) (hg0 : ∀ q, 0 ≤ g q)
    (hgp : ∀ {p : ℕ}, p.Prime → g p ≤ 4 / (p : ℝ) ^ 2) (n : ℕ) :
    ∏ p ∈ n.primesBelow, (1 + g p) ≤ Real.exp (∑' m : ℕ, 4 / (m : ℝ) ^ 2) := by
  have h1 : ∏ p ∈ n.primesBelow, (1 + g p) ≤ ∏ p ∈ n.primesBelow, Real.exp (4 / (p : ℝ) ^ 2) := by
    apply Finset.prod_le_prod₀ (fun p _ => by linarith [hg0 p])
    intro p hp
    have h1 := hgp (Nat.prime_of_mem_primesBelow hp)
    have h2 := Real.add_one_le_exp (4 / (p : ℝ) ^ 2)
    linarith
  refine h1.trans ?_
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hsub : n.primesBelow ⊆ Finset.range n := fun p hp => (Finset.mem_filter.mp hp).1
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => by positivity)) ?_
  exact summable_four_div_sq_id1122d.sum_le_tsum (Finset.range n) (fun i _ => by positivity)

/-- Absolute summability of the singular series, page 271. -/
theorem summable_abs_singTerm_id1122d (N : ℕ) : Summable (fun q => |singTerm N q|) := by
  have hg1 : |singTerm N 1| = 1 := by rw [singTerm_one_id1122d, abs_one]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      |singTerm N (m * n)| = |singTerm N m| * |singTerm N n| := by
    intro m n h; rw [singTerm_mul_id1122d N h, abs_mul]
  have hgz : |singTerm N 0| = 0 := by simp [singTerm]
  have hpe : ∀ {p : ℕ}, p.Prime → ∀ e, 2 ≤ e → |singTerm N (p ^ e)| = 0 := by
    intro p hp e he; rw [singTerm_prime_pow_id1122d N hp he, abs_zero]
  have hpsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖|singTerm N (p ^ e)|‖) := by
    intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro e he
    simp only [Finset.mem_range, not_lt] at he
    rw [hpe hp e he, norm_zero]
  refine summable_of_sum_range_le (fun q => abs_nonneg _)
    (c := Real.exp (∑' m : ℕ, 4 / (m : ℝ) ^ 2)) ?_
  intro n
  refine (sum_range_le_of_mult_id1122d (fun q => |singTerm N q|) hg1 hgmul
    (fun q => abs_nonneg _) hgz hpsum n).trans ?_
  have hfac : ∏ p ∈ n.primesBelow, ∑' e, |singTerm N (p ^ e)| =
      ∏ p ∈ n.primesBelow, (1 + |singTerm N p|) :=
    Finset.prod_congr rfl (fun p hp =>
      tsum_prime_pow_id1122d (fun q => |singTerm N q|) hg1
        (hpe (Nat.prime_of_mem_primesBelow hp)))
  rw [hfac]
  exact prod_primesBelow_le_id1122d (fun q => |singTerm N q|) (fun q => abs_nonneg _)
    (fun hp => abs_singTerm_prime_le_id1122d N hp) n

/-- Page 271, the Euler factor of the singular series at a prime `p`. -/
theorem singTerm_euler_factor_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, singTerm N (p ^ e) =
      if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  rw [tsum_prime_pow_id1122d (singTerm N) (singTerm_one_id1122d N)
    (fun e he => singTerm_prime_pow_id1122d N hp he), singTerm_prime_id1122d N hp,
    ramanujanC_prime_id1122d p N hp]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  split_ifs <;> field_simp <;> ring

/-- Page 271, the singular series identity `Σ_q μ(q) c_q(N)/φ(q)³ = 𝔖(N)` for odd `N`,
via Mathlib's Euler product. PROVED. -/
theorem singSeriesIdentity_proof : SingSeriesIdentity := by
  intro N _
  have hsum : Summable (fun q => ‖singTerm N q‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_singTerm_id1122d N
  have hf0 : singTerm N 0 = 0 := by simp [singTerm]
  have hE := EulerProduct.eulerProduct_tprod (singTerm_one_id1122d N)
    (fun h => singTerm_mul_id1122d N h) hsum hf0
  have hS : Sing N = ∑' n, singTerm N n := by
    rw [← hE]
    unfold Sing
    exact tprod_congr (fun p => (singTerm_euler_factor_id1122d N p.2).symm)
  rw [hS]
  exact hsum.of_norm.hasSum

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.singSeriesIdentity_proof
