/-
Split of `linnik_weighted_gap150` into three steps. Nothing here changes the
statement: `linnik_weighted_gap150_split` states it character for character and
proves it from the leaves below. In order, the leaves record (1) an upper bound
for the von Mangoldt mass carried by the non prime numbers of one residue class,
(2) a lower bound for the von Mangoldt mass of a whole residue class at the scale
`C * q ^ L`, and (3) one choice of `L` and one choice of `C` for which that lower
bound beats that upper bound at every modulus at least two. The assembly needs
nothing further: the two bounds meet at the floor of `C * q ^ L`, which is also
the witness of the polynomial scale.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150c

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-! ### Helpers for Leaf 1: the von Mangoldt mass of the non primes -/

private lemma vonMangoldt_eq_log_minFac {n : ℕ} (h : IsPrimePow n) :
    vonMangoldt n = Real.log ((n.minFac : ℕ) : ℝ) := by
  rw [vonMangoldt_apply]
  simp [h]

private lemma fiber_sum_le_log (X p : ℕ) (hp : p.Prime) :
    (∑ n ∈ (Finset.Icc 1 X).filter
        (fun n => IsPrimePow n ∧ ¬ n.Prime ∧ n.minFac = p), vonMangoldt n)
      ≤ Real.log (X : ℝ) := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    simp
  set F : Finset ℕ := (Finset.Icc 1 X).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime ∧ n.minFac = p) with hF
  have hmemF : ∀ n, n ∈ F ↔ (1 ≤ n ∧ n ≤ X) ∧ IsPrimePow n ∧ ¬ n.Prime ∧ n.minFac = p := by
    intro n; rw [hF]; simp
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hval : ∀ n ∈ F, vonMangoldt n = Real.log (p : ℝ) := by
    intro n hn
    obtain ⟨-, hpp, -, hmin⟩ := (hmemF n).mp hn
    rw [vonMangoldt_eq_log_minFac hpp, hmin]
  have hconst : (∑ n ∈ F, vonMangoldt n) = (F.card : ℝ) * Real.log (p : ℝ) := by
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  rcases Finset.eq_empty_or_nonempty F with hF0 | hFne
  · rw [hF0]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact Real.log_nonneg (by exact_mod_cast hX)
  have hfac : ∀ n ∈ F, n = p ^ (n.factorization p) := by
    intro n hn
    obtain ⟨-, hpp, -, hmin⟩ := (hmemF n).mp hn
    have h := IsPrimePow.minFac_pow_factorization_eq hpp
    rw [hmin] at h
    exact h.symm
  have hexp1 : ∀ n ∈ F, 1 ≤ n.factorization p := by
    intro n hn
    have h := hfac n hn
    rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | h0
    · rw [h0, pow_zero] at h
      obtain ⟨-, hpp, -, -⟩ := (hmemF n).mp hn
      rw [h] at hpp
      exact absurd rfl hpp.ne_one
    · exact h0
  have hinjOn : Set.InjOn (fun n : ℕ => n.factorization p) (↑F : Set ℕ) := by
    intro n1 h1 n2 h2 he
    have he' : n1.factorization p = n2.factorization p := he
    rw [hfac n1 h1, hfac n2 h2, he']
  set s : Finset ℕ := F.image (fun n => n.factorization p) with hs
  have hcard : F.card = s.card := by
    rw [hs]
    exact (Finset.card_image_of_injOn hinjOn).symm
  have hsne : s.Nonempty := by
    rw [hs]; exact hFne.image _
  have hspos : ∀ e ∈ s, 1 ≤ e := by
    intro e he
    rw [hs, Finset.mem_image] at he
    obtain ⟨n, hn, rfl⟩ := he
    exact hexp1 n hn
  have hmaxpos : 1 ≤ s.max' hsne := hspos _ (Finset.max'_mem s hsne)
  have hcardle : s.card ≤ s.max' hsne := by
    have hsub : s ⊆ Finset.Icc 1 (s.max' hsne) := by
      intro e he
      exact Finset.mem_Icc.mpr ⟨hspos e he, Finset.le_max' s e he⟩
    calc s.card ≤ (Finset.Icc 1 (s.max' hsne)).card := Finset.card_le_card hsub
      _ = s.max' hsne := by rw [Nat.card_Icc]; omega
  have hkey : ∀ e ∈ s, ∃ n ∈ F, n.factorization p = e := by
    intro e he
    rw [hs, Finset.mem_image] at he
    exact he
  have hmaxpow : p ^ (s.max' hsne) ≤ X := by
    obtain ⟨n, hnF, hne⟩ := hkey _ (Finset.max'_mem s hsne)
    rw [← hne, ← hfac n hnF]
    exact ((hmemF n).mp hnF).1.2
  have hlogmax : (s.max' hsne : ℝ) * Real.log (p : ℝ) ≤ Real.log (X : ℝ) := by
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have h1 : Real.log ((p:ℝ) ^ s.max' hsne) ≤ Real.log (X:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmaxpow)
    rwa [Real.log_pow] at h1
  calc (F.card : ℝ) * Real.log (p:ℝ) = (s.card : ℝ) * Real.log (p:ℝ) := by rw [hcard]
    _ ≤ (s.max' hsne : ℝ) * Real.log (p:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlogp
        exact_mod_cast hcardle
    _ ≤ Real.log (X:ℝ) := hlogmax

/-! ### Helpers for Leaf 1: the von Mangoldt mass of the non primes -/

private lemma sum_primepow_nonprime_le (X : ℕ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), vonMangoldt n)
      ≤ 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · subst hX0
    norm_num
  set B : Finset ℕ := (Finset.Icc 1 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hB
  have hfib : ∀ p ∈ B.image (fun n => n.minFac),
      (∑ n ∈ B.filter (fun n => n.minFac = p), vonMangoldt n) ≤ Real.log (X : ℝ) := by
    intro p hp
    rw [hB, Finset.mem_image] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    have hnB : n ∈ B := by rw [hB]; exact hn
    have hn1 : n ≠ 1 := (Finset.mem_filter.mp hn).2.1.ne_one
    have hpp : p.Prime := hpn ▸ Nat.minFac_prime hn1
    have hset : B.filter (fun n => n.minFac = p)
        = (Finset.Icc 1 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime ∧ n.minFac = p) := by
      rw [hB]; ext m; simp only [Finset.mem_filter]; tauto
    rw [hset]
    exact fiber_sum_le_log X p hpp
  have hdecomp : (∑ n ∈ B, vonMangoldt n)
      = ∑ p ∈ B.image (fun n => n.minFac),
          ∑ n ∈ B.filter (fun n => n.minFac = p), vonMangoldt n := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)]
  rw [hdecomp]
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hcardle : (B.image (fun n => n.minFac)).card ≤ Nat.sqrt X := by
    have hsub : B.image (fun n => n.minFac) ⊆ Finset.Icc 1 (Nat.sqrt X) := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨n, hnB, rfl⟩ := hb
      rw [hB] at hnB
      obtain ⟨hnI, hpp, hnp⟩ := Finset.mem_filter.mp hnB
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hnI
      have h0 : 0 < n := by omega
      have hsq0 : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self h0 hnp
      have hsq : n.minFac * n.minFac ≤ X := by
        have h2 : n.minFac ^ 2 = n.minFac * n.minFac := pow_two _
        omega
      exact Finset.mem_Icc.mpr
        ⟨Nat.Prime.one_le (Nat.minFac_prime hpp.ne_one), Nat.le_sqrt.mpr hsq⟩
    calc (B.image (fun n => n.minFac)).card ≤ (Finset.Icc 1 (Nat.sqrt X)).card :=
          Finset.card_le_card hsub
      _ = Nat.sqrt X := by rw [Nat.card_Icc]; omega
  calc ∑ p ∈ B.image (fun n => n.minFac), ∑ n ∈ B.filter (fun n => n.minFac = p), vonMangoldt n
      ≤ ∑ p ∈ B.image (fun n => n.minFac), Real.log (X : ℝ) := Finset.sum_le_sum hfib
    _ = ((B.image (fun n => n.minFac)).card : ℝ) * Real.log (X : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt X : ℝ) * Real.log (X : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hlogX
          exact_mod_cast hcardle
    _ ≤ Real.sqrt (X : ℝ) * Real.log (X : ℝ) := by
          apply mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hlogX
    _ ≤ 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) := by
          have h1 : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 2) := by
            apply Real.log_le_log (by exact_mod_cast hX0); linarith
          have h2 : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg X
          nlinarith [h1, h2]

private lemma nonprime_le_primepow_sum (q a X : ℕ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime), vonMangoldt n)
      ≤ (∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), vonMangoldt n) := by
  have hA : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime), vonMangoldt n)
      = ∑ n ∈ ((Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime)).filter
          (fun n => vonMangoldt n ≠ 0), vonMangoldt n := by
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro n _
    split_ifs with h
    · rfl
    · exact not_not.mp h
  rw [hA]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => vonMangoldt_nonneg)
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnA, hne⟩ := hn
  rw [Finset.mem_filter] at hnA
  exact Finset.mem_filter.mpr ⟨hnA.1, vonMangoldt_ne_zero_iff.mp hne, hnA.2.2⟩

/-! ### Leaf 1: the mass of the non primes -/

/-- LEAF. Removal of the proper prime powers. The von Mangoldt mass of the non
prime numbers of the residue class of `a` modulo `q` up to `X` is at most
`4 * sqrt X * log (X + 2)`. A non prime carries weight only at a prime power
`p ^ k` with `k` at least two, of weight `log p` at most `log X`, and the powers
up to `X` number about `sqrt X`, which leaves a wide margin at the small `X`
where the two sides are comparable. -/
theorem leaf_nonprime_mass_upper (q a X : ℕ) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime), vonMangoldt n)
      ≤ 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) :=
  le_trans (nonprime_le_primepow_sum q a X) (sum_primepow_nonprime_le X)

/-! ### Leaf 2: the mass of a whole residue class -/

/-- LEAF. The von Mangoldt mass of the residue class of `a` modulo `q` up to the
floor of `C * q ^ L` is at least one hundredth of `X / q`, whenever the modulus is
at least two, `a` is coprime to it, the exponent is at least six and the constant
is at least one. This is the progressions input: the mass of a class is of the
order of `X / phi q`, and `phi q ≤ q` with a relative loss that one hundredth
absorbs once the scale is a fixed power of the modulus. -/
theorem leaf_ap_mass_lower (L C : ℝ) (hL : 6 ≤ L) (hC : 1 ≤ C)
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : Nat.Coprime a q) :
    (∑ n ∈ (Finset.Icc 1 (Nat.floor (C * (q : ℝ) ^ L))).filter (fun n => n % q = a % q),
        vonMangoldt n)
      ≥ (1 / 100) * (Nat.floor (C * (q : ℝ) ^ L) : ℝ) / (q : ℝ) := by
  sorry

/-! ### Helpers for Leaf 3 -/

/-- `log (2 * 10 ^ 20) < 50`, from `exp 50 > (2.718...) ^ 50 > 2 * 10 ^ 20`. -/
private lemma log_two_ten_pow_20_lt : Real.log (2 * (10:ℝ)^20) < 50 := by
  have hpos : (0:ℝ) < 2 * (10:ℝ)^20 := by positivity
  rw [Real.log_lt_iff_lt_exp hpos]
  have hexp : Real.exp 50 = (Real.exp 1)^50 := by
    rw [show (50:ℝ) = ((50:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [hexp]
  have h1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hp : (2.7182818283:ℝ)^50 > 2 * (10:ℝ)^20 := by norm_num
  calc (2:ℝ) * (10:ℝ)^20 < (2.7182818283:ℝ)^50 := hp
    _ < (Real.exp 1)^50 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)

/-- `10 ^ 9 < sqrt (5 * 10 ^ 19)`. -/
private lemma nine_lt_sqrt : (10:ℝ)^9 < Real.sqrt (5*(10:ℝ)^19) := by
  rw [Real.lt_sqrt (by positivity)]
  norm_num

/-- The margin at the scale `X = floor (10 ^ 20 * Q ^ 6)`, for a real modulus `Q` at least two. -/
private lemma scale_margin_core (Q : ℝ) (hQ2 : 2 ≤ Q) :
    400 * Q * Real.log ((Nat.floor ((10:ℝ)^20 * Q^6) : ℝ) + 2)
      < Real.sqrt (Nat.floor ((10:ℝ)^20 * Q^6) : ℝ) := by
  have hQ0 : (0:ℝ) < Q := by linarith
  set K : ℝ := (10:ℝ)^20 * Q^6 with hK
  have hX5 : (8:ℝ) ≤ Q^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hQ2 3
    norm_num at h
    linarith
  have hQ3pos : (0:ℝ) < Q^3 := by positivity
  have hK2 : (2:ℝ) ≤ K := by
    rw [hK]
    nlinarith [hX5]
  have hK0 : (0:ℝ) ≤ K := by linarith
  have hNle : (Nat.floor K : ℝ) ≤ K := Nat.floor_le hK0
  have hNge : K - 1 ≤ (Nat.floor K : ℝ) := by
    have := Nat.lt_floor_add_one K
    linarith
  have hNhalf : K / 2 ≤ (Nat.floor K : ℝ) := by linarith
  have hlogN : Real.log ((Nat.floor K : ℝ) + 2) ≤ Real.log (2 * K) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlogK : Real.log (2 * K) = Real.log (2 * (10:ℝ)^20) + 6 * Real.log Q := by
    rw [hK, show (2:ℝ) * ((10:ℝ)^20 * Q^6) = (2*(10:ℝ)^20) * Q^6 by ring]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    push_cast
    ring
  have hlogQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ0
    linarith
  have hstep : 400 * Q * Real.log ((Nat.floor K : ℝ) + 2) ≤ 400 * Q * (50 + 6*Q) := by
    have h1 : Real.log ((Nat.floor K : ℝ) + 2) ≤ 50 + 6*Q := by
      have h2 := hlogN
      rw [hlogK] at h2
      linarith [h2, hlogQ, log_two_ten_pow_20_lt.le]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hstep2 : 400 * Q * (50 + 6*Q) < (10:ℝ)^9 * Q^3 := by
    nlinarith [hQ2, hQ3pos, hX5]
  have hbig9 : (10:ℝ)^9 * Q^3 < Real.sqrt (5*(10:ℝ)^19) * Q^3 := by
    have := nine_lt_sqrt
    nlinarith [hQ3pos]
  have hsqrt : Real.sqrt (5*(10:ℝ)^19) * Q^3 ≤ Real.sqrt (Nat.floor K : ℝ) := by
    have h2 : Real.sqrt (K/2) = Real.sqrt (5*(10:ℝ)^19) * Q^3 := by
      rw [hK, show (10:ℝ)^20 * Q^6 / 2 = 5*(10:ℝ)^19 * Q^6 by ring]
      rw [Real.sqrt_mul (by positivity)]
      have h3 : Real.sqrt (Q^6) = Q^3 := by
        rw [show Q^6 = (Q^3)^2 by ring, Real.sqrt_sq (by positivity)]
      rw [h3]
    have h4 : Real.sqrt (K/2) ≤ Real.sqrt (Nat.floor K : ℝ) := Real.sqrt_le_sqrt hNhalf
    rw [← h2]
    exact h4
  calc 400 * Q * Real.log ((Nat.floor K : ℝ) + 2) ≤ 400 * Q * (50 + 6*Q) := hstep
    _ < (10:ℝ)^9 * Q^3 := hstep2
    _ < Real.sqrt (5*(10:ℝ)^19) * Q^3 := hbig9
    _ ≤ Real.sqrt (Nat.floor K : ℝ) := hsqrt

/-! ### Leaf 3: the scale at which the two bounds meet -/

/-- LEAF. The scale. There are an exponent `L` at least six and a constant `C` at
least one such that at every modulus `q` at least two the upper bound of the first
leaf, multiplied by the hundredth and by `q`, is smaller than `sqrt` of the
witness `X = floor (C * q ^ L)`: in symbols `400 * q * log (X + 2) < sqrt X`. A
fixed power above the square and a large constant turn the left side into a
logarithmic quantity against a power of `q`. -/
theorem leaf_scale_margin :
    ∃ L C : ℝ, 6 ≤ L ∧ 1 ≤ C ∧ ∀ q : ℕ, 2 ≤ q →
      400 * (q : ℝ) * Real.log ((Nat.floor (C * (q : ℝ) ^ L) : ℝ) + 2)
        < Real.sqrt (Nat.floor (C * (q : ℝ) ^ L) : ℝ) := by
  refine ⟨6, (10:ℝ)^20, by norm_num, by norm_num, ?_⟩
  intro q hq
  set Q : ℝ := (q:ℝ) with hQ
  have hQ2 : (2:ℝ) ≤ Q := by
    rw [hQ]; exact_mod_cast hq
  have hrpow : Q ^ (6:ℝ) = Q^6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow]
  exact scale_margin_core Q hQ2

/-! ### Assembly -/

/-- Exactly the statement of `linnik_weighted_gap150`, proved from the three
leaves above and not from the original theorem. -/
theorem linnik_weighted_gap150_split : ∃ L C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∃ X : ℕ,
      (X : ℝ) ≤ C * (q : ℝ) ^ L ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n := by
  obtain ⟨L, C, hL, hC, hmargin⟩ := leaf_scale_margin
  refine ⟨L, C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro q hq a ha
  set X : ℕ := Nat.floor (C * (q : ℝ) ^ L) with hX
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hbase : (0 : ℝ) ≤ C * (q : ℝ) ^ L :=
    mul_nonneg (le_trans zero_le_one hC) (Real.rpow_nonneg (Nat.cast_nonneg q) L)
  have hXle : (X : ℝ) ≤ C * (q : ℝ) ^ L := by
    rw [hX]
    exact Nat.floor_le hbase
  have hlog : (0 : ℝ) ≤ Real.log ((X : ℝ) + 2) :=
    Real.log_nonneg (by have h : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X; linarith)
  have hm : 400 * (q : ℝ) * Real.log ((X : ℝ) + 2) < Real.sqrt (X : ℝ) := hmargin q hq
  have hsqrtpos : 0 < Real.sqrt (X : ℝ) := by nlinarith [hm, hlog, hqpos]
  have hsq : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg X)
  have hmain : 4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) <
      (1 / 100) * (X : ℝ) / (q : ℝ) := by
    have hden : (0 : ℝ) < 100 * (q : ℝ) := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hm (div_pos hsqrtpos hden)
    have e1 : 400 * (q : ℝ) * Real.log ((X : ℝ) + 2) *
        (Real.sqrt (X : ℝ) / (100 * (q : ℝ))) =
        4 * Real.sqrt (X : ℝ) * Real.log ((X : ℝ) + 2) := by
      field_simp
      ring
    have e2 : Real.sqrt (X : ℝ) * (Real.sqrt (X : ℝ) / (100 * (q : ℝ))) =
        (1 / 100) * (X : ℝ) / (q : ℝ) := by
      field_simp
      nlinarith [hsq]
    rw [e1, e2] at hmul
    exact hmul
  have hnon := leaf_nonprime_mass_upper q a X
  have hlow := leaf_ap_mass_lower L C hL hC q hq a ha
  refine ⟨X, hXle, ?_⟩
  linarith

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.linnik_weighted_gap150_split

