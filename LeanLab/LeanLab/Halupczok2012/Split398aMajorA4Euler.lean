import LeanLab.Halupczok2012.Split398aMajorA4

/-!
Split of the leaf `Split398aMajorA4.singular_ramanujan`, PP1993 page 41 and page 45:
S of 2k is the full Ramanujan series of mu^2 q over phi^2 q times c_q of -2k.
Source: A. Perelli and J. Pintz, J. London Math. Soc. 47, 1993, pages 41 to 49, PP1993.
The term `ramTerm k q` is the summand of `singular_ramanujan`, written verbatim.
Three leaves: `ramTerm_mul_coprime`, multiplicativity in q, `ramTerm_prime`, the local
factor at a prime p, equal to p - 1 or -1 over (p - 1)^2, and `euler_match`, the Euler
product of a multiplicative function supported on squarefree q matching the definition
of S. Proved here: `ramTerm_zero`, `ramTerm_one`, `ramTerm_prime_pow`, the vanishing at
higher prime powers, and `singular_ramanujan_of_leaves`, the assembly, which states the
same proposition as `singular_ramanujan`.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajorA4Euler

open Finset
open scoped Classical ArithmeticFunction.Moebius
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a

/-- The summand of `singular_ramanujan`, PP1993 p. 45: mu^2 q over phi^2 q times c_q of -2k,
with c_q written out as the sum over reduced a of e of a times -2k over q. -/
noncomputable def ramTerm (k q : ℕ) : ℂ :=
  ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
    ∑ a ∈ (Icc 1 q).filter (fun a => a.Coprime q),
      phase ((a : ℝ) * ((-((2 * k : ℕ) : ℤ) : ℤ) : ℝ) / q)

/-- The local factor of PP1993 p. 41 at a prime p for even r = 2k: p - 1 when p divides 2k,
and -1 otherwise, divided by (p - 1)^2. -/
noncomputable def locR (k p : ℕ) : ℂ :=
  (if p ∣ 2 * k then ((p : ℂ) - 1) else -1) / ((p : ℂ) - 1) ^ 2

theorem ramTerm_zero (k : ℕ) : ramTerm k 0 = 0 := by
  simp [ramTerm]

theorem ramTerm_one (k : ℕ) : ramTerm k 1 = 1 := by
  have h : (Icc 1 1).filter (fun a => a.Coprime 1) = {1} := by decide
  simp only [ramTerm, h, sum_singleton, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  simp only [Nat.cast_one, Int.cast_one, one_pow, div_one, one_mul, phase,
    LeanLab.PNTPort.LargeSieve.e]
  push_cast
  have : Complex.I * (2 * Real.pi * (-(2 * (k : ℂ)))) = ((-(2 * k : ℤ)) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, ← Int.cast_neg, Complex.exp_int_mul_two_pi_mul_I]

/-- mu vanishes at p^j for j at least 2, so the term does. -/
theorem ramTerm_prime_pow (k : ℕ) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    ramTerm k (p ^ j) = 0 := by
  have hμ : μ (p ^ j) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp; omega
  simp [ramTerm, hμ]

theorem e_eq_one_iff (x : ℝ) : LeanLab.PNTPort.LargeSieve.e x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold LeanLab.PNTPort.LargeSieve.e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℂ)) = n := by
      apply mul_right_cancel₀ h2
      push_cast at hn ⊢
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem sum_Icc_one_pow (ζ : ℂ) : ∀ n : ℕ, ∑ a ∈ Icc 1 n, ζ ^ a = ∑ a ∈ range n, ζ ^ (a + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_range_succ, sum_Icc_one_pow ζ n]

theorem geom_Icc (ζ : ℂ) (p : ℕ) (hζp : ζ ^ p = 1) (hζ : ζ ≠ 1) :
    ∑ a ∈ Icc 1 p, ζ ^ a = 0 := by
  rw [sum_Icc_one_pow]
  simp_rw [pow_succ, ← sum_mul]
  rw [geom_sum_eq hζ, hζp]; simp

/-- The Ramanujan sum at a prime, PP1993 p. 41: c_p of -2k is p - 1 or -1. -/
theorem ramSum_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑ a ∈ (Icc 1 p).filter (fun a => a.Coprime p),
      phase ((a : ℝ) * ((-((2 * k : ℕ) : ℤ) : ℤ) : ℝ) / p) =
      if p ∣ 2 * k then ((p : ℂ) - 1) else -1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set n : ℝ := ((-((2 * k : ℕ) : ℤ) : ℤ) : ℝ) with hn
  set ζ := LeanLab.PNTPort.LargeSieve.e (n / p) with hζ
  have hfil : (Icc 1 p).filter (fun a => a.Coprime p) = (Icc 1 p).erase p := by
    ext a
    simp only [mem_filter, mem_Icc, mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, hc⟩
      refine ⟨?_, h1, h2⟩
      rintro rfl
      exact hp.ne_one (by simpa using hc)
    · rintro ⟨hne, h1, h2⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      exact hne (le_antisymm h2 (Nat.le_of_dvd (by omega) hd))
  have hterm : ∀ a : ℕ, phase ((a : ℝ) * n / p) = ζ ^ a := by
    intro a
    rw [phase, mul_div_assoc, LeanLab.PNTPort.LargeSieve.e_nat_mul]
  have hζp : ζ ^ p = 1 := by
    rw [← hterm, mul_div_cancel_left₀ _ hp0, hn, phase, LeanLab.PNTPort.LargeSieve.e_int]
  rw [hfil, sum_erase_eq_sub (by simp [hp.one_lt.le, hp.one_le])]
  simp_rw [hterm]
  rw [hζp]
  split_ifs with hd
  · have hζ1 : ζ = 1 := by
      obtain ⟨c, hc⟩ := hd
      rw [hζ, hn, hc]
      have : ((-(((p * c : ℕ)) : ℤ) : ℤ) : ℝ) / p = ((-(c : ℤ) : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, LeanLab.PNTPort.LargeSieve.e_int]
    simp [hζ1]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := (e_eq_one_iff _).mp h1
      apply hd
      have : ((2 * k : ℕ) : ℝ) = ((-m * p : ℤ) : ℝ) := by
        rw [div_eq_iff hp0] at hm
        rw [hn] at hm
        push_cast at hm ⊢
        linarith
      have h' : ((2 * k : ℕ) : ℤ) = -m * p := by exact_mod_cast this
      have : (p : ℤ) ∣ ((2 * k : ℕ) : ℤ) := ⟨-m, by rw [h']; ring⟩
      exact_mod_cast this
    rw [geom_Icc ζ p hζp hζ1]; ring

theorem coprime_mod_iff (x q : ℕ) : Nat.Coprime (x % q) q ↔ Nat.Coprime x q := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

theorem phase_mod (x q : ℕ) (hq : 0 < q) (N : ℤ) :
    phase (((x % q : ℕ) : ℝ) * N / q) = phase ((x : ℝ) * N / q) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hx : (x : ℝ) = ((x % q : ℕ) : ℝ) + q * ((x / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div x q).symm
  have : (x : ℝ) * N / q = ((x % q : ℕ) : ℝ) * N / q + (((x / q : ℕ) * N : ℤ) : ℝ) := by
    rw [hx]; simp only [Int.cast_mul, Int.cast_natCast]; field_simp
  rw [this, phase, phase, LeanLab.PNTPort.LargeSieve.e_add, LeanLab.PNTPort.LargeSieve.e_int,
    mul_one]

/-- Icc 1 q and range q index the same reduced residues. -/
theorem ramSum_Icc_eq_range (N : ℤ) {q : ℕ} (hq : 0 < q) :
    ∑ a ∈ (Icc 1 q).filter (fun a => a.Coprime q), phase ((a : ℝ) * N / q) =
      ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((a : ℝ) * N / q) := by
  apply Finset.sum_nbij' (fun a => a % q) (fun b => if b = 0 then q else b)
  · intro a ha
    simp only [coe_filter, mem_coe, mem_filter, mem_Icc, Set.mem_ofPred_eq, Set.mem_setOf_eq, mem_range] at ha ⊢
    exact ⟨Nat.mod_lt _ hq, (coprime_mod_iff a q).mpr ha.2⟩
  · intro b hb
    simp only [coe_filter, mem_coe, mem_filter, mem_Icc, Set.mem_ofPred_eq, Set.mem_setOf_eq, mem_range] at hb ⊢
    split_ifs with h0
    · subst h0
      have : q = 1 := by simpa using hb.2
      subst this; simp
    · exact ⟨⟨by omega, hb.1.le⟩, hb.2⟩
  · intro a ha
    simp only [coe_filter, mem_coe, mem_filter, mem_Icc, Set.mem_ofPred_eq, Set.mem_setOf_eq] at ha
    by_cases haq : a = q
    · subst haq; simp
    · have : a % q = a := Nat.mod_eq_of_lt (by omega)
      rw [this]; simp; omega
  · intro b hb
    simp only [coe_filter, mem_coe, mem_filter, Set.mem_ofPred_eq, Set.mem_setOf_eq, mem_range] at hb
    split_ifs with h0
    · subst h0; simp
    · exact Nat.mod_eq_of_lt hb.1
  · intro a _
    exact (phase_mod a q hq N).symm

/-- The Ramanujan sum is multiplicative in the modulus, by the CRT map
(a1, a2) to a1 n + a2 m mod m n. -/
theorem ramSum_range_mul (N : ℤ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    ∑ a ∈ (range (m * n)).filter (fun a => a.Coprime (m * n)), phase ((a : ℝ) * N / (m * n : ℕ)) =
      (∑ a ∈ (range m).filter (fun a => a.Coprime m), phase ((a : ℝ) * N / m)) *
      ∑ a ∈ (range n).filter (fun a => a.Coprime n), phase ((a : ℝ) * N / n) := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  set A := (range m).filter (fun a => a.Coprime m)
  set B := (range n).filter (fun a => a.Coprime n)
  set T := (range (m * n)).filter (fun a => a.Coprime (m * n))
  let f : ℕ × ℕ → ℕ := fun x => (x.1 * n + x.2 * m) % (m * n)
  have hinj : Set.InjOn f ↑(A ×ˢ B) := by
    rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb hab
    simp only [A, B, coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_setOf_eq] at ha hb
    have hE : a1 * n + a2 * m ≡ b1 * n + b2 * m [MOD m * n] := hab
    have h1 : a1 * n ≡ b1 * n [MOD m] := by
      have := hE.of_mul_right n
      unfold Nat.ModEq at this ⊢
      simpa [Nat.add_mul_mod_self_right] using this
    have h2 : a2 * m ≡ b2 * m [MOD n] := by
      have := hE.of_mul_left m
      unfold Nat.ModEq at this ⊢
      simpa [Nat.add_mul_mod_self_right, Nat.mul_mod_left, Nat.add_mod] using this
    have e1 := Nat.ModEq.cancel_right_of_coprime (by simpa using h) h1
    have e2 := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using h) h2
    unfold Nat.ModEq at e1 e2
    rw [Nat.mod_eq_of_lt ha.1.1, Nat.mod_eq_of_lt hb.1.1] at e1
    rw [Nat.mod_eq_of_lt ha.2.1, Nat.mod_eq_of_lt hb.2.1] at e2
    simp [e1, e2]
  have hsub : (A ×ˢ B).image f ⊆ T := by
    intro y hy
    simp only [mem_image, mem_product, A, B, mem_filter, mem_range] at hy
    obtain ⟨⟨a1, a2⟩, ⟨⟨_, c1⟩, ⟨_, c2⟩⟩, rfl⟩ := hy
    simp only [T, f, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ hmn, (coprime_mod_iff _ _).mpr ?_⟩
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [← coprime_mod_iff, Nat.add_mul_mod_self_right, coprime_mod_iff]
      exact Nat.coprime_mul_iff_left.mpr ⟨c1, h.symm⟩
    · rw [← coprime_mod_iff, add_comm, Nat.add_mul_mod_self_right, coprime_mod_iff]
      exact Nat.coprime_mul_iff_left.mpr ⟨c2, h⟩
  have hcard : ∀ q, ((range q).filter (fun a => a.Coprime q)).card = Nat.totient q := by
    intro q
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply filter_congr
    intro x _
    exact Nat.coprime_comm
  have himg : (A ×ˢ B).image f = T := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn hinj, card_product, hcard, hcard, hcard, Nat.totient_mul h]
  rw [← himg, sum_image hinj, sum_product, sum_mul_sum]
  apply sum_congr rfl
  intro a1 _
  apply sum_congr rfl
  intro a2 _
  rw [phase_mod _ _ hmn N]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (((a1 * n + a2 * m : ℕ)) : ℝ) * N / (m * n : ℕ) = (a1 : ℝ) * N / m + (a2 : ℝ) * N / n := by
    push_cast; field_simp
  rw [this, phase, LeanLab.PNTPort.LargeSieve.e_add]
  rfl

/-- LEAF: PP1993 p. 45, the Ramanujan sum c_q of n is multiplicative in q and so are
mu^2 q and phi^2 q, hence the term mu^2 q over phi^2 q times c_q of -2k is multiplicative,
the standard fact used on p. 41. Class MEDIUM. -/
theorem ramTerm_mul_coprime (k : ℕ) {m n : ℕ} (h : m.Coprime n) :
    ramTerm k (m * n) = ramTerm k m * ramTerm k n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [ramTerm_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ramTerm_zero]
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  unfold ramTerm
  rw [ramSum_Icc_eq_range _ hm, ramSum_Icc_eq_range _ hn, ramSum_Icc_eq_range _ hmn]
  have hS := ramSum_range_mul ((-((2 * k : ℕ) : ℤ) : ℤ)) hm hn h
  push_cast at hS ⊢
  rw [hS, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  ring

/-- LEAF: PP1993 p. 41, the local factor: for a prime p, c_p of -2k equals p - 1 when p
divides 2k and -1 otherwise, so the term at p is that over (p - 1)^2, since mu^2 p = 1 and
phi p = p - 1. Class MEDIUM. -/
theorem ramTerm_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : ramTerm k p = locR k p := by
  unfold ramTerm locR
  rw [ramSum_prime k hp, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le]
  push_cast
  ring

/-- LEAF: PP1993 p. 41 display 2 and p. 45, the Euler product: a function on q that is 0
at 0, 1 at 1, multiplicative on coprime pairs, 0 at higher prime powers and equal to the
local factor `locR k p` at primes has absolutely convergent sum equal to the product over
p of 1 + locR k p, which is 2 at p = 2, p over p - 1 at odd p dividing k and
1 - 1 over (p - 1)^2 otherwise, that is S of 2k for k at least 1. Class HARD. -/
theorem euler_match (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℂ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n)
    (hpp : ∀ p j : ℕ, p.Prime → 2 ≤ j → f (p ^ j) = 0)
    (hp : ∀ p : ℕ, p.Prime → f p = locR k p) :
    HasSum f ((LeanLab.Halupczok2012.S (2 * k) : ℝ) : ℂ) := by
  sorry

/-- Assembly: the statement of `Split398aMajorA4.singular_ramanujan`, from the three leaves. -/
theorem singular_ramanujan_of_leaves (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun q : ℕ => ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ∑ a ∈ (Icc 1 q).filter (fun a => a.Coprime q),
        phase ((a : ℝ) * ((-((2 * k : ℕ) : ℤ) : ℤ) : ℝ) / q))
      ((LeanLab.Halupczok2012.S (2 * k) : ℝ) : ℂ) :=
  euler_match k hk (ramTerm k) (ramTerm_zero k) (ramTerm_one k)
    (fun _ _ h => ramTerm_mul_coprime k h) (fun _ _ hp hj => ramTerm_prime_pow k hp hj)
    (fun _ hp => ramTerm_prime k hp)

end LeanLab.Halupczok2012.Split398aMajorA4Euler
