/-
AI-written Lean code, Claude, 2026-10-21, run 20261020T2303Z-14596, unit U-1305.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720.

`DDMain.NathansonRd`, the remainder bound `|r_d(A)| ≤ 2^{ω(d)}` for `d = ∏ s`, `s` a finite set of
primes, PROVED here for every `N`, so the input drops out of Theorem 3.3 for `N ≥ 10^200`.

The argument. For a prime `p` put `m_p = 4` if `p = 2` and `N` is odd, else `m_p = p`. For
`1 ≤ n ≤ N - 1`, `p ∣ aₙ` iff `n ≡ 0` or `n ≡ N` mod `m_p`, so `d ∣ aₙ` iff `n` lies in a set of
residues mod `M = ∏ m_p` which by CRT has `c = ∏ c_p` elements, `c_p ∈ {1, 2}` and `c_p / m_p = g(p)`.
A set periodic mod `M` with `c` residues has `X c / M + θ` elements in `[1, X]`, `|θ| ≤ c`.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDMain

open Real Finset
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDMain

noncomputable section
namespace LeanLab.AlmostPrimes.DDNathanson

/-! ### Counting a periodic set in `[1, X]` -/

lemma count_add_period (P : ℕ → Prop) [DecidablePred P] (M : ℕ)
    (hper : ∀ n, P (n + M) ↔ P n) (Y : ℕ) :
    Nat.count P (M + Y) = Nat.count P M + Nat.count P Y := by
  rw [Nat.count_add]
  congr 1
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [add_comm]
  exact hper k

/-- A set periodic mod `M` with `c = count P M` residues has `X c / M + θ` elements below `X`,
`|θ| ≤ c`. -/
lemma periodic_bound (P : ℕ → Prop) [DecidablePred P] (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, P (n + M) ↔ P n) (X : ℕ) :
    |(Nat.count P X : ℝ) - X * Nat.count P M / M| ≤ Nat.count P M := by
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hc0 : (0 : ℝ) ≤ Nat.count P M := Nat.cast_nonneg _
  by_cases hX : X < M
  · have h1 : Nat.count P X ≤ Nat.count P M := Nat.count_monotone P hX.le
    have h1' : (Nat.count P X : ℝ) ≤ Nat.count P M := by exact_mod_cast h1
    have h2 : (X : ℝ) * Nat.count P M / M ≤ Nat.count P M := by
      rw [div_le_iff₀ hM']
      have : (X : ℝ) ≤ M := by exact_mod_cast hX.le
      nlinarith
    have h3 : 0 ≤ (X : ℝ) * Nat.count P M / M := by positivity
    have h4 : (0 : ℝ) ≤ Nat.count P X := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  · push Not at hX
    obtain ⟨Y, rfl⟩ := Nat.exists_eq_add_of_le hX
    have hih := ih Y (by omega)
    rw [count_add_period P M hper Y]
    push_cast
    have e : ((Nat.count P M : ℝ) + Nat.count P Y) - ((M : ℝ) + Y) * Nat.count P M / M =
        (Nat.count P Y : ℝ) - Y * Nat.count P M / M := by
      field_simp
      ring
    rw [e]
    exact hih

lemma card_Icc_eq_count (P : ℕ → Prop) [DecidablePred P] (X : ℕ) :
    #{n ∈ Icc 1 X | P n} = Nat.count (fun k => P (k + 1)) X := by
  rw [Nat.count_eq_card_filter_range]
  symm
  apply Finset.card_nbij' (fun k => k + 1) (fun n => n - 1)
  · intro a ha
    simp only [mem_coe, mem_filter, mem_range, mem_Icc] at ha ⊢
    exact ⟨⟨by omega, by omega⟩, ha.2⟩
  · intro a ha
    simp only [mem_coe, mem_filter, mem_range, mem_Icc] at ha ⊢
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel ha.1.1]
    exact ha.2
  · intro a _
    simp
  · intro a ha
    simp only [mem_coe, mem_filter, mem_Icc] at ha
    simp only
    omega

lemma count_shift (P : ℕ → Prop) [DecidablePred P] (M : ℕ) (hper : ∀ n, P (n + M) ↔ P n) :
    Nat.count (fun k => P (k + 1)) M = Nat.count P M := by
  have h1 := Nat.count_add P 1 M
  have h2 := Nat.count_succ P M
  rw [Nat.count_one] at h1
  have h3 : Nat.count (fun k => P (1 + k)) M = Nat.count (fun k => P (k + 1)) M := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    apply filter_congr
    intro k _
    rw [add_comm]
  have h4 : P M ↔ P 0 := by
    have := hper 0
    rwa [zero_add] at this
  rw [add_comm 1 M, h3] at h1
  by_cases h0 : P 0
  · rw [if_pos h0] at h1
    rw [if_pos (h4.mpr h0)] at h2
    omega
  · rw [if_neg h0] at h1
    rw [if_neg (fun h => h0 (h4.mp h))] at h2
    omega

/-- **The interval count.** A set periodic mod `M` with `c` residues in `[0, M)` has
`X c / M + θ` elements in `[1, X]`, `|θ| ≤ c`. PROVED. -/
theorem periodic_Icc (P : ℕ → Prop) [DecidablePred P] (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, P (n + M) ↔ P n) (X : ℕ) :
    |((#{n ∈ Icc 1 X | P n} : ℕ) : ℝ) - X * (#{r ∈ range M | P r} : ℕ) / M| ≤
      (#{r ∈ range M | P r} : ℕ) := by
  have hper' : ∀ n, P (n + M + 1) ↔ P (n + 1) := by
    intro n
    rw [show n + M + 1 = (n + 1) + M by ring]
    exact hper (n + 1)
  have hb := periodic_bound (fun k => P (k + 1)) M hM hper' X
  rw [card_Icc_eq_count, ← Nat.count_eq_card_filter_range, ← count_shift P M hper]
  exact hb

/-! ### CRT count -/

/-- For coprime `m, n`, the residues `r < mn` with `A (r mod m)` and `B (r mod n)` number
`#A · #B`. PROVED, from `Nat.chineseRemainder`. -/
theorem crt_count {m n : ℕ} (co : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n)
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    #{r ∈ range (m * n) | A (r % m) ∧ B (r % n)} =
      #{a ∈ range m | A a} * #{b ∈ range n | B b} := by
  rw [← Finset.card_product]
  apply Finset.card_nbij' (fun r => (r % m, r % n))
    (fun ab => (Nat.chineseRemainder co ab.1 ab.2 : ℕ))
  · intro r hr
    simp only [mem_coe, mem_filter, mem_range, mem_product] at hr ⊢
    exact ⟨⟨Nat.mod_lt _ hm, hr.2.1⟩, ⟨Nat.mod_lt _ hn, hr.2.2⟩⟩
  · intro ab hab
    simp only [mem_coe, mem_filter, mem_range, mem_product] at hab ⊢
    have h1 : (Nat.chineseRemainder co ab.1 ab.2 : ℕ) % m = ab.1 % m :=
      (Nat.chineseRemainder co ab.1 ab.2).2.1
    have h2 : (Nat.chineseRemainder co ab.1 ab.2 : ℕ) % n = ab.2 % n :=
      (Nat.chineseRemainder co ab.1 ab.2).2.2
    refine ⟨Nat.chineseRemainder_lt_mul co _ _ hm.ne' hn.ne', ?_, ?_⟩
    · rw [h1, Nat.mod_eq_of_lt hab.1.1]; exact hab.1.2
    · rw [h2, Nat.mod_eq_of_lt hab.2.1]; exact hab.2.2
  · intro r hr
    simp only [mem_coe, mem_filter, mem_range] at hr
    have hu := Nat.chineseRemainder_modEq_unique co (a := r % m) (b := r % n) (z := r)
      (Nat.mod_modEq r m).symm (Nat.mod_modEq r n).symm
    have hlt := Nat.chineseRemainder_lt_mul co (r % m) (r % n) hm.ne' hn.ne'
    unfold Nat.ModEq at hu
    rw [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hlt] at hu
    exact hu.symm
  · intro ab hab
    simp only [mem_coe, mem_product, mem_filter, mem_range] at hab
    have h1 : (Nat.chineseRemainder co ab.1 ab.2 : ℕ) % m = ab.1 % m :=
      (Nat.chineseRemainder co ab.1 ab.2).2.1
    have h2 : (Nat.chineseRemainder co ab.1 ab.2 : ℕ) % n = ab.2 % n :=
      (Nat.chineseRemainder co ab.1 ab.2).2.2
    simp only
    rw [h1, h2, Nat.mod_eq_of_lt hab.1.1, Nat.mod_eq_of_lt hab.2.1]

/-! ### The local conditions -/

/-- The exponent: `2` for `p = 2` and odd `N`, else `1`. -/
def ep (N p : ℕ) : ℕ := if p = 2 ∧ ¬ Even N then 2 else 1

/-- The local modulus `m_p = p^{ep}`. -/
def mp (N p : ℕ) : ℕ := p ^ ep N p

/-- The local condition `n ≡ 0` or `n ≡ N` mod `m_p`. -/
def Q (N p n : ℕ) : Prop := n % mp N p = 0 ∨ n % mp N p = N % mp N p

instance (N p : ℕ) : DecidablePred (Q N p) := fun n => by unfold Q; infer_instance

/-- All the local conditions for `p ∈ s`. -/
def Ps (N : ℕ) (s : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ s, Q N p n

instance (N : ℕ) (s : Finset ℕ) : DecidablePred (Ps N s) := fun n => by unfold Ps; infer_instance

/-- The modulus `M = ∏ m_p`. -/
def Ms (N : ℕ) (s : Finset ℕ) : ℕ := ∏ p ∈ s, mp N p

lemma mp_pos (N p : ℕ) (hp : p.Prime) : 0 < mp N p := pow_pos hp.pos _

lemma Ms_pos (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : 0 < Ms N s :=
  Finset.prod_pos fun p hp => mp_pos N p (hs p hp)

lemma dvd_sub_iff_mod {p n N : ℕ} (h : n ≤ N) : p ∣ N - n ↔ n % p = N % p := by
  rw [← Nat.modEq_iff_dvd' h]
  rfl

/-- For `n ≤ N` and a prime `p`, `p ∣ aₙ` iff `n ≡ 0` or `n ≡ N` mod `m_p`. PROVED. -/
theorem dvd_aSeq_iff {N p n : ℕ} (hp : p.Prime) (hn : n ≤ N) :
    p ∣ Campbell2026.aSeq N n ↔ Q N p n := by
  unfold Q mp ep Campbell2026.aSeq
  by_cases hE : Even N
  · rw [if_pos hE, if_neg (fun h => h.2 hE), pow_one, hp.dvd_mul, Nat.dvd_iff_mod_eq_zero,
      dvd_sub_iff_mod hn]
  · rw [if_neg hE]
    have hNo : N % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hE)
    have h2 : 2 ∣ n * (N - n) := by
      rcases Nat.even_or_odd n with h | h
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
      · apply Dvd.dvd.mul_left
        have := Nat.odd_iff.mp h
        omega
    by_cases hp2 : p = 2
    · rw [if_pos ⟨hp2, hE⟩]
      subst hp2
      rw [Nat.dvd_div_iff_mul_dvd h2]
      norm_num
      rcases Nat.even_or_odd n with h | h
      · have hn2 := Nat.even_iff.mp h
        have hco : Nat.Coprime 4 (N - n) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          apply Nat.Coprime.pow_left
          rw [Nat.coprime_two_left, Nat.odd_iff]
          omega
        rw [hco.dvd_mul_right]
        omega
      · have hn2 := Nat.odd_iff.mp h
        have hco : Nat.Coprime 4 n := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          apply Nat.Coprime.pow_left
          rw [Nat.coprime_two_left]
          exact h
        rw [hco.dvd_mul_left]
        omega
    · rw [if_neg (fun h => hp2 h.1), pow_one]
      obtain ⟨k, hk⟩ := h2
      have hco : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      have e : p ∣ n * (N - n) ↔ p ∣ k := by rw [hk]; exact hco.dvd_mul_left
      rw [hk, Nat.mul_div_cancel_left k two_pos, ← e, hp.dvd_mul,
        Nat.dvd_iff_mod_eq_zero, dvd_sub_iff_mod hn]

lemma prod_dvd_iff {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    (∏ p ∈ s, p) ∣ m ↔ ∀ p ∈ s, p ∣ m :=
  ⟨fun h p hp => dvd_trans (Finset.dvd_prod_of_mem _ hp) h,
   fun h => Finset.prod_primes_dvd m (fun p hp => (hs p hp).prime) h⟩

lemma Q_mod (N p r : ℕ) : Q N p (r % mp N p) ↔ Q N p r := by
  unfold Q; rw [Nat.mod_mod]

lemma Q_of_dvd {N p r k : ℕ} (h : mp N p ∣ k) : Q N p (r % k) ↔ Q N p r := by
  unfold Q; rw [Nat.mod_mod_of_dvd r h]

lemma Ps_mod (N : ℕ) (s : Finset ℕ) (r : ℕ) : Ps N s (r % Ms N s) ↔ Ps N s r := by
  unfold Ps
  exact forall_congr' fun p => imp_congr_right fun hp =>
    Q_of_dvd (Finset.dvd_prod_of_mem _ hp)

lemma Ps_period (N : ℕ) (s : Finset ℕ) (n : ℕ) : Ps N s (n + Ms N s) ↔ Ps N s n := by
  rw [← Ps_mod N s (n + Ms N s), Nat.add_mod_right, Ps_mod]

/-- The residue count is multiplicative over `s`. PROVED by induction with `crt_count`. -/
theorem count_Ps (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    #{r ∈ range (Ms N s) | Ps N s r} = ∏ p ∈ s, #{t ∈ range (mp N p) | Q N p t} := by
  induction s using Finset.induction_on with
  | empty => simp [Ms, Ps]
  | insert p s hps ih =>
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    have hp : p.Prime := hs p (mem_insert_self p s)
    rw [prod_insert hps, ← ih hs']
    have hMs : Ms N (insert p s) = mp N p * Ms N s := by unfold Ms; rw [prod_insert hps]
    have hco : Nat.Coprime (mp N p) (Ms N s) := by
      unfold Ms
      apply Nat.Coprime.prod_right
      intro q hq
      unfold mp
      apply Nat.coprime_pow_primes _ _ hp (hs' q hq)
      rintro rfl
      exact hps hq
    rw [hMs, ← crt_count hco (mp_pos N p hp) (Ms_pos N s hs') (Q N p) (Ps N s)]
    congr 1
    apply filter_congr
    intro r _
    rw [Q_mod, Ps_mod]
    unfold Ps
    simp only [forall_mem_insert]

lemma card_Q (N p : ℕ) (hp : p.Prime) :
    #{t ∈ range (mp N p) | Q N p t} = if N % mp N p = 0 then 1 else 2 := by
  have hm := mp_pos N p hp
  have hNm : N % mp N p < mp N p := Nat.mod_lt _ hm
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    rw [mem_filter, mem_range, mem_singleton]
    unfold Q
    constructor
    · rintro ⟨ht, h1⟩
      rw [Nat.mod_eq_of_lt ht] at h1
      omega
    · rintro rfl
      exact ⟨hm, Or.inl (Nat.zero_mod _)⟩
  · rw [Finset.card_eq_two]
    refine ⟨0, N % mp N p, by omega, ?_⟩
    ext t
    rw [mem_filter, mem_range, mem_insert, mem_singleton]
    unfold Q
    constructor
    · rintro ⟨ht, h1⟩
      rw [Nat.mod_eq_of_lt ht] at h1
      exact h1
    · rintro (rfl | rfl)
      · exact ⟨hm, Or.inl (Nat.zero_mod _)⟩
      · exact ⟨hNm, Or.inr (Nat.mod_mod _ _)⟩

lemma cp_div (N p : ℕ) (hp : p.Prime) :
    ((#{t ∈ range (mp N p) | Q N p t} : ℕ) : ℝ) / (mp N p : ℝ) = g N p := by
  rw [card_Q N p hp]
  by_cases hp2 : p = 2
  · subst hp2
    unfold g mp ep
    by_cases hE : Even N
    · have h0 : N % 2 = 0 := Nat.even_iff.mp hE
      simp [hE, h0]
    · have h1 : N % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hE)
      have h4 : N % 4 ≠ 0 := by omega
      simp [hE, h4]
      norm_num
  · have hm : mp N p = p := by unfold mp ep; rw [if_neg (fun h => hp2 h.1), pow_one]
    rw [hm]
    unfold g
    rw [if_neg hp2]
    by_cases hd : p ∣ N
    · rw [if_pos hd, if_pos (Nat.dvd_iff_mod_eq_zero.mp hd)]
      norm_num
    · rw [if_neg hd, if_neg (fun h => hd (Nat.dvd_iff_mod_eq_zero.mpr h))]
      norm_num

/-! ### `NathansonRd` -/

/-- **`NathansonRd`, PROVED**: `|r_d(A)| ≤ 2^{ω(d)}` for `d = ∏ s`, `s` any finite set of
primes, every `N`. -/
theorem nathansonRd : NathansonRd := by
  unfold NathansonRd
  intro N s hs
  have hM := Ms_pos N s hs
  have hAd : Ad N (∏ p ∈ s, p) = #{n ∈ Icc 1 (N - 1) | Ps N s n} := by
    unfold Ad
    congr 1
    apply filter_congr
    intro n hn
    rw [mem_Icc] at hn
    rw [prod_dvd_iff hs]
    exact forall_congr' fun p => imp_congr_right fun hp => dvd_aSeq_iff (hs p hp) (by omega)
  have hb := periodic_Icc (Ps N s) (Ms N s) hM (Ps_period N s) (N - 1)
  have hc := count_Ps N s hs
  have hg : gd N s = ((#{r ∈ range (Ms N s) | Ps N s r} : ℕ) : ℝ) / (Ms N s : ℝ) := by
    rw [hc]
    unfold gd Ms
    push_cast
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    have := cp_div N p (hs p hp)
    exact this.symm
  have hle : #{r ∈ range (Ms N s) | Ps N s r} ≤ 2 ^ s.card := by
    rw [hc]
    apply Finset.prod_le_pow_card
    intro p hp
    rw [card_Q N p (hs p hp)]
    split_ifs <;> norm_num
  have hle' : ((#{r ∈ range (Ms N s) | Ps N s r} : ℕ) : ℝ) ≤ (2 : ℝ) ^ s.card := by
    exact_mod_cast hle
  unfold rd
  rw [hAd, hg]
  unfold Xc
  have e : (((N - 1 : ℕ) : ℝ)) * (((#{r ∈ range (Ms N s) | Ps N s r} : ℕ) : ℝ) / (Ms N s : ℝ)) =
      ((N - 1 : ℕ) : ℝ) * ((#{r ∈ range (Ms N s) | Ps N s r} : ℕ) : ℝ) / (Ms N s : ℝ) := by
    ring
  rw [e]
  exact le_trans hb hle'

/-! ### Theorem 3.3 without `NathansonRd` -/

/-- **Theorem 3.3 for `N ≥ 10^200`**: `N = a + b` with `Ω(ab) ≤ 39` for even `N`, `≤ 40` for odd
`N`. CONDITIONAL ON `RSHyp`, `RSRecip`, `SelbergThm13` only. -/
theorem theorem3_3_large_of_RS (hRS : DDLemma21All.RSHyp) (hRec : RSRecip)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  theorem3_3_large hRS hRec nathansonRd hSel N hN

/-- **Theorem 3.3 for every `N ≥ 2`**. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RSHyp`,
`RSRecip`, `SelbergThm13`. -/
theorem theorem3_3_of_RS (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  theorem3_3 hG hV hRS hRec nathansonRd hSel

/-- **Theorem 1.2**, same five inputs. -/
theorem theorem1_2_of_RS (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N :=
  theorem1_2 hG hV hRS hRec nathansonRd hSel

/-! ### Vacuity check -/

/-- A concrete nonzero remainder, so `rd` is not identically zero: at `N = 7`, `s = {2}`,
`X = 6`, `A_2 = {n : 4 ∣ n(7-n)} = {3, 4}`, so `r_2 = 2 - 3 = -1`. -/
theorem rd_example : rd 7 {2} = -1 := by
  unfold rd Ad Xc gd g
  have : ((Icc 1 (7 - 1)).filter (fun n => (∏ p ∈ ({2} : Finset ℕ), p) ∣
      Campbell2026.aSeq 7 n)).card = 2 := by decide
  rw [this]
  norm_num

#print axioms periodic_Icc
#print axioms crt_count
#print axioms dvd_aSeq_iff
#print axioms count_Ps
#print axioms nathansonRd
#print axioms theorem3_3_large_of_RS
#print axioms theorem3_3_of_RS
#print axioms theorem1_2_of_RS
#print axioms rd_example

end LeanLab.AlmostPrimes.DDNathanson
