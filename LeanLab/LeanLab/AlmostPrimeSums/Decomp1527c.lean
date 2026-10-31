/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file c of three.

Chen's lower bound from the linear sieve, in the switching form of Bordignon-Johnston-
Starichkova (arXiv 2207.09452, Lemma 37, Theorems 44, 50, 51, Lemma 52; Nathanson, Additive
Number Theory: The Classical Bases, Theorem 10.2) with `z = N^{1/8}`, `y = N^{1/3}`, sieve
level `D = N^{1/2}/(log N)^B`, and the normalisation `M(N) = 2e^γ U_N N / log² N`, so that
`S(A,P(z)) ≈ 2 log 3 · M`, `½ Σ_q S(A_q,P(z)) ≈ log 6 · M`, `½ S(B,P(y)) ≈ c̄ · M`,
`c̄ = ∫_{1/8}^{1/3} log(2-3β)/(β(1-β)) dβ = 0.3630837`, margin `log(3/2) − c̄ = 0.0423814`.
Chen's own cut-off is `z = N^{1/10}` with sharper weights and gives `0.67`; the `N^{1/8}` form
is the shortest complete route and is what the existing lab file `Chen1973.lean` uses.

The level of distribution enters as two explicit hypotheses:
* `LevelBV`: the Bombieri-Vinogradov theorem for primes, level `x^{1/2}/(log x)^B`
  (Iwaniec-Kowalski Theorem 17.1; Halberstam-Richert ch. 3; Davenport ch. 28), with
  `π(y)/φ(q)` in place of `li(y)/φ(q)`, which changes the sum by `O(x e^{-c√log x} log x)`;
* `LevelBVTriples`: the Bombieri-Vinogradov theorem for the Chen sequence
  `m = p₁p₂p₃`, `N^{1/8} ≤ p₁ < N^{1/3} ≤ p₂ ≤ p₃`, `m < N`, `(m, N) = 1`, the input of the
  switching principle (Bombieri's theorem for convolutions, Motohashi 1976; Pan-Ding-Wang 1975;
  Halberstam-Richert ch. 11; Iwaniec-Kowalski Theorem 17.4).
The assemblies `chen_lower_conditional` and `chen_conditional` are CONDITIONAL ON both.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.ChenExplicit.Bridge
import LeanLab.ChenExplicit.Reductions
import LeanLab.AlmostPrimeSums.Decomp1527b
import LeanLab.ChenExplicit.BJSCbar
import LeanLab.ChenExplicit.Assembly
import LeanLab.PNTPort.BV.Helpers
import LeanLab.AlmostPrimes.Decomp1528b
import LeanLab.ChenPrimeExceptional.Task101MertensLimit

namespace LeanLab.AlmostPrimeSums.Decomp1527c
open Finset Real Filter Topology LeanLab.ChenExplicit
attribute [local instance] Classical.propDecidable

/-! ### Definitions -/

/-- `π(y; q, a)`: primes `p ≤ y` with `p ≡ a (mod q)`. -/
noncomputable def primesAP (y q a : ℕ) : ℕ :=
  #((range (y + 1)).filter fun p => p.Prime ∧ p % q = a % q)

/-- **Bombieri-Vinogradov, level `x^{1/2}/(log x)^B`**: for every `A > 0` there are `B, C` with
`Σ_{q ≤ √x/(log x)^B} max_{y ≤ x} max_{(a,q)=1} |π(y;q,a) − π(y)/φ(q)| ≤ C x/(log x)^A`
for all `x ≥ 2`; the maxima are written as arbitrary choices `y q ≤ x`, `(a q, q) = 1`.
Iwaniec-Kowalski Theorem 17.1; Davenport ch. 28. -/
def LevelBV : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ y a : ℕ → ℕ,
    (∀ q, y q ≤ x) → (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Icc 1 ⌊√(x : ℝ) / log x ^ B⌋₊,
      |(primesAP (y q) q (a q) : ℝ) - (Nat.primeCounting (y q) : ℝ) / (q.totient : ℝ)|
      ≤ C * x / log x ^ A

/-- Chen's switched sequence `T`: `m = p₁p₂p₃ < N`, `(m, N) = 1`, `z ≤ p₁ < y ≤ p₂ ≤ p₃`;
`B = {N − m : m ∈ T}` is the lab's `BSet`, BJS (108). -/
noncomputable def TSet (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (range N).filter fun m => Nat.Coprime m N ∧ ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
    z ≤ p₁ ∧ (p₁ : ℝ) < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧ m = p₁ * p₂ * p₃

/-- **Bombieri-Vinogradov for the Chen sequence `T` at `z = N^{1/8}`, `y = N^{1/3}`**: for every
`A > 0` there are `B, C` with
`Σ_{q ≤ √N/(log N)^B} max_{(a,q)=1} |#{m ∈ T : m ≡ a (q)} − #{m ∈ T : (m,q)=1}/φ(q)| ≤ C N/(log N)^A`.
Motohashi 1976; Iwaniec-Kowalski Theorem 17.4; Halberstam-Richert ch. 11. -/
def LevelBVTriples : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊,
      |(#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
          fun m => m % q = a q % q) : ℝ)
        - (#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
          fun m => Nat.Coprime m q) : ℝ) / (q.totient : ℝ)|
      ≤ C * N / log N ^ A

/-- The normalisation `M(N) = 2 e^γ U_N N / log² N = 4 C_N N / log² N`. -/
noncomputable def Mchen (N : ℕ) : ℝ :=
  2 * exp eulerMascheroniConstant * U N * N / log N ^ 2

/-- `M(N) > 0` for `N ≥ 2`. -/
theorem Mchen_pos (N : ℕ) (hN : 2 ≤ N) : 0 < Mchen N := by
  unfold Mchen
  have hU := U_pos N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  positivity

/-! ### Switching bookkeeping -/

/-- LEAF. Switching: `B = {N − m : m ∈ T}` as finite sets, from the definitions of `BSet`,
`InB` and `TSet`, BJS (108). Nathanson Theorem 10.2 proof; Halberstam-Richert ch. 11, p. 338.
Unit U-1527. -/
theorem bset_eq_image (N : ℕ) (z y : ℝ) :
    BSet N z y = (TSet N z y).image (fun m => N - m) := by
  ext b
  simp only [BSet, InB, TSet, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨hbN, ⟨p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, hlt, hcop, rfl⟩⟩
    refine ⟨p1 * p2 * p3, ⟨hlt, hcop, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, rfl⟩, rfl⟩
  · rintro ⟨m, ⟨hmN, hcop, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, rfl⟩, rfl⟩
    have hpos : 0 < p1 * p2 * p3 := Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos
    have h1 : N - p1 * p2 * p3 < N := Nat.sub_lt (by omega) hpos
    refine ⟨h1, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, hmN, hcop, rfl⟩

/-- LEAF. Switching: `|B| = |T|`, since `m ↦ N − m` is injective on `m < N`.
Halberstam-Richert ch. 11, p. 338. Unit U-1527. -/
theorem card_bset (N : ℕ) (z y : ℝ) : #(BSet N z y) = #(TSet N z y) := by
  rw [bset_eq_image N z y, card_image_of_injOn]
  intro a ha b hb hab
  dsimp only at hab
  have h1 : a < N := by
    have := (mem_filter.1 ha).1
    exact mem_range.1 this
  have h2 : b < N := by
    have := (mem_filter.1 hb).1
    exact mem_range.1 this
  omega

/-- LEAF. Switching of divisibility into congruence, the heart of Chen's switching principle:
`#{b ∈ B : d ∣ b} = #{m ∈ T : m ≡ N (mod d)}`, because `d ∣ N − m ↔ m ≡ N (mod d)` for `m ≤ N`.
Halberstam-Richert ch. 11, p. 338 bookkeeping. Unit U-1527. -/
theorem card_bset_dvd (N : ℕ) (z y : ℝ) (d : ℕ) :
    #((BSet N z y).filter (d ∣ ·)) = #((TSet N z y).filter fun m => m % d = N % d) := by
  rw [bset_eq_image N z y]
  rw [filter_image]
  have H : ((TSet N z y).filter fun x => d ∣ N - x) = (TSet N z y).filter fun m => m % d = N % d := by
    apply filter_congr
    intro x hx
    have h1 : x ≤ N := by
      have := (mem_filter.1 hx).1
      exact le_of_lt (mem_range.1 this)
    have hdvd : d ∣ N - x ↔ x ≡ N [MOD d] := (Nat.modEq_iff_dvd' h1).symm
    have hmodeq : x ≡ N [MOD d] ↔ x % d = N % d := Iff.rfl
    rw [hdvd, hmodeq]
  rw [H]
  apply card_image_of_injOn
  intro a ha b hb hab
  dsimp only at hab
  have h1 : a < N := by
    have := (mem_filter.1 (mem_filter.1 ha).1).1
    exact mem_range.1 this
  have h2 : b < N := by
    have := (mem_filter.1 (mem_filter.1 hb).1).1
    exact mem_range.1 this
  omega

/-- LEAF. On `B`, sifting by the primes `r < y` with `r ∤ N` is the same as sifting by all
primes `r < y`: if `r ∣ N` and `r ∣ N − m` then `r ∣ m`, against `(m, N) = 1`. BJS (109).
Unit U-1527. -/
theorem siftedBy_iff_of_mem_bset {N : ℕ} {z y : ℝ} {b : ℕ} (hb : b ∈ BSet N z y) :
    SiftedBy N y b ↔ ∀ r : ℕ, r.Prime → (r : ℝ) < y → ¬ r ∣ b := by
  unfold SiftedBy
  constructor
  · intro h r hr hy hrb
    by_cases hN : r ∣ N
    · have hInB : InB N z y b := (mem_filter.1 hb).2
      obtain ⟨p1, p2, p3, hp1, hp2, hp3, hz1, hz2, hy2, hy3, hlt, hcop, rfl⟩ := hInB
      have h1 : r ∣ N - p1 * p2 * p3 := hrb
      have h2 : r ∣ p1 * p2 * p3 := by
        have h3 : p1 * p2 * p3 + (N - p1 * p2 * p3) = N := by omega
        have h4 : r ∣ p1 * p2 * p3 + (N - p1 * p2 * p3) := by
          rw [h3]
          exact hN
        exact (Nat.dvd_add_left h1).mp h4
      have h3 : r ∣ Nat.gcd (p1 * p2 * p3) N := Nat.dvd_gcd h2 hN
      have h4 : Nat.gcd (p1 * p2 * p3) N = 1 := hcop
      rw [h4] at h3
      exact hr.not_dvd_one h3
    · exact h r hr hy hN hrb
  · intro h r hr hy hN hrb
    exact h r hr hy hrb

/-- LEAF. Sieve setup for `A = {N − p}`: `|A_d| = #{p < N : p ∤ N, d ∣ N − p}` equals
`π(N−1; d, N)` up to at most `ω(N)` primes `p ∣ N`. BJS (105), (107); Halberstam-Richert
ch. 11, p. 338. Unit U-1527. -/
theorem card_A_dvd (N d : ℕ) :
    #((range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p) ≤ primesAP (N - 1) d N ∧
    primesAP (N - 1) d N ≤
      #((range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p) + N.primeFactors.card := by
  by_cases hN0 : N = 0
  · subst hN0; unfold primesAP;
    have h1 : ((range 0).filter fun p => p.Prime ∧ ¬p ∣ 0 ∧ d ∣ 0 - p) = ∅ := filter_false_of_mem (by intro x hx; simp at hx)
    have h2 : ((range 1).filter fun p => p.Prime ∧ p % d = 0 % d) = ∅ := by
      apply filter_false_of_mem
      intro x hx
      simp only [mem_range] at hx
      have : x = 0 := by omega
      subst this
      intro h
      have : Nat.Prime 0 := h.1
      exact Nat.not_prime_zero this
    rw [h1, h2]; simp
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
  unfold primesAP
  have hr : range (N - 1 + 1) = range N := by
    ext x
    simp only [mem_range]
    omega
  rw [hr]

  set S := (range N).filter fun p => p.Prime ∧ p % d = N % d
  set S1 := (range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p

  have H1 : S1 ⊆ S := by
    intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨hp.1, hp.2.1, ?_⟩
    have h1 : p ≤ N := le_of_lt (mem_range.1 hp.1)
    have h2 : p ≡ N [MOD d] := (Nat.modEq_iff_dvd' h1).mpr hp.2.2.2
    exact h2

  have H2 : S \ S1 ⊆ N.primeFactors := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    rw [Nat.mem_primeFactors]
    obtain ⟨hp_in_S, hp_not_S1⟩ := hp
    rw [mem_filter] at hp_in_S
    obtain ⟨hp1, hp2, hp3⟩ := hp_in_S
    have h1 : p ≤ N := le_of_lt (mem_range.1 hp1)
    have h2 : p ≡ N [MOD d] := hp3
    have h3 : d ∣ N - p := (Nat.modEq_iff_dvd' h1).mp h2
    have h4 : p ∣ N := by
      by_contra hn
      have : p ∈ S1 := by
        rw [mem_filter]
        exact ⟨hp1, hp2, hn, h3⟩
      exact hp_not_S1 this
    exact ⟨hp2, h4, hN_pos.ne.symm⟩

  constructor
  · exact card_mono H1
  · have H3 : S ⊆ S1 ∪ N.primeFactors := by
      intro p hp
      by_cases h : p ∈ S1
      · rw [mem_union]
        left
        exact h
      · rw [mem_union]
        right
        have : p ∈ S \ S1 := by
          rw [Finset.mem_sdiff]
          exact ⟨hp, h⟩
        exact H2 this
    calc
      #S ≤ #(S1 ∪ N.primeFactors) := card_mono H3
      _ ≤ #S1 + #N.primeFactors := card_union_le _ _

/-- LEAF. The remainder of the sieve on `A` is controlled by `LevelBV`: for every `A > 0`
there are `B, C` with `Σ_{d ≤ √N/(log N)^B, (d,N)=1} |π(N−1; d, N) − π(N−1)/φ(d)| ≤ C N/(log N)^A`.
Take `y q = N − 1`, `a q = N` when `(N, q) = 1`. Iwaniec-Kowalski Theorem 17.1;
Halberstam-Richert ch. 11. Unit U-1527. -/
theorem remainder_of_levelBV (h : LevelBV) :
    ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
        ≤ C * N / log N ^ A := by
  intro A hA
  unfold LevelBV at h
  obtain ⟨B, C, hBC⟩ := h A hA
  use B, C
  intro N hN
  have h1 : ∀ d : ℕ, N - 1 ≤ N := fun d => by omega

  set a : ℕ → ℕ := fun q => if Nat.Coprime q N then N else 1
  have ha : ∀ q, Nat.Coprime (a q) q := by
    intro q
    unfold a
    split_ifs with h_cop
    · exact h_cop.symm
    · exact Nat.coprime_one_left q

  have h3 := hBC N hN (fun d => N - 1) a h1 ha

  have h4 : ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
      ≤ ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊),
        |(primesAP (N - 1) d (a d) : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)| := by
    have H : ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
      = ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d (a d) : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)| := by
      apply sum_congr rfl
      intro i hi
      have h_cop : Nat.Coprime i N := (mem_filter.1 hi).2
      have ha_eq : a i = N := by
        unfold a
        split_ifs
        · rfl
      rw [ha_eq]
    rw [H]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (mem_filter.1 hx).1
    · intro i _ _
      exact abs_nonneg _
  exact le_trans h4 h3

/-- For a finite set and terms between zero and one, the product of one minus each term is at least one minus their sum. Derived elementary product estimate for BJS p. 37 equation 117. Instance set 3 and 5 with both terms equal to one half. -/
theorem chen_product_union_bound (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := h0 a (mem_insert_self _ _)
    have ha1 := h1 a (mem_insert_self _ _)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (mem_insert_of_mem hi)
    have hprod0 : 0 ≤ ∏ i ∈ s, (1 - f i) := prod_nonneg fun i hi => by linarith [hs1 i hi]
    have hprod1 : ∏ i ∈ s, (1 - f i) ≤ 1 :=
      prod_le_one₀ (fun i hi => by linarith [hs1 i hi]) (fun i hi => by linarith [hs0 i hi])
    rw [sum_insert ha, prod_insert ha]
    have hh := ih hs0 hs1
    nlinarith

/-- For every positive natural N, the number of distinct prime factors is at most log N divided by log 2. BJS p. 37 in the proof of equation 118 and Lemma 22. Instance N equal to 30. -/
theorem chen_primeFactors_card_log (N : ℕ) (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ log N / log 2 := by
  exact (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (LeanLab.PNTPort.BV.card_primeFactors_mul_log_two_le hN)


/-- For z greater than two, the product of one minus the reciprocal of p minus one over odd prime divisors of N at least z is between one minus the prime factor count divided by z minus one and one. Derived bound for BJS p. 37 equations 116 to 118. Instance N equal to 30 and z equal to 4. -/
theorem chen_large_prime_correction_bounds (N : ℕ) (z : ℝ) (hz : 2 < z) :
    1 - (N.primeFactors.card : ℝ) / (z - 1) ≤
      ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p),
        (1 - 1 / ((p : ℝ) - 1)) ∧
    (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p),
        (1 - 1 / ((p : ℝ) - 1))) ≤ 1 := by
  let s := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p)
  have h0 : ∀ p ∈ s, 0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hh := (mem_filter.mp hp).2.2
    exact div_nonneg (by norm_num) (by linarith)
  have h1 : ∀ p ∈ s, (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
    intro p hp
    have hh := (mem_filter.mp hp).2.2
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hs : ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) - 1) ≤ (N.primeFactors.card : ℝ) / (z - 1) := by
    calc
      _ ≤ ∑ p ∈ s, (1 : ℝ) / (z - 1) := by
        apply sum_le_sum
        intro p hp
        exact one_div_le_one_div_of_le (by linarith) (by have := (mem_filter.mp hp).2.2; linarith)
      _ = (s.card : ℝ) / (z - 1) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact_mod_cast card_le_card (filter_subset _ _)
  constructor
  · exact (sub_le_sub_left hs 1).trans (chen_product_union_bound s _ h0 h1)
  · exact prod_le_one₀ (fun p hp => by linarith [h1 p hp]) (fun p hp => by linarith [h0 p hp])

/-- For every positive theta, the product of the odd prime divisor correction factors above N to the power theta tends to one as N tends to infinity. BJS p. 37 equation 118 in limit form. Instance theta equal to one eighth. -/
theorem chen_large_prime_correction_tendsto (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ =>
      ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ θ ≤ p),
        (1 - 1 / ((p : ℝ) - 1))) atTop (𝓝 1) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ) / (N : ℝ) ^ θ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hθ).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => 2 / log 2 * (log (N : ℝ) / (N : ℝ) ^ θ))
      atTop (𝓝 0) := by simpa using hlog.const_mul (2 / log 2)
  have hl : Tendsto (fun N : ℕ => 1 - 2 / log 2 * (log (N : ℝ) / (N : ℝ) ^ θ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hpow.eventually_gt_atTop 2, eventually_ge_atTop (1 : ℕ)] with N hNθ hN
    have hb := (chen_large_prime_correction_bounds N _ hNθ).1
    apply le_trans _ hb
    have hcard := chen_primeFactors_card_log N hN
    have hden : 0 < (N : ℝ) ^ θ - 1 := by linarith
    have hpowpos : 0 < (N : ℝ) ^ θ := by linarith
    have hh : (N.primeFactors.card : ℝ) / ((N : ℝ) ^ θ - 1) ≤
        2 / log 2 * (log (N : ℝ) / (N : ℝ) ^ θ) := by
      calc
        _ ≤ (log N / log 2) / ((N : ℝ) ^ θ - 1) := div_le_div_of_nonneg_right hcard hden.le
        _ ≤ 2 / log 2 * (log (N : ℝ) / (N : ℝ) ^ θ) := by
          have hl0 := Real.log_natCast_nonneg N
          have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
          apply (div_le_iff₀ hden).mpr
          field_simp
          nlinarith
    linarith
  · filter_upwards [hpow.eventually_gt_atTop 2] with N hNθ
    exact (chen_large_prime_correction_bounds N _ hNθ).2

/-- The normalized sifted twin product equals the full odd prime product divided by twice exp of minus Euler constant times twinC, multiplied by the large prime divisor correction. This holds for positive N and z at most N. BJS p. 37 equation 116. Instance N equal to 30 and z equal to 6. -/
theorem chen_twin_product_factorization (N : ℕ) (hN : 0 < N) (z : ℝ) (hzN : z ≤ N) :
    (∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < z ∧ ¬ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1))) / U N =
    ((∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < z),
      (1 - 1 / ((p : ℝ) - 1))) /
      (2 * exp (-eulerMascheroniConstant) * twinC)) *
    ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p),
      (1 - 1 / ((p : ℝ) - 1)) := by
  classical
  let f : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1)
  let S := (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < z)
  let D := N.primeFactors.filter (2 < ·)
  have hpos : ∀ p ∈ D, 0 < f p := by
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    dsimp [f]
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hsmall : D.filter (fun p : ℕ => (p : ℝ) < z) = S.filter (fun p => p ∣ N) := by
    ext p
    simp only [D, S, mem_filter, mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨hp, hd, _⟩, hp2⟩, hpz⟩
      have hpN : p < N := by exact_mod_cast (lt_of_lt_of_le hpz hzN)
      exact ⟨⟨hpN, hp, hp2, hpz⟩, hd⟩
    · rintro ⟨⟨hpN, hp, hp2, hpz⟩, hd⟩
      exact ⟨⟨⟨hp, hd, hN.ne'⟩, hp2⟩, hpz⟩
  have hsplitD : (∏ p ∈ D, f p) =
      (∏ p ∈ S.filter (fun p => p ∣ N), f p) *
        ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p), f p := by
    have hh := prod_filter_mul_prod_filter_not D (fun p : ℕ => (p : ℝ) < z) f
    rw [hsmall] at hh
    have htail : D.filter (fun p : ℕ => ¬ (p : ℝ) < z) =
        N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ p) := by
      ext p
      simp only [D, mem_filter, not_lt, and_assoc]
    rw [htail] at hh
    exact hh.symm
  have hsplitS : (∏ p ∈ S.filter (fun p => ¬ p ∣ N), f p) *
      (∏ p ∈ S.filter (fun p => p ∣ N), f p) = ∏ p ∈ S, f p := by
    rw [mul_comm]
    exact prod_filter_mul_prod_filter_not S (fun p => p ∣ N) f
  have hexcluded : S.filter (fun p => ¬ p ∣ N) =
      (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < z ∧ ¬ p ∣ N) := by
    ext p
    simp only [S, mem_filter, and_assoc]
  have hU : U N = (2 * exp (-eulerMascheroniConstant) * twinC) / (∏ p ∈ D, f p) := by
    unfold U
    rw [div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    dsimp [f]
    have hf : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
      ring
    rw [hf, inv_div]
  change (∏ p ∈ _, f p) / U N = ((∏ p ∈ S, f p) / _) * ∏ p ∈ _, f p
  rw [← hexcluded, hU, div_div_eq_mul_div, hsplitD]
  rw [← mul_assoc, hsplitS]
  ring

/-- The finite product of one minus the reciprocal square of p minus one over odd primes below z tends to twinC as z tends to infinity. BJS p. 38 before equation 119. Instance any real cutoff sequence tending to infinity, including z equal to N. -/
theorem chen_twin_truncation_tendsto :
    Tendsto (fun z : ℝ => ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
      (1 - 1 / ((p : ℝ) - 1) ^ 2)) atTop (𝓝 twinC) := by
  let s : Set ℕ := {p | p.Prime ∧ 2 < p}
  let f : ℕ → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2
  have hh : HasProd (s.mulIndicator f) twinC :=
    hasProd_subtype_iff_mulIndicator.mp twinC_multipliable.hasProd
  have ht := hh.tendsto_prod_nat.comp (tendsto_nat_ceil_atTop (α := ℝ))
  simpa only [s, f, Set.mulIndicator, prod_filter, Function.comp_def, Set.mem_ofPred_eq] using ht

/-- For z greater than two, the odd twin sieve product below z equals twice the ordinary Euler prime product below z times the truncated twin constant product. BJS p. 38 before equation 119. Instance z equal to 4 gives both sides equal to one half. -/
theorem chen_odd_product_factorization (z : ℝ) (hz : 2 < z) :
    (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
      (1 - 1 / ((p : ℝ) - 1))) =
    2 * (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) *
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  let P := (range ⌈z⌉₊).filter Nat.Prime
  let O := (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p)
  have htwo : 2 ∈ P := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hz), by decide⟩
  have herase : P.erase 2 = O := by
    ext p
    simp only [P, O, mem_erase, mem_filter, mem_range]
    constructor
    · rintro ⟨hne, hpz, hp⟩
      exact ⟨hpz, hp, by have := hp.two_le; omega⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨by omega, hpz, hp⟩
  have hsplit : (∏ p ∈ O, (1 - 1 / (p : ℝ))) =
      2 * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have hh := prod_erase_mul (s := P) (f := fun p : ℕ => (1 - 1 / (p : ℝ))) htwo
    rw [herase] at hh
    norm_num at hh
    simpa only [one_div] using (show (∏ p ∈ O, (1 - (p : ℝ)⁻¹)) = 2 * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) by linarith)
  change (∏ p ∈ O, _) = 2 * (∏ p ∈ P, _) * ∏ p ∈ O, _
  rw [← hsplit, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.2
  field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
  ring

/-- CONDITIONAL ON the ordinary Mertens product limit: the full odd twin sieve product times log of its cutoff divided by twice exp of minus Euler constant times twinC tends to one. BJS p. 38 equation 119. The finite cutoff 4 identity is checked separately. The cited global limit is not an unconditional instance. -/
theorem chen_odd_product_limit_of_mertens
    (hM : Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log z)
      atTop (𝓝 (exp (-eulerMascheroniConstant)))) :
    Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) * log z /
        (2 * exp (-eulerMascheroniConstant) * twinC)) atTop (𝓝 1) := by
  have hc : 2 * exp (-eulerMascheroniConstant) * twinC ≠ 0 := by
    have := twinC_pos
    positivity
  have ht := ((hM.const_mul 2).mul chen_twin_truncation_tendsto).div_const
    (2 * exp (-eulerMascheroniConstant) * twinC)
  rw [div_self hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with z hz
  rw [chen_odd_product_factorization z hz]
  ring

/-- CONDITIONAL ON the ordinary Mertens product limit: for every theta greater than zero and at most one, the normalized product over odd primes below N to the power theta not dividing N tends to one. This is the sealed mertens_twin conclusion. BJS pp. 37 to 38 equations 116 to 119. Instance theta equal to one eighth meets both elementary hypotheses. The cited global input remains open. -/
theorem mertens_twin_of_euler_product (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1)
    (hM : Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log z)
      atTop (𝓝 (exp (-eulerMascheroniConstant)))) :
    Tendsto (fun N : ℕ =>
      (∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))) * log ((N : ℝ) ^ θ) / U N) atTop (𝓝 1) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop h0).comp tendsto_natCast_atTop_atTop
  have ht := ((chen_odd_product_limit_of_mertens hM).comp hpow).mul
    (chen_large_prime_correction_tendsto θ h0)
  rw [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNp : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hzN : (N : ℝ) ^ θ ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hN1 h1
      _ = N := rpow_one _
  have hs : (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ) =
      (range ⌈(N : ℝ) ^ θ⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p) := by
    ext p
    simp only [mem_filter, mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨hpN, hp, hp2, hpz⟩
      exact ⟨hpz, hp, hp2⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨by exact_mod_cast lt_of_lt_of_le hpz hzN, hp, hp2, hpz⟩
  have hf := chen_twin_product_factorization N hNp _ hzN
  rw [hs] at hf
  dsimp only [Function.comp_apply]
  have hh := congrArg (fun x : ℝ => x * log ((N : ℝ) ^ θ)) hf
  convert hh.symm using 1 <;> ring


/-- CONDITIONAL ON LevelBVTriples: the total absolute error for divisibility counts in B over moduli coprime to N has the stated BV bound. The main term counts members of T coprime to each modulus and divides by its totient. Switching identity BJS p. 35 equation 108 and the distribution hypothesis in the Theorem 51 argument on pp. 56 to 60. At N equal to 98 and d equal to 2 the finite switching set contains 75 and B contains 23. The global distribution input remains a hypothesis. -/
theorem remainder_bset_of_levelBVTriples (h : LevelBVTriples) :
    ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(#((BSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter (d ∣ ·)) : ℝ)
          - (#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
            fun m => Nat.Coprime m d) : ℝ) / (d.totient : ℝ)|
        ≤ C * N / log N ^ A := by
  intro A hA
  obtain ⟨B, C, hBC⟩ := h A hA
  refine ⟨B, C, fun N hN => ?_⟩
  let a : ℕ → ℕ := fun q => if Nat.Coprime q N then N else 1
  have ha : ∀ q, Nat.Coprime (a q) q := by
    intro q
    dsimp [a]
    split_ifs with hq
    · exact hq.symm
    · exact Nat.coprime_one_left q
  have hh := hBC N hN a ha
  apply le_trans _ hh
  calc
    _ = ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
            fun m => m % d = a d % d) : ℝ)
          - (#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
            fun m => Nat.Coprime m d) : ℝ) / (d.totient : ℝ)| := by
      apply sum_congr rfl
      intro d hd
      rw [card_bset_dvd]
      have had : a d = N := ite_eq_left (mem_filter.mp hd).2
      rw [had]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)

/-- Every prime divisor of a member of T is at least z when z is at most y. BJS p. 35 equation 108 and p. 56 before equation 179. Instance N equal to 98, z equal to 3, y equal to 5 and m equal to 75 with prime divisor 5. -/
theorem TSet_rough {N m : ℕ} {z y : ℝ} (hzy : z ≤ y) (hm : m ∈ TSet N z y)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) : z ≤ (p : ℝ) := by
  classical
  obtain ⟨hmN, hcop, p1, p2, p3, hp1, hp2, hp3, hz1, hy1, hy2, h23, rfl⟩ := mem_filter.mp hm
  rcases hp.dvd_mul.mp hpm with h12 | h3
  · rcases hp.dvd_mul.mp h12 with h1 | h2
    · have he : p = p1 := (Nat.prime_dvd_prime_iff_eq hp hp1).mp h1
      simpa [he] using hz1
    · have he : p = p2 := (Nat.prime_dvd_prime_iff_eq hp hp2).mp h2
      simpa [he] using hzy.trans hy2
  · have he : p = p3 := (Nat.prime_dvd_prime_iff_eq hp hp3).mp h3
    have h23R : (p2 : ℝ) ≤ p3 := by exact_mod_cast h23
    simpa [he] using (hzy.trans hy2).trans h23R

/-- If d is positive and every prime factor of d is below z, every member of T is coprime to d, so filtering T by coprimality to d changes nothing. Assume z at most y. BJS p. 35 equation 108. Instance N equal to 98, z equal to 3, y equal to 5 and d equal to 2. -/
theorem TSet_coprime_of_small_primeFactors {N d : ℕ} {z y : ℝ} (hzy : z ≤ y)
    (hd : d ≠ 0) (hsmall : ∀ p ∈ d.primeFactors, (p : ℝ) < z) :
    (TSet N z y).filter (fun m => Nat.Coprime m d) = TSet N z y := by
  classical
  apply filter_eq_self.mpr
  intro m hm
  apply Nat.coprime_of_dvd' (fun p hp hpm hpd => ?_)
  have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩
  exact False.elim ((not_lt_of_ge (TSet_rough hzy hm hp hpm)) (hsmall p hmem))

/-- For every positive theta and every real B, the logarithmic sieve parameter with level square root N divided by log N to the power B and cutoff N to the power theta tends to one divided by twice theta. Derived substitution into BJS p. 5 equation 6. Instance theta equal to one eighth and B equal to zero gives limit four. -/
theorem chen_sieve_parameter_tendsto (θ B : ℝ) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => log (√(N : ℝ) / log N ^ B) / log ((N : ℝ) ^ θ))
      atTop (𝓝 (1 / (2 * θ))) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => log (log (N : ℝ)) / log N) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hh := ((tendsto_const_nhds.sub (hsmall.const_mul B)).div_const θ :
    Tendsto (fun N : ℕ => ((1 / 2 : ℝ) - B * (log (log (N : ℝ)) / log N)) / θ)
      atTop (𝓝 (((1 / 2 : ℝ) - B * 0) / θ)))
  have hvalue : (((1 / 2 : ℝ) - B * 0) / θ) = 1 / (2 * θ) := by
    rw [mul_zero, sub_zero, div_mul_eq_div_div]
  rw [hvalue] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [log_div (sqrt_pos_of_pos hNp).ne' (rpow_pos_of_pos hLp B).ne',
    log_sqrt hNp.le, log_rpow hLp, log_rpow hNp]
  field_simp

/-- For every positive modulus p, the number of members of T divisible by p is at most the floor of N divided by p. Derived elementary count for BJS p. 35 equation 108 and the p. 56 switching setup. Instance N equal to 98, p equal to 3, z equal to 3 and y equal to 5 contains the triple 75. -/
theorem card_TSet_multiples_le (N p : ℕ) (hp : 0 < p) (z y : ℝ) :
    #((TSet N z y).filter (p ∣ ·)) ≤ N / p := by
  classical
  have hmpos : ∀ m ∈ TSet N z y, 0 < m := by
    intro m hm
    obtain ⟨_, _, p1, p2, p3, hp1, hp2, hp3, _, _, _, _, rfl⟩ := mem_filter.mp hm
    exact Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos
  have hh : #((TSet N z y).filter (p ∣ ·)) ≤ #(Icc 1 (N / p)) := by
    apply card_le_card_of_injOn (fun m => m / p)
    · intro m hm
      obtain ⟨hmT, hpm⟩ := mem_filter.mp hm
      have hmN : m ≤ N := (mem_range.mp (mem_filter.mp hmT).1).le
      have hple : p ≤ m := Nat.le_of_dvd (hmpos m hmT) hpm
      exact mem_Icc.mpr ⟨Nat.div_pos hple hp, Nat.div_le_div_right hmN⟩
    · intro a ha b hb hab
      dsimp only at hab
      have hpa := (mem_filter.mp ha).2
      have hpb := (mem_filter.mp hb).2
      calc
        a = a / p * p := (Nat.div_mul_cancel hpa).symm
        _ = b / p * p := by rw [hab]
        _ = b := Nat.div_mul_cancel hpb
  simpa using hh

/-- For positive d and z at most y, the number of members of T not coprime to d is at most the sum of floor N divided by p over prime factors p of d at least z. Derived finite correction for BJS p. 56 switching setup. Instance N equal to 98, d equal to 15, z equal to 3 and y equal to 5 contains the excluded triple 75. -/
theorem card_TSet_not_coprime_le (N d : ℕ) (hd : d ≠ 0) (z y : ℝ) (hzy : z ≤ y) :
    #((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) ≤
      ∑ p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), N / p := by
  classical
  let P := d.primeFactors.filter (fun p : ℕ => z ≤ p)
  have hcover : (TSet N z y).filter (fun m => ¬ Nat.Coprime m d) ⊆
      P.biUnion (fun p => (TSet N z y).filter (p ∣ ·)) := by
    intro m hm
    obtain ⟨hmT, hbad⟩ := mem_filter.mp hm
    obtain ⟨p, hp, hpm, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
    refine mem_biUnion.mpr ⟨p, ?_, mem_filter.mpr ⟨hmT, hpm⟩⟩
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩, TSet_rough hzy hmT hp hpm⟩
  apply (card_le_card hcover).trans (card_biUnion_le.trans ?_)
  apply sum_le_sum
  intro p hp
  exact card_TSet_multiples_le N p (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos z y

/-- For every real B, the lower sieve function at level square root N divided by log N to the power B and cutoff N to the power one eighth tends to exp of Euler constant times log 3 divided by two. Derived from BJS p. 5 equation 6 and the f of four value used in Theorem 44. Instance B equal to zero. -/
theorem chen_lower_sieve_coefficient_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => LeanLab.AlmostPrimeSums.Decomp1527a.fsieve (log (√(N : ℝ) / log N ^ B) /
      log ((N : ℝ) ^ ((1 : ℝ) / 8)))) atTop
      (𝓝 (exp eulerMascheroniConstant * log 3 / 2)) := by
  have hp := chen_sieve_parameter_tendsto ((1 : ℝ) / 8) B (by norm_num)
  norm_num at hp
  have hc : ContinuousAt LeanLab.AlmostPrimeSums.Decomp1527a.fsieve (4 : ℝ) :=
    LeanLab.AlmostPrimeSums.Decomp1527a.fsieve_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
  have hh := hc.tendsto.comp hp
  rwa [LeanLab.AlmostPrimeSums.Decomp1527a.fsieve_four] at hh

/-- For every real B, the upper sieve function at level square root N divided by log N to the power B and cutoff N to the power one third tends to four times exp of Euler constant divided by three. Derived from BJS p. 5 equation 6 and the F of three halves value used in Theorem 51. Instance B equal to zero. -/
theorem chen_switched_sieve_coefficient_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (log (√(N : ℝ) / log N ^ B) /
      log ((N : ℝ) ^ ((1 : ℝ) / 3)))) atTop
      (𝓝 (4 * exp eulerMascheroniConstant / 3)) := by
  have hp := chen_sieve_parameter_tendsto ((1 : ℝ) / 3) B (by norm_num)
  norm_num at hp
  have hc : ContinuousAt LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (3 / 2 : ℝ) :=
    LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve_continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
  have hh := hc.tendsto.comp hp
  have hv : LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (3 / 2 : ℝ) = 4 * exp eulerMascheroniConstant / 3 := by
    rw [LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve, ite_eq_left (by norm_num)]
    ring
  rwa [hv] at hh

/-- For positive d and positive z at most y, the real cardinality of triples not coprime to d is at most log d divided by log 2 times N divided by z. Derived from BJS p. 35 equation 108 and the p. 56 switching setup. Instance N equal to 98, d equal to 15, z equal to 3 and y equal to 5. -/
theorem card_TSet_not_coprime_real_le (N d : ℕ) (hd : 1 ≤ d) (z y : ℝ)
    (hz : 0 < z) (hzy : z ≤ y) :
    (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) ≤
      (log d / log 2) * ((N : ℝ) / z) := by
  classical
  have hh := card_TSet_not_coprime_le N d (by omega) z y hzy
  have hsum : ((∑ p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), N / p : ℕ) : ℝ) ≤
      (∑ p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), (N : ℝ) / p : ℝ) := by
    push_cast
    apply sum_le_sum
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
    apply (le_div_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  calc
    _ ≤ ((∑ p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), N / p : ℕ) : ℝ) := by exact_mod_cast hh
    _ ≤ ∑ p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), (N : ℝ) / p := hsum
    _ ≤ ∑ _p ∈ d.primeFactors.filter (fun p : ℕ => z ≤ p), (N : ℝ) / z := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left (by positivity) hz (mem_filter.mp hp).2
    _ = (#(d.primeFactors.filter (fun p : ℕ => z ≤ p)) : ℝ) * ((N : ℝ) / z) := by simp
    _ ≤ (d.primeFactors.card : ℝ) * ((N : ℝ) / z) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_le_card (filter_subset _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (chen_primeFactors_card_log d hd) (by positivity)

/-- There is an absolute positive C such that the sum over moduli d from one to D of the number of triples not coprime to d divided by phi of d is at most C times N divided by z times one plus log D squared, whenever zero is less than z and z is at most y. Derived finite correction for BJS p. 56 switching setup. Instance N equal to 98, D equal to 10, z equal to 3 and y equal to 5. -/
theorem sum_TSet_coprime_loss_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N D : ℕ, ∀ z y : ℝ, 0 < z → z ≤ y →
      ∑ d ∈ Icc 1 D,
        (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) / (d.totient : ℝ) ≤
      C * ((N : ℝ) / z) * (1 + log D) ^ 2 := by
  obtain ⟨C, hC, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨C / log 2, div_pos hC hlog2, fun N D z y hz hzy => ?_⟩
  by_cases hD : D = 0
  · subst D
    simp only [Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), sum_empty, Nat.cast_zero, log_zero, add_zero, one_pow, mul_one]
    positivity
  have hD1 : 1 ≤ D := by omega
  have hLD : 0 ≤ log (D : ℝ) := log_nonneg (by exact_mod_cast hD1)
  let K : ℝ := (1 + log D) / log 2 * ((N : ℝ) / z)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterm : ∀ d ∈ Icc 1 D,
      (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) ≤ K := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hdD := (mem_Icc.mp hd).2
    have hh := card_TSet_not_coprime_real_le N d hd1 z y hz hzy
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ hlog2.le
    have hlog := log_le_log (by exact_mod_cast (show 0 < d by omega))
      (by exact_mod_cast hdD : (d : ℝ) ≤ D)
    linarith
  calc
    _ ≤ ∑ d ∈ Icc 1 D, K / (d.totient : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right (hterm d hd) (by positivity)
    _ = K * ∑ d ∈ Icc 1 D, 1 / (d.totient : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      ring
    _ ≤ K * (C * (1 + log D)) := mul_le_mul_of_nonneg_left (hsum D) hK
    _ = _ := by dsimp [K]; ring

/-- The sum of absolute B remainder errors against full T mass is at most the sum against the coprime T mass plus the total coprimality loss divided by phi. This holds for every finite set of moduli. Derived triangle inequality for BJS p. 56 switching setup and the LevelBVTriples normalization. Instance N equal to 98, z equal to 3, y equal to 5 and modulus set consisting of 2. -/
theorem bset_full_mass_remainder_le (N : ℕ) (z y : ℝ) (s : Finset ℕ) :
    ∑ d ∈ s,
      |(#((BSet N z y).filter (d ∣ ·)) : ℝ) - (#(TSet N z y) : ℝ) / (d.totient : ℝ)| ≤
    (∑ d ∈ s,
      |(#((BSet N z y).filter (d ∣ ·)) : ℝ) -
        (#((TSet N z y).filter (fun m => Nat.Coprime m d)) : ℝ) / (d.totient : ℝ)|) +
    ∑ d ∈ s,
      (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) / (d.totient : ℝ) := by
  classical
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hc := card_filter_add_card_filter_not (s := TSet N z y) (fun m => Nat.Coprime m d)
  have hcr : (#(TSet N z y) : ℝ) =
      (#((TSet N z y).filter (fun m => Nat.Coprime m d)) : ℝ) +
      (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) := by
    exact_mod_cast hc.symm
  rw [hcr, add_div, sub_add_eq_sub_sub]
  have hh := abs_sub ((#((BSet N z y).filter (d ∣ ·)) : ℝ) -
    (#((TSet N z y).filter (fun m => Nat.Coprime m d)) : ℝ) / (d.totient : ℝ))
    ((#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) / (d.totient : ℝ))
  rwa [abs_of_nonneg (by positivity :
    0 ≤ (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) / (d.totient : ℝ))] at hh

/-- CONDITIONAL ON LevelBVTriples: there is a positive absolute K such that every positive distribution exponent A admits B and C with the full T mass B remainder bounded by C times N divided by log N to the power A plus K times N divided by z times one plus log D squared. Here z is N to the power one eighth, y is N to the power one third and D is the natural floor of the BV level. Derived from BJS p. 56 switching setup and the cited triple distribution input. Finite instance N equal to 98 has the triple 75. The global distribution input remains a hypothesis. -/
theorem remainder_bset_full_mass_of_levelBVTriples (h : LevelBVTriples) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N →
      let z := (N : ℝ) ^ ((1 : ℝ) / 8)
      let y := (N : ℝ) ^ ((1 : ℝ) / 3)
      let D := ⌊√(N : ℝ) / log N ^ B⌋₊
      ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N),
        |(#((BSet N z y).filter (d ∣ ·)) : ℝ) - (#(TSet N z y) : ℝ) / (d.totient : ℝ)| ≤
      C * N / log N ^ A + K * ((N : ℝ) / z) * (1 + log D) ^ 2 := by
  classical
  obtain ⟨K, hK, hLoss⟩ := sum_TSet_coprime_loss_le
  refine ⟨K, hK, fun A hA => ?_⟩
  obtain ⟨B, C, hBC⟩ := remainder_bset_of_levelBVTriples h A hA
  refine ⟨B, C, fun N hN => ?_⟩
  let z := (N : ℝ) ^ ((1 : ℝ) / 8)
  let y := (N : ℝ) ^ ((1 : ℝ) / 3)
  let D := ⌊√(N : ℝ) / log N ^ B⌋₊
  let s := (Icc 1 D).filter (fun d => Nat.Coprime d N)
  have hz : 0 < z := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hzy : z ≤ y := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hsmall : (∑ d ∈ s,
      (#((TSet N z y).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) / (d.totient : ℝ)) ≤
      K * ((N : ℝ) / z) * (1 + log D) ^ 2 := by
    apply le_trans _ (hLoss N D z y hz hzy)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  exact (bset_full_mass_remainder_le N z y s).trans (add_le_add (hBC N hN) hsmall)

/-- There exists a positive real c such that the ordinary Euler prime product through floor x times log x tends to c. This proves the existence part used in BJS p. 38 equation 119 from the proved Mertens block bounds. It does not identify c as exp of minus Euler constant. The theorem has no hypotheses. The cutoff x equal to 4 gives product one third and a positive logarithmic factor. -/
theorem exists_positive_euler_product_limit :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun x : ℝ => LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x⌋₊ * log x) atTop (𝓝 c) := by
  let F : ℝ → ℝ := fun x => log (LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x⌋₊) + log (log x)
  let g : ℝ → ℝ := fun x => 4 / log x + (1 / 2 : ℝ) / (⌊x⌋₊ : ℝ)
  have hg1 : Tendsto (fun x : ℝ => 4 / log x) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 4
  have hf : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have hg2 := hf.const_div_atTop (1 / 2 : ℝ)
  have hg : Tendsto g atTop (𝓝 0) := by simpa [g] using hg1.add hg2
  have hmod : ∀ x y : ℝ, 2 ≤ y → y ≤ x → |F x - F y| ≤ g y := by
    intro x y hy hyx
    have hmy : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
    have hsplit := LeanLab.ChenPrimeExceptional.Task101.eulerProduct_split (Nat.floor_mono hyx)
    have hpos1 := LeanLab.ChenPrimeExceptional.Task101.eulerProduct_pos ⌊y⌋₊
    have hpos2 := LeanLab.ChenPrimeExceptional.Task101.eulerBlock_pos (w := ⌊x⌋₊) hmy
    calc
      _ = |log (LeanLab.ChenPrimeExceptional.Task101.eulerBlock ⌊y⌋₊ ⌊x⌋₊) + (log (log x) - log (log y))| := by
        dsimp only [F]
        rw [hsplit, log_mul hpos1.ne' hpos2.ne']
        congr 1
        ring
      _ ≤ _ := by
        have hh := LeanLab.AlmostPrimes.Decomp1528b.mertens3_block hy hyx
        simpa only [LeanLab.ChenPrimeExceptional.Task101.eulerBlock, g, div_mul_eq_div_div] using hh
  obtain ⟨B, hB⟩ := LeanLab.AlmostPrimes.Decomp1528b.exists_limit_of_modulus F g 2 hg hmod
  have hl : Tendsto F atTop (𝓝 B) := by
    have hlow : Tendsto (fun x => B - g x) atTop (𝓝 B) := by
      simpa using tendsto_const_nhds.sub hg
    have hupp : Tendsto (fun x => B + g x) atTop (𝓝 B) := by
      simpa using tendsto_const_nhds.add hg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hh := (abs_le.mp (hB x hx)).1
      linarith
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hh := (abs_le.mp (hB x hx)).2
      linarith
  refine ⟨exp B, exp_pos _, ?_⟩
  have ht := continuous_exp.continuousAt.tendsto.comp hl
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  dsimp only [F, Function.comp_apply]
  rw [exp_add, exp_log (LeanLab.ChenPrimeExceptional.Task101.eulerProduct_pos _), exp_log (log_pos (by linarith))]

/-- For every real cutoff x, the ordinary Euler prime product through floor x is at most the product over primes strictly below x. That strict product is at most the Euler product through floor of x minus one. Derived cutoff comparison for the Mertens input in BJS p. 38. Instance x equal to 4 gives the same product one third in all three places. -/
theorem strict_euler_product_bounds (x : ℝ) :
    LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x⌋₊ ≤ (∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) ∧
    (∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) ≤ LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x - 1⌋₊ := by
  classical
  let S := (range ⌈x⌉₊).filter Nat.Prime
  let P := (Icc 1 ⌊x⌋₊).filter Nat.Prime
  let Q := (Icc 1 ⌊x - 1⌋₊).filter Nat.Prime
  have hSP : S ⊆ P := by
    intro p hp
    obtain ⟨hpR, hpP⟩ := mem_filter.mp hp
    have hpx : (p : ℝ) < x := Nat.lt_ceil.mp (mem_range.mp hpR)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpP.pos, Nat.le_floor hpx.le⟩, hpP⟩
  have hQS : Q ⊆ S := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    have hpx : (p : ℝ) < x := by
      have hh := (Nat.le_floor_iff' hpP.ne_zero).mp (mem_Icc.mp hpI).2
      linarith
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpx), hpP⟩
  have hpos : ∀ p : ℕ, p.Prime → 0 ≤ 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hh : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hle : ∀ p : ℕ, (1 - 1 / (p : ℝ)) ≤ 1 := fun p => sub_le_self _ (by positivity)
  constructor
  · exact prod_le_prod_of_subset_of_le_one₀ hSP
      (fun p hp => hpos p (mem_filter.mp hp).2) (fun p _ _ => hle p)
  · exact prod_le_prod_of_subset_of_le_one₀ hQS
      (fun p hp => hpos p (mem_filter.mp hp).2) (fun p _ _ => hle p)

/-- There exists a positive c such that the ordinary Euler prime product over primes strictly below x times log x tends to c. This proves the strict cutoff existence part of the Mertens input in BJS p. 38 equation 119. The value of c is not identified here. The theorem has no hypotheses and supplies its own positive witness. -/
theorem exists_positive_strict_euler_product_limit :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x : ℝ =>
      (∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log x) atTop (𝓝 c) := by
  obtain ⟨c, hc, hlim⟩ := exists_positive_euler_product_limit
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have hratio : Tendsto (fun x : ℝ => x / (x - 1)) atTop (𝓝 1) := by
    have hh : Tendsto (fun x : ℝ => 1 + 1 / (x - 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (hshift.const_div_atTop (1 : ℝ))
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn : x - 1 ≠ 0 := by linarith
    field_simp
    ring
  have heq : Asymptotics.IsEquivalent atTop (fun x : ℝ => x) (fun x => x - 1) :=
    Asymptotics.isEquivalent_of_tendsto_one hratio
  have hlogeq := heq.log hshift
  have hlogne := (tendsto_log_atTop.comp hshift).eventually_ne_atTop 0
  have hlogratio : Tendsto (fun x : ℝ => log x / log (x - 1)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hlogne).mp hlogeq
  have hupper0 := (hlim.comp hshift).mul hlogratio
  rw [mul_one] at hupper0
  have hupper : Tendsto (fun x : ℝ => LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x - 1⌋₊ * log x) atTop (𝓝 c) := by
    apply hupper0.congr'
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hn : log (x - 1) ≠ 0 := (log_pos (by linarith)).ne'
    dsimp only [Function.comp_apply]
    field_simp
  refine ⟨c, hc, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim hupper
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_right (strict_euler_product_bounds x).1 (log_nonneg (by linarith))
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_right (strict_euler_product_bounds x).2 (log_nonneg (by linarith))

/-- LEAF. Identify the positive constant in Mertens third theorem.
If the strict ordinary Euler product times log of the cutoff has limit c,
then c equals exp of minus Euler constant. The existence of such a positive c
is proved above, so this hypothesis has a proved instance.
Rosser and Schoenfeld 1962 Theorem 7, as applied in BJS arXiv 2207.09452
p. 38 equation 119. DOI https://doi.org/10.1215/ijm/1255631807. -/
theorem mertens_constant_identification (c : ℝ)
    (hlim : Tendsto (fun x : ℝ =>
      (∏ p ∈ (range ⌈x⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log x) atTop (𝓝 c)) :
    c = exp (-eulerMascheroniConstant) := by
  sorry

/-- LEAF. Ordinary Mertens third theorem in limit form, with strict prime cutoff.
Rosser and Schoenfeld 1962 Theorem 7, cited and applied in BJS arXiv 2207.09452
p. 38 in the proof of Lemma 38, equation 119. DOI https://doi.org/10.1215/ijm/1255631807.
The exact constant exp of minus Euler constant remains the analytic input.
The twin constant truncation and the uniform prime divisor correction are proved above. -/
theorem mertens_euler_product :
    Tendsto (fun z : ℝ =>
      (∏ p ∈ (range ⌈z⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * log z)
      atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  obtain ⟨c, hc, hlim⟩ := exists_positive_strict_euler_product_limit
  rw [mertens_constant_identification c hlim] at hlim
  exact hlim


/-- The integral from one eighth to one third of one divided by beta times four minus eight beta equals log 6 divided by four. This is the zero alpha limit of BJS p. 54 equation 173 and the kernel in sumSAq_upper. The closed interval has positive length and stays below one half, so both denominator factors are positive. There are no hypotheses. -/
theorem chen_upper_prime_integral :
    (∫ t in (1 / 8 : ℝ)..(1 / 3), 1 / (t * (4 - 8 * t))) = log 6 / 4 := by
  have hF : ∀ t ∈ Set.uIcc (1 / 8 : ℝ) (1 / 3),
      HasDerivAt (fun t : ℝ => (log t - log (1 - 2 * t)) / 4)
        (1 / (t * (4 - 8 * t))) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h10 : 1 - 2 * t ≠ 0 := by linarith [ht.2]
    have hh := ((hasDerivAt_log ht0).sub
      (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul 2)).log h10)).div_const 4
    simp only [Pi.sub_apply, id_eq, mul_one, zero_sub] at hh
    have hcoef : 1 / (t * (4 - 8 * t)) = (t⁻¹ - -2 / (1 - 2 * t)) / 4 := by
      rw [show (4 : ℝ) - 8 * t = 4 * (1 - 2 * t) by ring]
      field_simp
      ring_nf
      field_simp [show (1 : ℝ) - t * 2 ≠ 0 by simpa only [mul_comm] using h10]
      ring
    rw [← hcoef] at hh
    exact hh
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * (4 - 8 * t)))
      (Set.uIcc (1 / 8) (1 / 3)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
    intro t ht
    change t * (4 - 8 * t) ≠ 0
    apply mul_ne_zero
    · linarith [ht.1]
    · linarith [ht.2]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  have hlog : log (3 / 4 : ℝ) - log (1 / 8 : ℝ) = log 6 := by
    rw [← log_div (by norm_num) (by norm_num)]
    norm_num
  norm_num only [show (1 : ℝ) - 2 * (1 / 3) = 1 / 3 by norm_num,
    show (1 : ℝ) - 2 * (1 / 8) = 3 / 4 by norm_num]
  linarith

/-- If the ordinary Euler product through floor x times log x tends to c, then one divided by 1500 is at most c and c is at most one. This is a proved weak interval for the Mertens constant, using the lab elementary product bounds in place of the exact value needed in BJS p. 38 equation 119. exists_positive_euler_product_limit supplies a limit satisfying the hypothesis. The concrete value c equal to one satisfies the interval but differs from exp of minus Euler constant, so this route does not identify the required constant. -/
theorem euler_product_limit_bounds (c : ℝ)
    (hlim : Tendsto (fun x : ℝ => LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x⌋₊ * log x) atTop (𝓝 c)) :
    (1 / 1500 : ℝ) ≤ c ∧ c ≤ 1 := by
  have hevent : ∀ᶠ x : ℝ in atTop,
      LeanLab.ChenPrimeExceptional.Task101.eulerProduct ⌊x⌋₊ * log x ∈ Set.Icc (1 / 1500 : ℝ) 1 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hs : (Icc 1 ⌊x⌋₊).filter Nat.Prime = Nat.primesLE ⌊x⌋₊ := by
      ext p
      simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        exact ⟨h2, hp⟩
      · rintro ⟨h2, hp⟩
        exact ⟨⟨hp.pos, h2⟩, hp⟩
    have hLp : 0 < log x := log_pos (by linarith)
    have hl := LeanLab.AlmostPrimes.Decomp1528b.mertens_prod_lower hx
    have hu := LeanLab.AlmostPrimes.Decomp1528b.mertens_prod_upper hx
    rw [le_div_iff₀ hLp] at hu
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1500 * log x)] at hl
    unfold LeanLab.ChenPrimeExceptional.Task101.eulerProduct
    rw [hs]
    exact ⟨by nlinarith, hu⟩
  exact isClosed_Icc.mem_of_tendsto hlim hevent

/-- LEAF. Mertens' product for the twin density: for `0 < θ ≤ 1`, as `N → ∞`,
`∏_{2<p<N^θ, p∤N} (1 − 1/(p−1)) · log N^θ / U_N → 1`; from Mertens' third theorem
`∏_{p<z}(1−1/p) ~ e^{-γ}/log z`, `(p−2)/(p−1) = (1−1/p)(1−1/(p−1)²)`, and at most `1/θ` primes
`p ∣ N` with `p ≥ N^θ`. Halberstam-Richert ch. 2 and ch. 11 p. 339; Iwaniec-Kowalski Section 2.2.
Unit U-1527. -/
theorem mertens_twin (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) :
    Tendsto (fun N : ℕ =>
      (∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))) * log ((N : ℝ) ^ θ) / U N) atTop (𝓝 1) := by
  exact mertens_twin_of_euler_product θ h0 h1 mertens_euler_product

/-! ### The three sieve estimates, from the linear sieve and the level of distribution -/

/-- LEAF. Lower bound for `S(A, P(z))`, `z = N^{1/8}`: CONDITIONAL ON `LevelBV`, for every
`η > 0` and large even `N`, `S(A,P(z)) ≥ (2 log 3 − η) M(N)`. Apply `Decomp1527b.jr_lower` with
`X = π(N)`, `g(d) = 1/φ(d)` on `d ∣ P(z)`, `D = N^{1/2}/(log N)^B`, `s → 4`,
`f(4) = e^γ log 3/2` (`Decomp1527a.fsieve_four`, continuity), `mertens_twin 1/8`,
`card_A_dvd`, `remainder_of_levelBV`. BJS Theorem 44; Halberstam-Richert Theorem 11.1 proof.
Unit U-1527. -/
theorem SA_lower (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (2 * log 3 - η) * Mchen N ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  sorry

/-- LEAF. Upper bound for `½ Σ_{z≤q<y, q∤N} S(A_q, P(z))`: CONDITIONAL ON `LevelBV`, for every
`η > 0` and large even `N`, `≤ (log 6 + η) M(N)`. Apply `Decomp1527b.jr_upper` to each `A_q`
at level `D/q`, `s_q = 4 − 8 log q/log N ∈ (4/3, 3]`, `F(s_q) = 2e^γ/s_q`, and
`Σ_q 1/(q s_q) → ∫_{1/8}^{1/3} dα/(α(4−8α)) = (log 6)/4`. BJS Theorem 50.
Unit U-1527. -/
theorem sumSAq_upper (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (log 6 + η) * Mchen N := by
  sorry

/-- LEAF. Upper bound for `½ S(B, P(y))`, `y = N^{1/3}`: CONDITIONAL ON `LevelBVTriples`, for
every `η > 0` and large even `N`, `≤ (c̄ + η) M(N)`. Apply `Decomp1527b.jr_upper` to `B` with
`X = |T| ~ c̄ N/log N`, `g(d) = 1/φ(d)`, `s → 3/2`, `F(3/2) = 4e^γ/3`, `mertens_twin 1/3`,
`card_bset_dvd`, `siftedBy_iff_of_mem_bset`. BJS Theorem 51 and Lemma 52; Chen's switching.
Unit U-1527. -/
theorem SB_upper (h : LevelBVTriples) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * Mchen N := by
  sorry

/-- LEAF. The trivial terms of Chen's inequality are small: for every `η > 0`, eventually
`2N^{7/8} + N^{1/3} ≤ η M(N)`, since `U_N ≥ 2e^{-γ} C₂ > 0` and `M(N) ≫ N/log² N`.
BJS Lemma 37 and Section 9. Unit U-1527. -/
theorem error_small :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3) ≤ η * Mchen N := by
  intro η hη
  let c : ℝ := 2 * exp eulerMascheroniConstant / 1000
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog : (fun x : ℝ => log x ^ 2) =o[atTop] (fun x => x ^ ((1 : ℝ) / 8)) := by
    simpa only [rpow_two] using isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 8)
  have he := hlog.bound (show 0 < η * c / 3 by positivity)
  have hen := tendsto_natCast_atTop_atTop.eventually he
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hen
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < log (N : ℝ) ^ 2 := sq_pos_of_pos (log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hb := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg hNp.le _)] at hb
  have hp : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
    rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hmul : (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8) = N := by
    rw [← rpow_add hNp]; norm_num
  have herr : (2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3)) * log N ^ 2 ≤ η * c * N := by
    calc
      _ ≤ (3 * (N : ℝ) ^ ((7 : ℝ) / 8)) * log N ^ 2 := by gcongr; linarith
      _ ≤ (3 * (N : ℝ) ^ ((7 : ℝ) / 8)) * (η * c / 3 * (N : ℝ) ^ ((1 : ℝ) / 8)) := by gcongr
      _ = η * c * ((N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8)) := by ring
      _ = η * c * N := by rw [hmul]
  have hM : c * N / log N ^ 2 ≤ Mchen N := by
    unfold Mchen
    apply div_le_div_of_nonneg_right _ hL.le
    have hu := U_ge N
    dsimp [c]
    calc
      _ = (2 * exp eulerMascheroniConstant * (1 / 1000)) * N := by ring
      _ ≤ _ := by gcongr
  have hm := mul_le_mul_of_nonneg_left hM hη.le
  rw [← mul_div_assoc, ← mul_assoc] at hm
  exact ((le_div_iff₀ hL).mpr herr).trans hm

/-- LEAF. `c̄ = ∫_{1/8}^{1/3} log(2−3β)/(β(1−β)) dβ < 0.3631` (value `0.36308373`). The lab file
`ChenExplicit/BJSCbar.lean` has `BJS.cbar_lt : cbar < 0.363084` for the same integral, so this
is a port. BJS Lemma 52. Unit U-1527. -/
theorem cbar_lt' : (∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) < 0.3631 := by
  have hc := BJS.cbar_lt
  unfold BJS.cbar at hc
  linarith

/-- `log 3 − log 2 > 0.405`. -/
theorem log_three_halves_gt : 0.405 < log 3 - log 2 := by
  have := Real.log_three_gt_d9
  have := Real.log_two_lt_d9
  norm_num at *; linarith

/-! ### Assembly: Chen's lower bound, CONDITIONAL ON the level of distribution -/

/-- **Chen's lower bound, CONDITIONAL ON `LevelBV` and `LevelBVTriples`**: for every large even
`N`, `π₂(N) > M(N)/100 = 0.04 C_N N / log² N`, where `π₂(N) = chenCount N` counts primes
`p < N` with `N − p` a product of at most two primes. Assembled from the leaves `SA_lower`,
`sumSAq_upper`, `SB_upper`, `error_small`, `cbar_lt'` and the PROVED Chen inequality
`ChenExplicit.lemma37`; margin `log(3/2) − c̄ − 4η > 0.405 − 0.3631 − 0.02 > 0.01`. -/
theorem chen_lower_conditional (h1 : LevelBV) (h2 : LevelBVTriples) :
    ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → (1 / 100 : ℝ) * Mchen N < chenCount N := by
  obtain ⟨N1, hA⟩ := SA_lower h1 0.005 (by norm_num)
  obtain ⟨N2, hQ⟩ := sumSAq_upper h1 0.005 (by norm_num)
  obtain ⟨N3, hB⟩ := SB_upper h2 0.005 (by norm_num)
  obtain ⟨N4, hE⟩ := error_small 0.005 (by norm_num)
  refine ⟨max (max N1 N2) (max (max N3 N4) 256), fun N he hN => ?_⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN4 : N4 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN5 : 256 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have l37 := lemma37 N hN5
  have a := hA N he hN1
  have q := hQ N he hN2
  have b := hB N he hN3
  have e := hE N hN4
  have hc := cbar_lt'
  have hl := log_three_halves_gt
  have hM := Mchen_pos N (by omega)
  have h6 : log (6 : ℝ) = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h6] at q
  set M := Mchen N
  set cb := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))
  have hm : 0 ≤ (log 3 - log 2 - cb - 0.03) * M := mul_nonneg (by linarith) hM.le
  nlinarith

/-- **Chen's theorem, CONDITIONAL ON `LevelBV` and `LevelBVTriples`**: every large even `N` is
`p + m` with `p` prime and `m` a product of at most two primes. From `chen_lower_conditional`. -/
theorem chen_conditional (h1 : LevelBV) (h2 : LevelBVTriples) : ∃ T : ℝ, ChenAbove T := by
  obtain ⟨N₀, hN⟩ := chen_lower_conditional h1 h2
  refine ⟨max N₀ 2, fun N he hT => ?_⟩
  have hle : max N₀ 2 ≤ N := by exact_mod_cast hT.le
  have hM := Mchen_pos N (le_of_max_le_right hle)
  have hc := hN N he (le_of_max_le_left hle)
  have hpos' : 0 < chenCount N := by
    have : (0 : ℝ) < chenCount N := by linarith
    exact_mod_cast this
  unfold chenCount at hpos'
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos'
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, N - p, hp.2.1, by omega, hp.2.2⟩

/-- Vacuity of `card_bset_dvd` and `card_A_dvd`: at `N = 10`, `d = 3`, the primes `p < 10`,
`p ∤ 10`, `3 ∣ 10 − p` are `p = 7` only. -/
example : ((range 10).filter fun p => p.Prime ∧ ¬ p ∣ 10 ∧ 3 ∣ 10 - p) = {7} := by
  ext p; simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; interval_cases p <;> norm_num at *
  · rintro rfl; norm_num

/-! Concrete task198 instances. AI wrote these Lean examples. -/

example : 75 ∈ TSet 98 3 5 := by
  simp only [TSet, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, 3, 5, 5, ?_⟩
  norm_num
example : #((TSet 98 3 5).filter (3 ∣ ·)) ≤ 32 := by
  simpa using card_TSet_multiples_le 98 3 (by norm_num) 3 5
example : #((TSet 98 3 5).filter (fun m => ¬ Nat.Coprime m 15)) ≤ 51 := by
  have h := card_TSet_not_coprime_le 98 15 (by norm_num) 3 5 (by norm_num)
  norm_num [show (15 : ℕ).primeFactors = {3, 5} by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      (by decide : Nat.Prime 3).primeFactors, (by decide : Nat.Prime 5).primeFactors]
    simp] at h
  exact h
example : (TSet 98 3 5).filter (fun m => Nat.Coprime m 2) = TSet 98 3 5 := by
  apply TSet_coprime_of_small_primeFactors (by norm_num) (by norm_num)
  norm_num [(by decide : Nat.Prime 2).primeFactors]
example : (3 : ℝ) ≤ (5 : ℕ) := by
  have hm : 75 ∈ TSet 98 3 5 := by
    simp only [TSet, mem_filter, mem_range]
    refine ⟨by norm_num, by norm_num, 3, 5, 5, ?_⟩
    norm_num
  exact TSet_rough (by norm_num : (3 : ℝ) ≤ 5) hm (by norm_num : Nat.Prime 5) (by norm_num)
example : (∏ p ∈ (range ⌈(4 : ℝ)⌉₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) = 1 / 3 := by
  norm_num [Finset.prod_filter, Finset.prod_range_succ]
example : (∏ p ∈ (3 : ℕ).primeFactors.filter (fun p : ℕ => 2 < p ∧ (3 : ℝ) ≤ p),
    (1 - 1 / ((p : ℝ) - 1))) = 1 / 2 := by
  norm_num [Finset.prod_filter, (by decide : Nat.Prime 3).primeFactors]
example : (∏ p ∈ (5 : ℕ).primeFactors.filter (fun p : ℕ => 2 < p ∧ (4 : ℝ) ≤ p),
    (1 - 1 / ((p : ℝ) - 1))) = 3 / 4 := by
  norm_num [Finset.prod_filter, (by decide : Nat.Prime 5).primeFactors]
example : 0 ≤ (1 - (1 / 2 : ℝ)) * (1 - 1 / 2) := by
  have h := chen_product_union_bound ({3, 5} : Finset ℕ) (fun _ => (1 / 2 : ℝ))
    (by intro i hi; norm_num) (by intro i hi; norm_num)
  norm_num at h ⊢
example : ((30 : ℕ).primeFactors.card : ℝ) ≤ log 30 / log 2 :=
  chen_primeFactors_card_log 30 (by norm_num)
example : ∃ C : ℝ, 0 < C ∧
    ∑ d ∈ Icc 1 10, (#((TSet 98 3 5).filter (fun m => ¬ Nat.Coprime m d)) : ℝ) /
      (d.totient : ℝ) ≤ C * (98 / 3 : ℝ) * (1 + log 10) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := sum_TSet_coprime_loss_le
  exact ⟨C, hC, hbound 98 10 3 5 (by norm_num) (by norm_num)⟩
example : Tendsto (fun N : ℕ => log (√(N : ℝ) / log N ^ (0 : ℝ)) /
    log ((N : ℝ) ^ ((1 : ℝ) / 8))) atTop (𝓝 4) := by
  have h := chen_sieve_parameter_tendsto ((1 : ℝ) / 8) 0 (by norm_num)
  norm_num at h ⊢
  exact h
example : Tendsto (fun N : ℕ => log (√(N : ℝ) / log N ^ (0 : ℝ)) /
    log ((N : ℝ) ^ ((1 : ℝ) / 3))) atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := chen_sieve_parameter_tendsto ((1 : ℝ) / 3) 0 (by norm_num)
  norm_num at h ⊢
  exact h
example : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3) ≤ Mchen N := by
  simpa using error_small 1 (by norm_num)

example : (1 / 1500 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≠ exp (-eulerMascheroniConstant) := by
  refine ⟨by norm_num, le_rfl, ?_⟩
  have hγ := one_half_lt_eulerMascheroniConstant
  have hh : exp (-eulerMascheroniConstant) < 1 := by
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by linarith)
  exact ne_of_gt hh


end LeanLab.AlmostPrimeSums.Decomp1527c
