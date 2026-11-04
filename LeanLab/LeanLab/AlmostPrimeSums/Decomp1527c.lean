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

/-!
Mertens' third theorem with its exact constant, ported privately.

The block below is a verbatim copy (namespace `Port1527c`) of
`LeanLab/BS2022GRH/PortedMertens.lean` in this repository, itself an adaptation for CODEX
task224 of `prove2me/TaoFivePrimes_reciprocal_prime_mertens_limit.lean` (Prove2Me id
415d7119-0292-4cbd-9e1f-bc7d99cde221, accepted author xuanji), whose underlying development
is by the PrimeNumberTheoremAnd contributors, Apache License 2.0,
revision 55270df807213fc3584523d09e0311d7dc073ff5.
Copyright the PrimeNumberTheoremAnd contributors.

It is reproduced here because `LeanLab.AlmostPrimeSums.Decomp1527c.lean` has frozen imports and
cannot import that module, but its leaf `mertens_constant_identification` closes from it.
The only edits are the namespace wrapper and the three `simp only [mem_Ioi]` steps, which had to
be written `Set.mem_Ioi` because this file opens `Finset` at the top level.
-/

namespace Port1527c

open _root_.Real
open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

section Issue1584
open MeasureTheory Set Filter Topology

/-- The integrand `log v * exp (-v)` is integrable on `Ioi 0`. -/
private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/-- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/-- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Set.Ioi 1 = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Set.Ici 1 = Set.Ici 0 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [Set.mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [Set.mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [Set.mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

/-
\section{Mertens' theorems}

In this section we give explicit versions of Mertens' theorems:
\begin{itemize}
\item Mertens' first theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x + O(1)$.
\item Mertens' first theorem (prime form): $\sum_{p \leq x} \frac{\log p}{p} = \log x + O(1)$.
\item Mertens' second theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n \log n} = \log \log x + \gamma + O(1/\log x)$.
\item Mertens' second theorem (prime form): $\sum_{p \leq x} \frac{1}{p} = \log \log x + M + O(1/\log x)$, where $M$ is the Meissel-Mertens constant.
\item Mertens' third theorem: $\prod_{p \leq x} (1 - \frac{1}{p}) = e^{-\gamma}/\log x + O(1/\log^2 x)$.
\end{itemize}
We aim to upstreaming these results to Mathlib.  In particular, the arguments here should be self-contained and written for efficiency, coherency, and clarity.  As such, extensive use of AI tools is \emph{strongly discouraged} in this section.

The arguments here are drawn from Leo Goldmakher's ``A quick proof of Mertens' theorem'' from https://web.williams.edu/Mathematics/lg5/mertens.pdf

The unfinished formalization of Mertens' theorems by Arend Mellendijk in https://github.com/FLDutchmann/Analytic/blob/main/Analytic/Mertens.lean may also be relevant here.
-/


open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]


theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]


noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind


theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring




theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring


theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩




noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind


theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity


theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl


theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq


theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]



theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩


noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)


noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa


private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [local fun_prop] measurable_from_top

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp


theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one


theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_setOf_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/-- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/-- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp]
private lemma c_zero : c 0 = 0 := by simp [c]
@[simp]
private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/-- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/-- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/-- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/-- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/-- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end


private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs


private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs


private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/-- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/-- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/-- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/-- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2


private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal


private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/-- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

/-- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/-- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/-- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/-- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/-- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/-- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end


theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)


noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)


theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one


lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/-- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring


theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

end Mertens

open Filter Topology

theorem solution :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x))
      atTop (nhds (Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))) := by
  have hfin (n : ℕ) : Nat.primesLE n = (Finset.Ioc 0 n).filter Nat.Prime := by
    rw [Nat.primesLE_eq_filter_Icc_one] <;> rfl
  have hc : Mertens.M = Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    rw [Mertens.M.eq, Mertens.γ.eq_eulerMascheroni]
    congr 1
    exact (Mertens.tsum_primes_eq_tsum_ite
      (fun n : ℕ => Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))).symm
  have hzero : Tendsto Mertens.E₂p atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h := hzero.add_const Mertens.M
  rw [zero_add, hc] at h
  convert h using 1
  funext x
  simp only [Mertens.E₂p, hfin, hc]
  ring

open _root_.Real Filter Asymptotics Topology

/-- The prime correction term `log (1 - 1/p) + 1/p`, extended by zero off the primes. -/
noncomputable def g (n : ℕ) : ℝ :=
  if n.Prime then Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) else 0

theorem summable_two_div_sq : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  refine (h.add h).congr (fun n => ?_)
  show 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 = 2 / (n : ℝ) ^ 2
  ring

theorem norm_g_le (n : ℕ) : ‖g n‖ ≤ 2 / (n : ℝ) ^ 2 := by
  have hg : g n = if n.Prime then Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) else 0 := rfl
  rw [hg]
  by_cases hn : n.Prime
  · rw [if_pos hn]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
    have ht1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    have h1m : 0 < 1 - 1 / (n : ℝ) := by linarith
    have hu : Real.log (1 - 1 / (n : ℝ)) ≤ -(1 / (n : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos h1m
      linarith
    have hl : -(1 / (n : ℝ)) - 2 * (1 / (n : ℝ)) ^ 2 ≤ Real.log (1 - 1 / (n : ℝ)) := by
      have hq : Real.log (1 / (1 - 1 / (n : ℝ))) = -Real.log (1 - 1 / (n : ℝ)) := by
        rw [Real.log_div one_ne_zero h1m.ne', Real.log_one]
        ring
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 - 1 / (n : ℝ)) by positivity)
      rw [hq] at h
      have hR : 1 / (1 - 1 / (n : ℝ)) - 1 = (1 / (n : ℝ)) / (1 - 1 / (n : ℝ)) := by
        rw [div_sub_one h1m.ne']
        congr 1
        ring
      rw [hR] at h
      have hle : (1 / (n : ℝ)) / (1 - 1 / (n : ℝ)) ≤ 1 / (n : ℝ) + 2 * (1 / (n : ℝ)) ^ 2 := by
        rw [div_le_iff₀ h1m]
        nlinarith
      linarith
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have h2 : 2 / (n : ℝ) ^ 2 = 2 * (1 / (n : ℝ)) ^ 2 := by
      field_simp
    have hkey : |Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)| ≤ 2 / (n : ℝ) ^ 2 := by
      rw [abs_le, h2]
      constructor <;> linarith
    rw [Real.norm_eq_abs]
    exact hkey
  · rw [if_neg hn, norm_zero]
    positivity

theorem summable_g : Summable g :=
  summable_two_div_sq.of_norm_bounded (fun n => norm_g_le n)

theorem tsum_g : (∑' n : ℕ, g n) = Mertens.M - Mertens.γ := by
  have h := Mertens.M.eq
  simp only [g]
  linarith

theorem tendsto_sum_primesLE_g :
    Tendsto (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      atTop (𝓝 (Mertens.M - Mertens.γ)) := by
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n) atTop
      (𝓝 (Mertens.M - Mertens.γ)) := by
    rw [← tsum_g]
    exact summable_g.hasSum.tendsto_sum_nat
  have heq : ∀ M : ℕ, (∑ p ∈ Nat.primesLE M, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      = ∑ n ∈ Finset.range (M + 1), g n := by
    intro M
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by simp only [g])
  have hcomp : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
    tendsto_add_atTop_nat 1 |>.comp tendsto_nat_floor_atTop
  refine (hsum.comp hcomp).congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  exact (heq ⌊x⌋₊).symm

theorem tendsto_sum_log_one_sub_inv_prime :
    Tendsto (fun x : ℝ =>
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ))) + Real.log (Real.log x))
      atTop (𝓝 (- Real.eulerMascheroniConstant)) := by
  have hSp : (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      = Mertens.M - Mertens.γ := by
    have hsplit := Mertens.tsum_primes_eq_tsum_ite
      (fun t : ℕ => Real.log (1 - 1 / (t : ℝ)) + 1 / (t : ℝ))
    have h2 := tsum_g
    simp only [g] at h2
    rw [h2] at hsplit
    simpa only using hsplit
  have hlim : -(Real.eulerMascheroniConstant +
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))))
      + (Mertens.M - Mertens.γ) = -Real.eulerMascheroniConstant := by
    rw [hSp]
    ring
  have h := solution.neg.add tendsto_sum_primesLE_g
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards with x
  rw [Finset.sum_add_distrib]
  ring

theorem tendsto_eulerProduct_primesLE_mul_log :
    Tendsto (fun x : ℝ => (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ))) * Real.log x)
      atTop (𝓝 (Real.exp (- Real.eulerMascheroniConstant))) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp ((∑ p ∈ Nat.primesLE ⌊x⌋₊,
      Real.log (1 - 1 / (p : ℝ))) + Real.log (Real.log x)))
      atTop (𝓝 (Real.exp (- Real.eulerMascheroniConstant))) :=
    (Real.continuous_exp.tendsto _).comp tendsto_sum_log_one_sub_inv_prime
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hpos : ∀ p ∈ Nat.primesLE ⌊x⌋₊, (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.mem_primesLE.mp hp).2
      exact_mod_cast this.two_le
    have hle : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hprod : (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ)))
      = Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    exact (Real.exp_log (hpos p hp)).symm
  symm
  calc (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ))) * Real.log x
      = Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ))) * Real.log x := by
        rw [hprod]
    _ = Real.exp (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ))) *
        Real.exp (Real.log (Real.log x)) := by rw [Real.exp_log hlog]
    _ = Real.exp ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (1 - 1 / (p : ℝ))) +
        Real.log (Real.log x)) := by rw [Real.exp_add]
end Port1527c

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
  have hfloor : Tendsto (fun x : ℝ => (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1 / (p : ℝ))) * log x)
      atTop (𝓝 (exp (-eulerMascheroniConstant))) :=
    Port1527c.tendsto_eulerProduct_primesLE_mul_log
  have hEp : ∀ z : ℕ, LeanLab.ChenPrimeExceptional.Task101.eulerProduct z
      = ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) := by
    intro z
    unfold LeanLab.ChenPrimeExceptional.Task101.eulerProduct
    rw [Nat.primesLE_eq_filter_Icc_one]
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have hratio0 : Tendsto (fun x : ℝ => x / (x - 1)) atTop (𝓝 1) := by
    have hh : Tendsto (fun x : ℝ => 1 + 1 / (x - 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (hshift.const_div_atTop (1 : ℝ))
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn : x - 1 ≠ 0 := by linarith
    field_simp
    ring
  have heq : Asymptotics.IsEquivalent atTop (fun x : ℝ => x) (fun x => x - 1) :=
    Asymptotics.isEquivalent_of_tendsto_one hratio0
  have hlogeq := heq.log hshift
  have hlogne := (tendsto_log_atTop.comp hshift).eventually_ne_atTop 0
  have hratio : Tendsto (fun x : ℝ => log x / log (x - 1)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hlogne).mp hlogeq
  have hfloor' : Tendsto (fun x : ℝ => (∏ p ∈ Nat.primesLE ⌊x - 1⌋₊, (1 - 1 / (p : ℝ))) * log x)
      atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
    have h := (hfloor.comp hshift).mul hratio
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hn : log (x - 1) ≠ 0 := (log_pos (by linarith)).ne'
    dsimp only [Function.comp_apply]
    field_simp
  refine tendsto_nhds_unique hlim ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hfloor hfloor' ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hlog : 0 ≤ log x := (log_pos (by linarith)).le
    rw [← hEp ⌊x⌋₊]
    exact mul_le_mul_of_nonneg_right (strict_euler_product_bounds x).1 hlog
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
    have hlog : 0 ≤ log x := (log_pos (by linarith)).le
    rw [← hEp ⌊x - 1⌋₊]
    exact mul_le_mul_of_nonneg_right (strict_euler_product_bounds x).2 hlog

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
