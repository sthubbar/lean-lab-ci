/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T0703Z-4724, unit U-1388, track T1.
P0072 Togashi and Uchiyama 1964, J. Fac. Sci. Hokkaido Univ. 18, pp. 60 to 68, Section 5,
pp. 67 to 68, lab copy papers/P0072.pdf and papers/P0072.txt.

This file wires the PROVED counting steps of TogashiUchiyamaCount.lean into one Section 5
argument over the paper's own finite sets, so that the main theorem rests only on the
two sieve inequalities and the S₃ size bound, as named hypotheses.

The paper's sets, for an even N, z = N^{1/6}, z₁ = N^{1/3}, a_n = n(N - n):
* `Aset N`: 1 ≤ n ≤ N with (n, N) = 1.
* `S1set N`: those n with no prime p ≤ z dividing a_n; #S1set N is S₁ of Lemma 4.
* `Qset N`: primes q with z < q ≤ z₁ and (q, N) = 1.
* `Sq N q`: n in S1set N with q ∣ a_n; #Sq N q is S(q) of Lemma 5.
* `S2set N`: n in S1set N with at least three distinct q in Qset N dividing a_n; S₂.
* `S3set N`: n in S1set N with q² ∣ a_n for some q in Qset N; S₃.
* `Sset N`: S1set N minus S2set N minus S3set N; the paper's S.
Integer forms: p ≤ N^{1/6} iff p⁶ ≤ N, and q ≤ N^{1/3} iff q³ ≤ N, for naturals.

PROVED unconditional: `S2_double_count` 3 S₂ ≤ Σ_q S(q), `S1_le` S₁ ≤ S + S₂ + S₃,
`omega_of_mem_Sset` every n in S has V(n) ≤ 3 and V(N - n) ≤ 3, `exists_of_two_lt` S > 2
gives n with 1 < n < N - 1, (n, N) = 1, V(n) ≤ 3, V(N - n) ≤ 3, and `section5_arith`.
CONDITIONAL ON Lemma 4, the Selberg upper sieve sum of Lemma 5, the S₃ bound and the size
facts for large N: `togashiUchiyama_of_sieve`. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.TogashiUchiyamaCount

open Finset

namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

open LeanLab.AlmostPrimeSums.TogashiUchiyamaCount

/-- 1 ≤ n ≤ N with (n, N) = 1. -/
def Aset (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => n.Coprime N)

/-- No prime p with p⁶ ≤ N, that is p ≤ z = N^{1/6}, divides n(N - n). -/
def sieved (N n : ℕ) : Prop :=
  ∀ p ∈ range (N + 1), p.Prime → p ^ 6 ≤ N → ¬ p ∣ n * (N - n)

instance (N n : ℕ) : Decidable (sieved N n) := by unfold sieved; infer_instance

/-- The sifted set of Lemma 4, S₁ = P(N^{1/6}). -/
def S1set (N : ℕ) : Finset ℕ := (Aset N).filter (sieved N)

/-- Primes q with z < q ≤ z₁ and (q, N) = 1. -/
def Qset (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N ∧ q.Coprime N)

/-- S(q) of Lemma 5. -/
def Sq (N q : ℕ) : Finset ℕ := (S1set N).filter (fun n => q ∣ n * (N - n))

/-- S₂: at least three distinct q of Qset N divide a_n. -/
def S2set (N : ℕ) : Finset ℕ :=
  (S1set N).filter (fun n => 2 + 1 ≤ ((Qset N).filter (fun q => q ∣ n * (N - n))).card)

/-- S₃: some q² with q in Qset N divides a_n. -/
def S3set (N : ℕ) : Finset ℕ :=
  (S1set N).filter (fun n => ∃ q ∈ Qset N, q ^ 2 ∣ n * (N - n))

/-- The paper's S. -/
def Sset (N : ℕ) : Finset ℕ := (S1set N).filter (fun n => n ∉ S2set N ∧ n ∉ S3set N)

/-- p. 65 with r = 2: 3 S₂ ≤ Σ_{q} S(q). -/
theorem S2_double_count (N : ℕ) :
    3 * (S2set N).card ≤ ∑ q ∈ Qset N, (Sq N q).card :=
  lemma5_double_count (S1set N) (Qset N) (fun n q => q ∣ n * (N - n)) 2

/-- p. 67: S ≥ S₁ - S₂ - S₃. -/
theorem S1_le (N : ℕ) : (S1set N).card ≤ (Sset N).card + (S2set N).card + (S3set N).card :=
  section5_inclusion (S1set N) (S2set N) (S3set N)

lemma mem_Aset {N n : ℕ} : n ∈ Aset N ↔ 1 ≤ n ∧ n ≤ N ∧ n.Coprime N := by
  simp [Aset, and_assoc]

lemma lt_of_mem_Aset {N n : ℕ} (hN : 2 ≤ N) (h : n ∈ Aset N) : n < N := by
  rw [mem_Aset] at h
  rcases h.2.1.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso; subst heq
    have := h.2.2; rw [Nat.coprime_self] at this; omega

/-- A prime factor of a_n, for n in S₁, exceeds z and is coprime to N. -/
lemma big_of_mem_S1 {N n p : ℕ} (hn : n ∈ S1set N) (hp : p.Prime) (hd : p ∣ n * (N - n)) :
    N < p ^ 6 := by
  rw [S1set, mem_filter] at hn
  by_contra hc'
  have hc : p ^ 6 ≤ N := not_lt.mp hc'
  have hpN : p ≤ N := le_trans (Nat.le_self_pow (by norm_num) p) hc
  exact hn.2 p (mem_range.mpr (by omega)) hp hc hd

lemma coprime_of_mem_S1 {N n p : ℕ} (hn : n ∈ S1set N) (hp : p.Prime) (hd : p ∣ n * (N - n)) :
    p.Coprime N := by
  rw [S1set, mem_filter, mem_Aset] at hn
  obtain ⟨⟨_, hnN, hcop⟩, _⟩ := hn
  rw [hp.coprime_iff_not_dvd]
  intro hpN
  have hpn : p ∣ n := by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact h
    · have := Nat.dvd_sub hpN h
      rwa [Nat.sub_sub_self hnN] at this
  have := Nat.dvd_gcd hpn hpN
  rw [hcop] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma mem_Qset_of {N n q : ℕ} (hn : n ∈ S1set N) (hq : q.Prime) (hd : q ∣ n * (N - n))
    (h3 : q ^ 3 ≤ N) : q ∈ Qset N := by
  rw [Qset, mem_filter, mem_range]
  have hqN : q ≤ N := le_trans (Nat.le_self_pow (by norm_num) q) h3
  exact ⟨by omega, hq, big_of_mem_S1 hn hq hd, h3, coprime_of_mem_S1 hn hq hd⟩

/-- pp. 67 to 68: every n in S has V(n) ≤ 3 and V(N - n) ≤ 3. -/
theorem omega_of_mem_Sset {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ Sset N) :
    ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  have hn' := hn
  rw [Sset, mem_filter] at hn'
  obtain ⟨h1, hS2, hS3⟩ := hn'
  have hA : n ∈ Aset N := (mem_filter.mp h1).1
  have hnN : n < N := lt_of_mem_Aset hN hA
  have hn0 : 0 < n := (mem_Aset.mp hA).1
  have ha : n * (N - n) ≠ 0 := Nat.mul_ne_zero hn0.ne' (by omega)
  refine section5_final_paper hn0 hnN ?_ ?_ ?_
  · intro p hp
    rw [Nat.mem_primeFactors_of_ne_zero ha] at hp
    exact big_of_mem_S1 h1 hp.1 hp.2
  · have hsub : (n * (N - n)).primeFactors.filter (fun q => q ^ 3 ≤ N) ⊆
        (Qset N).filter (fun q => q ∣ n * (N - n)) := by
      intro q hq
      rw [mem_filter, Nat.mem_primeFactors_of_ne_zero ha] at hq
      exact mem_filter.mpr ⟨mem_Qset_of h1 hq.1.1 hq.1.2 hq.2, hq.1.2⟩
    have : ¬ 2 + 1 ≤ ((Qset N).filter (fun q => q ∣ n * (N - n))).card := by
      intro h; exact hS2 (mem_filter.mpr ⟨h1, h⟩)
    have := card_le_card hsub
    omega
  · intro q hq h3 hq2
    rw [Nat.mem_primeFactors_of_ne_zero ha] at hq
    exact hS3 (mem_filter.mpr ⟨h1, q, mem_Qset_of h1 hq.1 hq.2 h3, hq2⟩)

/-- p. 67 to 68: S > 2 gives n with 1 < n < N - 1, (n, N) = 1, V(n) ≤ 3, V(N - n) ≤ 3. -/
theorem exists_of_two_lt {N : ℕ} (hN : 2 ≤ N) (hS : 2 < (Sset N).card) :
    ∃ n, 1 < n ∧ n < N - 1 ∧ n.Coprime N ∧
      ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  have hc : 0 < ((Sset N) \ {1, N - 1}).card := by
    have := le_card_sdiff ({1, N - 1} : Finset ℕ) (Sset N)
    have h2 : ({1, N - 1} : Finset ℕ).card ≤ 2 := card_le_two
    omega
  obtain ⟨n, hn⟩ := card_pos.mp hc
  rw [mem_sdiff, mem_insert, mem_singleton] at hn
  obtain ⟨hnS, hne⟩ := hn
  have h1 : n ∈ S1set N := (mem_filter.mp hnS).1
  have hA : n ∈ Aset N := (mem_filter.mp h1).1
  have hnN := lt_of_mem_Aset hN hA
  have hA' := mem_Aset.mp hA
  refine ⟨n, by omega, by omega, hA'.2.2, omega_of_mem_Sset hN hnS⟩

/-- The arithmetic of p. 67 over abstract counts: S₁ > 26.4612 M - E, Σ S(q) ≤ I M + 3E with
I < 79.3026, 3 S₂ ≤ Σ S(q), S₃ ≤ E, S₁ ≤ S + S₂ + S₃, 3E ≤ 0.0001 M give S > 0.0269 M. -/
theorem section5_arith {S S1 S2 S3 SQ M E I : ℝ} (hM : 0 < M)
    (lemma4 : 26.4612 * M - E < S1) (lemma5 : SQ ≤ I * M + 3 * E) (hI : I < 79.3026)
    (hdc : 3 * S2 ≤ SQ) (hS3 : S3 ≤ E) (hincl : S1 ≤ S + S2 + S3) (hE : 3 * E ≤ 0.0001 * M) :
    0.0269 * M < S := by
  have : I * M < 79.3026 * M := mul_lt_mul_of_pos_right hI hM
  linarith

/-- Vacuity check of `section5_arith`: all hypotheses hold at M = 1, E = 0, I = 78,
S₁ = 27, Σ S(q) = 78, S₂ = 26, S₃ = 0, S = 1. -/
example : (0.0269 : ℝ) * 1 < 1 :=
  section5_arith (S1 := 27) (S2 := 26) (S3 := 0) (SQ := 78) (E := 0) (I := 78)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Togashi and Uchiyama 1964, Theorem, Section 5 assembly over the paper's sets.**
CONDITIONAL ON: `lemma4`, Lemma 4 p. 63, S₁ > 26.4612 M - E with M = A_N φ(N)/log² N;
`lemma5`, the Selberg upper sieve of Section 3 summed over q, Σ_{z<q≤z₁} S(q) ≤ I(ε) M + 3E,
with `hI`, I(ε) < 79.3026 from Section 4; `hS3`, S₃ ≤ E, p. 67; `hE` and `hM`, the size
facts 3E ≤ 0.0001 M and 0.0269 M > 2 for N ≥ N₀(ε). Everything else is PROVED here. -/
theorem togashiUchiyama_of_sieve {N : ℕ} {M E I : ℝ} (hN : 2 ≤ N)
    (lemma4 : 26.4612 * M - E < ((S1set N).card : ℝ))
    (lemma5 : ((∑ q ∈ Qset N, (Sq N q).card : ℕ) : ℝ) ≤ I * M + 3 * E) (hI : I < 79.3026)
    (hS3 : ((S3set N).card : ℝ) ≤ E) (hE : 3 * E ≤ 0.0001 * M) (hM : 2 < 0.0269 * M) :
    ∃ n, 1 < n ∧ n < N - 1 ∧ n.Coprime N ∧
      ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  have hM0 : 0 < M := by linarith
  have hdc : (3 : ℝ) * ((S2set N).card : ℝ) ≤ ((∑ q ∈ Qset N, (Sq N q).card : ℕ) : ℝ) := by
    exact_mod_cast S2_double_count N
  have hincl : ((S1set N).card : ℝ) ≤ (Sset N).card + (S2set N).card + (S3set N).card := by
    exact_mod_cast S1_le N
  have := section5_arith hM0 lemma4 lemma5 hI hdc hS3 hincl hE
  refine exists_of_two_lt hN ?_
  have h2 : (2 : ℝ) < (Sset N).card := by linarith
  exact_mod_cast h2

/-- Vacuity check of the counting core at N = 8: S = {1, 3, 5, 7} has more than two
elements, and `exists_of_two_lt` returns n = 3, N - n = 5. -/
example : 2 < (Sset 8).card := by decide

example : ∃ n, 1 < n ∧ n < 8 - 1 ∧ n.Coprime 8 ∧
    ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (8 - n) ≤ 3 :=
  exists_of_two_lt (by norm_num) (by decide)

end LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.S2_double_count
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.S1_le
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.omega_of_mem_Sset
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.exists_of_two_lt
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.section5_arith
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5.togashiUchiyama_of_sieve
