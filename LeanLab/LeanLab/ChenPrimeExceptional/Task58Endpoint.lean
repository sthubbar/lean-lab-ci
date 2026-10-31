/-
AI wrote this Lean code for CODEX task58.
Endpoint bookkeeping for P0039 equations 3.1, 3.2 and 3.11.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.U1433GTSValues

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task58

open U1433 U1424

noncomputable section

/-- Count the prime divisors below the upper endpoint, with the lower endpoint included. -/
def openScount (lo a : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) < a)).card

/-- Count the prime divisors equal to the upper endpoint. -/
def endpointCount (lo a : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) = a)).card

/-- The closed count is the disjoint sum of the open count and the endpoint count. -/
theorem Scount_split (lo a : ℝ) (n : ℕ) :
    Scount lo a n = openScount lo a n + endpointCount lo a n := by
  classical
  unfold Scount openScount endpointCount
  have he : n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ a) =
      n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) < a) ∪
      n.primeFactors.filter (fun p : ℕ => lo ≤ (p : ℝ) ∧ (p : ℝ) = a) := by
    ext p
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hp, hlo, hpa⟩
      rcases lt_or_eq_of_le hpa with h | h
      · exact Or.inl ⟨hp, hlo, h⟩
      · exact Or.inr ⟨hp, hlo, h⟩
    · rintro (⟨hp, hlo, h⟩ | ⟨hp, hlo, h⟩)
      · exact ⟨hp, hlo, h.le⟩
      · exact ⟨hp, hlo, h.le⟩
  rw [he, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro p hp hq
  simp only [mem_filter] at hp hq
  linarith [hp.2.2, hq.2.2]

private lemma three_factors {q p₁ p₂ p₃ : ℕ} (hq : q.Prime) (h1 : p₁.Prime)
    (h2 : p₂.Prime) (h3 : p₃.Prime) (hd : q ∣ p₁ * p₂ * p₃) :
    q = p₁ ∨ q = p₂ ∨ q = p₃ := by
  rcases hq.dvd_mul.mp hd with hd | hd
  · rcases hq.dvd_mul.mp hd with hd | hd
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq h1).mp hd)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq h2).mp hd))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq h3).mp hd))

private lemma real_prime_pos {p : ℕ} (hp : p.Prime) : (0 : ℝ) < p := by
  exact_mod_cast hp.pos

/-- The open count is one on B1, including at prime endpoints. -/
theorem openScount_B1 {lo a N : ℝ} {n : ℕ} (hB : InB1 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 4 * a ^ 3 ≤ N) : openScount lo a n = 1 := by
  classical
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, rfl, hlo1, hp1a, hap2, hp2N, hlo3⟩ := hB
  have hn' : N ≤ 2 * ((p₁ : ℝ) * p₂ * p₃) := by push_cast at hn; exact hn
  have hap3 := B1_p3_large (real_prime_pos h1) (real_prime_pos h2) (real_prime_pos h3)
    hp1a hp2N hn' ha
  have hne : p₁ * p₂ * p₃ ≠ 0 := mul_ne_zero (mul_ne_zero h1.ne_zero h2.ne_zero) h3.ne_zero
  unfold openScount
  rw [card_eq_one]
  refine ⟨p₁, ?_⟩
  ext q
  simp only [mem_filter, Nat.mem_primeFactors, mem_singleton]
  constructor
  · rintro ⟨⟨hq, hd, -⟩, -, hqa⟩
    rcases three_factors hq h1 h2 h3 hd with rfl | rfl | rfl
    · rfl
    · linarith
    · linarith
  · rintro rfl
    exact ⟨⟨h1, ⟨p₂ * p₃, by ring⟩, hne⟩, hlo1, hp1a⟩

/-- The open count is zero on B2, including at prime endpoints. -/
theorem openScount_B2 {lo a N : ℝ} {n : ℕ} (hB : InB2 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 8 * a ^ 3 < N) : openScount lo a n = 0 := by
  classical
  obtain ⟨p₁, p₂, p₃, h1, h2, h3, rfl, hap1, h12, hp2N, hlo3⟩ := hB
  have h12' : (p₁ : ℝ) ≤ p₂ := by exact_mod_cast h12
  have hn' : N ≤ 2 * ((p₁ : ℝ) * p₂ * p₃) := by push_cast at hn; exact hn
  have hap3 := B2_p3_large (real_prime_pos h1) (real_prime_pos h2) (real_prime_pos h3)
    h12' hp2N hn' ha
  unfold openScount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q hq
  simp only [Nat.mem_primeFactors] at hq
  rintro ⟨-, hqa⟩
  rcases three_factors hq.1 h1 h2 h3 hq.2.1 with rfl | rfl | rfl <;> linarith

/-- Exact closed count on B1 without EndpointNotPrime. -/
theorem Scount_B1_corrected {lo a N : ℝ} {n : ℕ} (hB : InB1 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 4 * a ^ 3 ≤ N) :
    Scount lo a n = 1 + endpointCount lo a n := by
  rw [Scount_split, openScount_B1 hB hn ha]

/-- Exact closed count on B2 without EndpointNotPrime. -/
theorem Scount_B2_corrected {lo a N : ℝ} {n : ℕ} (hB : InB2 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 8 * a ^ 3 < N) :
    Scount lo a n = endpointCount lo a n := by
  rw [Scount_split, openScount_B2 hB hn ha, zero_add]

/-- The endpoint count vanishes under the existing endpoint condition. -/
theorem endpointCount_zero {a : ℝ} (h : EndpointNotPrime a) (lo : ℝ) (n : ℕ) :
    endpointCount lo a n = 0 := by
  classical
  unfold endpointCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hmem
  exact h p (Nat.mem_primeFactors.mp hp).1 hmem.2


/-- At most one distinct prime equals a given real endpoint. -/
theorem endpointCount_le_one (lo a : ℝ) (n : ℕ) : endpointCount lo a n ≤ 1 := by
  classical
  unfold endpointCount
  apply card_le_one.mpr
  intro p hp q hq
  simp only [mem_filter] at hp hq
  exact_mod_cast hp.2.2.trans hq.2.2.symm

/-- Prime endpoints can add at most one to the B1 count. -/
theorem Scount_B1_le_two {lo a N : ℝ} {n : ℕ} (hB : InB1 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 4 * a ^ 3 ≤ N) : Scount lo a n ≤ 2 := by
  rw [Scount_B1_corrected hB hn ha]
  have h := endpointCount_le_one lo a n
  omega

/-- Prime endpoints can add at most one to the B2 count. -/
theorem Scount_B2_le_one {lo a N : ℝ} {n : ℕ} (hB : InB2 lo a N n)
    (hn : N ≤ 2 * (n : ℝ)) (ha : 8 * a ^ 3 < N) : Scount lo a n ≤ 1 := by
  rw [Scount_B2_corrected hB hn ha]
  exact endpointCount_le_one lo a n

/-- Irrational endpoints satisfy the existing named endpoint condition. -/
theorem endpointNotPrime_of_irrational {a : ℝ} (ha : Irrational a) : EndpointNotPrime a := by
  intro q hq hqa
  apply ha.ne_rat (q : ℚ)
  simpa using hqa.symm

/-- A non-prime endpoint can be chosen inside any nonempty open real interval. -/
theorem exists_endpointNotPrime_between {a b : ℝ} (hab : a < b) :
    ∃ c : ℝ, a < c ∧ c < b ∧ EndpointNotPrime c := by
  obtain ⟨c, hc, hac, hcb⟩ := exists_irrational_btwn hab
  exact ⟨c, hac, hcb, endpointNotPrime_of_irrational hc⟩

/-- For a fixed base N greater than one, arbitrarily small positive delta can avoid prime
endpoints at the cutoff N to the one third minus delta. -/
theorem exists_small_delta_endpoint {N ε : ℝ} (hN : 1 < N) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ EndpointNotPrime (N ^ ((1 : ℝ) / 3 - δ)) := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 < log N := log_pos hN
  have hlow : N ^ ((1 : ℝ) / 3 - ε) < N ^ ((1 : ℝ) / 3) :=
    rpow_lt_rpow_of_exponent_lt hN (by linarith)
  obtain ⟨a, haI, hla, hau⟩ := exists_irrational_btwn hlow
  have ha0 : 0 < a := (rpow_pos_of_pos hN0 _).trans hla
  let δ : ℝ := (1 : ℝ) / 3 - log a / log N
  have hla' := log_lt_log (rpow_pos_of_pos hN0 _) hla
  have hau' := log_lt_log ha0 hau
  rw [log_rpow hN0] at hla' hau'
  have hquotlo : (1 : ℝ) / 3 - ε < log a / log N := (lt_div_iff₀ hlogN).2 hla'
  have hquothi : log a / log N < (1 : ℝ) / 3 := (div_lt_iff₀ hlogN).2 hau'
  have he : N ^ ((1 : ℝ) / 3 - δ) = a := by
    have hex : (1 : ℝ) / 3 - δ = log a / log N := by dsimp [δ]; ring
    rw [hex]
    exact rpow_logb hN0 (ne_of_gt hN) ha0
  refine ⟨δ, ?_, ?_, ?_⟩
  · dsimp [δ]; linarith
  · dsimp [δ]; linarith
  · rw [he]
    exact endpointNotPrime_of_irrational haI


/-- One sufficiently small delta avoids prime endpoints simultaneously for every natural
base N greater than one. The choice of delta is independent of N. -/
theorem exists_uniform_delta_endpoint {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∀ N : ℕ, 1 < N →
      EndpointNotPrime ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) := by
  let bad : Set ℝ := Set.range (fun nq : ℕ × ℕ =>
    (1 : ℝ) / 3 - log (nq.2 : ℝ) / log (nq.1 : ℝ))
  have hc : bad.Countable := Set.countable_range _
  have hex : ∃ δ ∈ Set.Ioo (0 : ℝ) ε, δ ∉ bad := by
    by_contra h
    push_neg at h
    have hsub : Set.Ioo (0 : ℝ) ε ⊆ bad := fun δ hδ => h δ hδ
    have hcount : (Set.Ioo (0 : ℝ) ε).Countable := hc.mono hsub
    have hle := Cardinal.Real.Ioo_countable_iff.mp hcount
    linarith
  obtain ⟨δ, hδ, hnot⟩ := hex
  refine ⟨δ, hδ.1, hδ.2, ?_⟩
  intro N hN q hq hcut
  apply hnot
  refine ⟨(N, q), ?_⟩
  change (1 : ℝ) / 3 - log (q : ℝ) / log (N : ℝ) = δ
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : log (N : ℝ) ≠ 0 := (log_pos hN').ne'
  have he := congrArg log hcut
  rw [log_rpow hNp] at he
  have hdiv : log (q : ℝ) / log (N : ℝ) = (1 : ℝ) / 3 - δ :=
    (div_eq_iff hlog).2 he
  rw [hdiv]
  ring

#print axioms three_factors
#print axioms real_prime_pos

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.Scount_split
#print axioms LeanLab.ChenPrimeExceptional.Task58.openScount_B1
#print axioms LeanLab.ChenPrimeExceptional.Task58.openScount_B2
#print axioms LeanLab.ChenPrimeExceptional.Task58.Scount_B1_corrected
#print axioms LeanLab.ChenPrimeExceptional.Task58.Scount_B2_corrected
#print axioms LeanLab.ChenPrimeExceptional.Task58.endpointCount_zero

#print axioms LeanLab.ChenPrimeExceptional.Task58.endpointCount_le_one
#print axioms LeanLab.ChenPrimeExceptional.Task58.Scount_B1_le_two
#print axioms LeanLab.ChenPrimeExceptional.Task58.Scount_B2_le_one
#print axioms LeanLab.ChenPrimeExceptional.Task58.endpointNotPrime_of_irrational
#print axioms LeanLab.ChenPrimeExceptional.Task58.exists_endpointNotPrime_between
#print axioms LeanLab.ChenPrimeExceptional.Task58.exists_small_delta_endpoint

#print axioms LeanLab.ChenPrimeExceptional.Task58.exists_uniform_delta_endpoint
