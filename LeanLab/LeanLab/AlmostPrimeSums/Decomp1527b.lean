/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file b of three.

The linear sieve machinery behind Chen's theorem, part 2: Rosser's weights of level `D` with
`β = 2` (Iwaniec-Kowalski (6.30), Section 6.4; Friedlander-Iwaniec, Opera de Cribro, ch. 6 and
11), the upper and lower bound sieve inequalities they satisfy, the remainder bookkeeping, the
Jurkat-Richert / Iwaniec main term bounds with `F(s)`, `f(s)` (Iwaniec-Kowalski Theorem 11.13,
Halberstam-Richert ch. 8 Theorem 8.3 and 8.4), and the fundamental lemma (Iwaniec-Kowalski
Lemma 6.3 and Theorem 6.9). Sieve problems are Mathlib's `BoundingSieve`
(`Mathlib/NumberTheory/SelbergSieve.lean`): `X = totalMass`, `g = nu`, `r_d = rem d`,
`S(A, P) = siftedSum`, `V = ∏_{p ∣ P} (1 - g(p))`.

The two main-term leaves `jr_mainSum_upper`, `jr_mainSum_lower` are the deep ones; the
assemblies `jr_upper`, `jr_lower` derive the Jurkat-Richert sieve bounds from the leaves with
no sorry of their own.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.AlmostPrimeSums.Decomp1527a

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real ArithmeticFunction BoundingSieve LeanLab.AlmostPrimeSums.Decomp1527a
attribute [local instance] Classical.propDecidable

/-- The prime factors of `d` in decreasing order `p₁ > p₂ > ⋯ > p_r`. -/
noncomputable def decPrimes (d : ℕ) : List ℕ := d.primeFactors.sort (· ≥ ·)

/-- Rosser's weights with `β = 2` and level `D`: `λ_d = μ(d)` if `d = p₁⋯p_r` is squarefree,
`p₁ > ⋯ > p_r`, and `p₁⋯p_{m-1} p_m³ < D` for every `m` odd (upper, `upper = true`) or every
`m` even (lower, `upper = false`); else `0`. In the code `m` is 0-indexed, so "odd `m`" is
`m % 2 = 0`. Iwaniec-Kowalski (6.30). -/
noncomputable def rosserWeight (D : ℝ) (upper : Bool) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ m < (decPrimes d).length, (upper = true ↔ m % 2 = 0) →
      (((decPrimes d).take m).prod : ℝ) * ((decPrimes d).getD m 0 : ℝ) ^ 3 < D
  then (ArithmeticFunction.moebius d : ℝ) else 0

/-- The linear sieve density condition `Ω₁(K)`: for `2 ≤ w < w'`,
`∏_{p ∣ P, w ≤ p < w'} (1 - g(p))⁻¹ ≤ (log w'/log w)(1 + K/log w)`.
Iwaniec-Kowalski (6.34) with `κ = 1`; Halberstam-Richert `(Ω₂(1))`, `(Ω₂(κ))` p. 142. -/
def LinearDensity (s : BoundingSieve) (K : ℝ) : Prop :=
  ∀ w w' : ℝ, 2 ≤ w → w < w' →
    ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
      (1 - s.nu p)⁻¹ ≤ log w' / log w * (1 + K / log w)

/-- `|λ_d| ≤ 1` for Rosser's weights. -/
theorem abs_rosserWeight_le_one (D : ℝ) (b : Bool) (d : ℕ) : |rosserWeight D b d| ≤ 1 := by
  unfold rosserWeight
  split_ifs
  · exact_mod_cast abs_moebius_le_one
  · simp

private lemma decPrimes_mul_prime {e q : ℕ} (he : e ≠ 0) (hq : q.Prime)
    (hqm : ∀ p ∈ e.primeFactors, q < p) : decPrimes (e * q) = decPrimes e ++ [q] := by
  have hmem : ∀ p ∈ decPrimes e, q < p := by
    intro p hp
    rw [decPrimes, Finset.mem_sort] at hp
    exact hqm p hp
  have htofinset : (decPrimes e ++ [q]).toFinset = (e * q).primeFactors := by
    rw [List.toFinset_append, decPrimes, Finset.sort_toFinset,
      Nat.primeFactors_mul he hq.ne_zero, hq.primeFactors]
    simp
  have hnodup : (decPrimes e ++ [q]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact (hmem x hx).ne'
  have hpair : List.Pairwise (· ≥ ·) (decPrimes e ++ [q]) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact (hmem x hx).le
  have := (List.toFinset_sort (· ≥ ·) hnodup).mpr hpair
  rw [htofinset] at this
  exact this

private def LevelU (D : ℝ) (L : List ℕ) : Prop :=
  ∀ m < L.length, m % 2 = 0 → ((L.take m).prod : ℝ) * (L.getD m 0 : ℝ) ^ 3 < D

private def LevelO (D : ℝ) (L : List ℕ) : Prop :=
  ∀ m < L.length, m % 2 = 1 → ((L.take m).prod : ℝ) * (L.getD m 0 : ℝ) ^ 3 < D

private lemma levelU_append {D : ℝ} {L : List ℕ} {q : ℕ} :
    LevelU D (L ++ [q]) ↔
      LevelU D L ∧ (L.length % 2 = 0 → (L.prod : ℝ) * (q : ℝ) ^ 3 < D) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m hm hpar
      have h' := h m (by simp only [List.length_append, List.length_singleton]; omega) hpar
      rwa [List.take_append_of_le_length (by omega), List.getD_append L [q] 0 m hm] at h'
    · intro hpar
      have h' := h L.length (by simp) hpar
      rw [List.take_append_of_le_length le_rfl, List.getD_append_right L [q] 0 L.length le_rfl,
        List.take_length] at h'
      simpa using h'
  · rintro ⟨hL, hlast⟩ m hm hpar
    rw [List.length_append, List.length_singleton] at hm
    rcases lt_or_eq_of_le (by omega : m ≤ L.length) with hlt | heq
    · have h' := hL m hlt hpar
      rw [List.take_append_of_le_length (by omega), List.getD_append L [q] 0 m hlt]
      exact h'
    · subst heq
      have h' := hlast hpar
      rw [List.take_append_of_le_length le_rfl, List.getD_append_right L [q] 0 L.length le_rfl,
        List.take_length]
      simpa using h'

private lemma levelO_append {D : ℝ} {L : List ℕ} {q : ℕ} :
    LevelO D (L ++ [q]) ↔
      LevelO D L ∧ (L.length % 2 = 1 → (L.prod : ℝ) * (q : ℝ) ^ 3 < D) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m hm hpar
      have h' := h m (by simp only [List.length_append, List.length_singleton]; omega) hpar
      rwa [List.take_append_of_le_length (by omega), List.getD_append L [q] 0 m hm] at h'
    · intro hpar
      have h' := h L.length (by simp) hpar
      rw [List.take_append_of_le_length le_rfl, List.getD_append_right L [q] 0 L.length le_rfl,
        List.take_length] at h'
      simpa using h'
  · rintro ⟨hL, hlast⟩ m hm hpar
    rw [List.length_append, List.length_singleton] at hm
    rcases lt_or_eq_of_le (by omega : m ≤ L.length) with hlt | heq
    · have h' := hL m hlt hpar
      rw [List.take_append_of_le_length (by omega), List.getD_append L [q] 0 m hlt]
      exact h'
    · subst heq
      have h' := hlast hpar
      rw [List.take_append_of_le_length le_rfl, List.getD_append_right L [q] 0 L.length le_rfl,
        List.take_length]
      simpa using h'

private lemma parity (m : ℕ) : (¬ m % 2 = 0) ↔ m % 2 = 1 := by omega

private lemma rosserWeight_true_eq (D : ℝ) (d : ℕ) :
    rosserWeight D true d
      = if Squarefree d ∧ LevelU D (decPrimes d) then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [rosserWeight]
  by_cases h : Squarefree d ∧ LevelU D (decPrimes d)
  · have h' : Squarefree d ∧ ∀ m < (decPrimes d).length,
        (true = true ↔ m % 2 = 0) → ((decPrimes d).take m).prod * ((decPrimes d).getD m 0) ^ 3 < D :=
      ⟨h.1, fun m hm hpar => h.2 m hm (by simpa using hpar)⟩
    rw [ite_eq_left h, ite_eq_left h']
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact h ⟨h1, fun m hm hpar => h2 m hm (by simpa using hpar)⟩

private lemma rosserWeight_false_eq (D : ℝ) (d : ℕ) :
    rosserWeight D false d
      = if Squarefree d ∧ LevelO D (decPrimes d) then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [rosserWeight]
  by_cases h : Squarefree d ∧ LevelO D (decPrimes d)
  · have h' : Squarefree d ∧ ∀ m < (decPrimes d).length,
        (false = true ↔ m % 2 = 0) →
          ((decPrimes d).take m).prod * ((decPrimes d).getD m 0) ^ 3 < D :=
      ⟨h.1, fun m hm hpar => by
        have hp : ¬ m % 2 = 0 := by simpa [Bool.false_eq_true] using hpar
        exact h.2 m hm ((parity m).mp hp)⟩
    rw [ite_eq_left h, ite_eq_left h']
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact h ⟨h1, fun m hm hpar => h2 m hm (by
      have hp : ¬ m % 2 = 0 := (parity m).mpr hpar
      simpa [Bool.false_eq_true] using hp)⟩

/-- Each divisor `e` of `m` and its partner `q * e` contribute a nonpositive amount. -/

private lemma card_primeFactors_eq_omega (n : ℕ) :
    (n.primeFactors).card = ArithmeticFunction.cardDistinctFactors n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  simp

private lemma len_decPrimes_eq_Omega {e : ℕ} (hsq : Squarefree e) :
    (decPrimes e).length = ArithmeticFunction.cardFactors e := by
  rw [decPrimes, Finset.length_sort, card_primeFactors_eq_omega,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).mpr hsq]

private lemma moebius_cast_eq_one {e : ℕ} (hsq : Squarefree e)
    (hpar : (decPrimes e).length % 2 = 0) : (ArithmeticFunction.moebius e : ℝ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, ← len_decPrimes_eq_Omega hsq]
  have hev : Even (decPrimes e).length := by rw [Nat.even_iff]; exact hpar
  rw [Even.neg_one_pow hev]
  norm_num

/-- Each divisor `e` of `m` and its partner `q * e` contribute a nonnegative amount. -/

private lemma moebius_cast_eq_neg_one {e : ℕ} (hsq : Squarefree e)
    (hpar : (decPrimes e).length % 2 = 1) : (ArithmeticFunction.moebius e : ℝ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, ← len_decPrimes_eq_Omega hsq]
  have hodd : Odd (decPrimes e).length := by rw [Nat.odd_iff]; exact hpar
  rw [Odd.neg_one_pow hodd]
  norm_num

private lemma sum_divisors_pow_mul {f : ℕ → ℝ} {q m : ℕ} (hq : q.Prime) (hcop : Nat.Coprime q m) (k : ℕ) :
    ∑ d ∈ (q ^ k * m).divisors, f d = ∑ j ∈ range (k + 1), ∑ e ∈ m.divisors, f (q ^ j * e) := by
  have hc : Nat.Coprime (q ^ k) m := hcop.pow_left k
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image
    (fun x hx y hy hxy => Nat.Coprime.mul_injOn_divisors hc hx hy hxy)]
  rw [Finset.sum_product, Nat.divisors_prime_pow hq k]
  simp

private lemma add_mul_prime_nonpos {D : ℝ} {q e : ℕ} (he : e ≠ 0) (hq : q.Prime)
    (hqm : ∀ p ∈ e.primeFactors, q < p) :
    rosserWeight D false e + rosserWeight D false (q * e) ≤ 0 := by
  have hcop : Nat.Coprime q e := hq.coprime_iff_not_dvd.mpr fun hd =>
    absurd (hqm q (Nat.mem_primeFactors.mpr ⟨hq, hd, he⟩)) (lt_irrefl q)
  have hdp : decPrimes (q * e) = decPrimes e ++ [q] := by
    rw [Nat.mul_comm]; exact decPrimes_mul_prime he hq hqm
  have hsq : Squarefree (q * e) ↔ Squarefree e := by
    rw [Nat.squarefree_mul hcop]
    exact ⟨fun h => h.2, fun h => ⟨hq.squarefree, h⟩⟩
  have hmuZ : ArithmeticFunction.moebius (q * e) = -ArithmeticFunction.moebius e := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (m := e) (n := q)
      hcop.symm
    rw [ArithmeticFunction.moebius_apply_prime hq] at h
    rw [Nat.mul_comm e q] at h
    rw [h]; ring
  have hmu : (ArithmeticFunction.moebius (q * e) : ℝ) = -(ArithmeticFunction.moebius e : ℝ) := by
    rw [hmuZ]; push_cast; ring
  rw [rosserWeight_false_eq D e, rosserWeight_false_eq D (q * e)]
  by_cases hcond : Squarefree (q * e) ∧ LevelO D (decPrimes (q * e))
  · have hsq' : Squarefree (q * e) := hcond.1
    have hlv : LevelO D (decPrimes (q * e)) := hcond.2
    have hSe : Squarefree e := hsq.mp hsq'
    have hlv' : LevelO D (decPrimes e) := by
      rw [hdp, levelO_append] at hlv; exact hlv.1
    rw [ite_eq_left hcond, ite_eq_left ⟨hSe, hlv'⟩, hmu]
    linarith
  · rw [ite_eq_right hcond]
    by_cases hA : Squarefree e ∧ LevelO D (decPrimes e)
    · rw [ite_eq_left hA]
      have hpar : (decPrimes e).length % 2 = 1 := by
        by_contra hc
        refine absurd ?_ hcond
        refine ⟨hsq.mpr hA.1, ?_⟩
        rw [hdp, levelO_append]
        exact ⟨hA.2, fun hev => absurd hev hc⟩
      have h1 := moebius_cast_eq_neg_one hA.1 hpar
      linarith
    · rw [ite_eq_right hA]
      linarith

private lemma add_mul_prime_nonneg {D : ℝ} {q e : ℕ} (he : e ≠ 0) (hq : q.Prime)
    (hqm : ∀ p ∈ e.primeFactors, q < p) :
    0 ≤ rosserWeight D true e + rosserWeight D true (q * e) := by
  have hcop : Nat.Coprime q e := hq.coprime_iff_not_dvd.mpr fun hd =>
    absurd (hqm q (Nat.mem_primeFactors.mpr ⟨hq, hd, he⟩)) (lt_irrefl q)
  have hdp : decPrimes (q * e) = decPrimes e ++ [q] := by
    rw [Nat.mul_comm]; exact decPrimes_mul_prime he hq hqm
  have hsq : Squarefree (q * e) ↔ Squarefree e := by
    rw [Nat.squarefree_mul hcop]
    exact ⟨fun h => h.2, fun h => ⟨hq.squarefree, h⟩⟩
  have hmuZ : ArithmeticFunction.moebius (q * e) = -ArithmeticFunction.moebius e := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (m := e) (n := q)
      hcop.symm
    rw [ArithmeticFunction.moebius_apply_prime hq] at h
    rw [Nat.mul_comm e q] at h
    rw [h]; ring
  have hmu : (ArithmeticFunction.moebius (q * e) : ℝ) = -(ArithmeticFunction.moebius e : ℝ) := by
    rw [hmuZ]; push_cast; ring
  rw [rosserWeight_true_eq D e, rosserWeight_true_eq D (q * e)]
  by_cases hcond : Squarefree (q * e) ∧ LevelU D (decPrimes (q * e))
  · have hsq' : Squarefree (q * e) := hcond.1
    have hlv : LevelU D (decPrimes (q * e)) := hcond.2
    have hSe : Squarefree e := hsq.mp hsq'
    have hlv' : LevelU D (decPrimes e) := by
      rw [hdp, levelU_append] at hlv; exact hlv.1
    rw [ite_eq_left hcond, ite_eq_left ⟨hSe, hlv'⟩, hmu]
    linarith
  · rw [ite_eq_right hcond]
    by_cases hA : Squarefree e ∧ LevelU D (decPrimes e)
    · rw [ite_eq_left hA]
      have hpar : (decPrimes e).length % 2 = 0 := by
        by_contra hc
        refine absurd ?_ hcond
        refine ⟨hsq.mpr hA.1, ?_⟩
        rw [hdp, levelU_append]
        exact ⟨hA.2, fun hev => absurd hev hc⟩
      have h1 := moebius_cast_eq_one hA.1 hpar
      linarith
    · rw [ite_eq_right hA]
      linarith

/-- LEAF. Rosser's upper weights are an upper bound sieve: `Σ_{d ∣ n} λ⁺_d ≥ [n = 1]` for all
`n`. Proof: the support is closed under deleting the smallest prime, so
`Σ_{d∣n} μ(d) = Σ_{d∣n} λ⁺_d − Σ_{b first exit} [b ∣ n][(n/b, P(p_r)) = 1]`, every first
exit `b = p₁⋯p_r` has `r` odd and `μ(b) = −1`. Iwaniec-Kowalski (6.24) to (6.27) and Section 6.4.
Unit U-1527. -/
theorem rosser_upper_isUpperMoebius (D : ℝ) : IsUpperMoebius (rosserWeight D true) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [ite_eq_left rfl, Nat.divisors_one, Finset.sum_singleton]
    have h1 : rosserWeight D true 1 = 1 := by
      rw [rosserWeight_true_eq]
      simp [decPrimes, LevelU]
    rw [h1]
  · rw [ite_eq_right hn1]
    set q := n.minFac with hqdef
    have hq : q.Prime := Nat.minFac_prime hn1
    obtain ⟨k, m, hm_notdvd, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q hq.ne_one
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · exfalso
        rw [hk0, pow_zero, one_mul] at hn_eq
        exact hm_notdvd (hn_eq ▸ Nat.minFac_dvd n)
      · exact hk
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn_eq
      exact hn0 hn_eq
    have hcop : Nat.Coprime q m := hq.coprime_iff_not_dvd.mpr hm_notdvd
    have hlt : ∀ p ∈ m.primeFactors, q < p := by
      intro p hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
      have hpn : p ∣ n := hn_eq ▸ dvd_mul_of_dvd_right hpd _
      have hle : q ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpn
      exact lt_of_le_of_ne hle (fun heq => hm_notdvd (heq ▸ hpd))
    rw [hn_eq, sum_divisors_pow_mul hq hcop k]
    have hzero : ∀ j ∈ range (k + 1), j ∉ ({0, 1} : Finset ℕ) →
        ∑ e ∈ m.divisors, rosserWeight D true (q ^ j * e) = 0 := by
      intro j hj hj2
      simp only [mem_insert, mem_singleton, not_or] at hj2
      apply Finset.sum_eq_zero
      intro e he
      have hnsq : ¬ Squarefree (q ^ j * e) := by
        intro hsf
        have hdvd : q * q ∣ q ^ j * e := by
          have : q ^ 2 ∣ q ^ j := pow_dvd_pow q (by omega)
          exact dvd_mul_of_dvd_left (by simpa [pow_two] using this) e
        have h1 : Squarefree (q * q) := Squarefree.squarefree_of_dvd hdvd hsf
        exact hq.ne_one (Nat.isUnit_iff.mp (h1 q (dvd_refl (q * q))))
      rw [rosserWeight_true_eq, ite_eq_right (by simp [hnsq])]
    rw [show ∑ j ∈ range (k + 1), (∑ e ∈ m.divisors, rosserWeight D true (q ^ j * e))
        = (∑ e ∈ m.divisors, rosserWeight D true (q ^ 0 * e))
          + (∑ e ∈ m.divisors, rosserWeight D true (q ^ 1 * e)) from ?_]
    · simp only [pow_zero, pow_one, one_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_nonneg
      intro e he
      have hedvd : e ∣ m := (Nat.mem_divisors.mp he).1
      have he0 : e ≠ 0 := by
        rintro rfl
        exact (Nat.mem_divisors.mp he).2 (Nat.zero_dvd.mp hedvd)
      exact add_mul_prime_nonneg he0 hq (fun p hp =>
        hlt p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
          (Nat.mem_primeFactors.mp hp).2.1.trans hedvd, hm0⟩))
    · have hsub : ({0, 1} : Finset ℕ) ⊆ range (k + 1) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [mem_range]
        rcases hx with rfl | rfl <;> omega
      rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by norm_num)]


/-- LEAF. Rosser's lower weights are a lower bound sieve: `Σ_{d ∣ n} λ⁻_d ≤ [n = 1]` for all
`n`; first exits have `r` even and `μ(b) = +1`. Iwaniec-Kowalski (6.24) to (6.27) and
Section 6.4. Unit U-1527. -/
theorem rosser_lower_le (D : ℝ) (n : ℕ) :
    ∑ d ∈ n.divisors, rosserWeight D false d ≤ if n = 1 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [ite_eq_left rfl, Nat.divisors_one, Finset.sum_singleton]
    have h1 : rosserWeight D false 1 = 1 := by
      rw [rosserWeight_false_eq]
      simp [decPrimes, LevelO]
    rw [h1]
  · rw [ite_eq_right hn1]
    set q := n.minFac with hqdef
    have hq : q.Prime := Nat.minFac_prime hn1
    obtain ⟨k, m, hm_notdvd, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q hq.ne_one
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · exfalso
        rw [hk0, pow_zero, one_mul] at hn_eq
        exact hm_notdvd (hn_eq ▸ Nat.minFac_dvd n)
      · exact hk
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn_eq
      exact hn0 hn_eq
    have hcop : Nat.Coprime q m := hq.coprime_iff_not_dvd.mpr hm_notdvd
    have hlt : ∀ p ∈ m.primeFactors, q < p := by
      intro p hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
      have hpn : p ∣ n := hn_eq ▸ dvd_mul_of_dvd_right hpd _
      have hle : q ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpn
      exact lt_of_le_of_ne hle (fun heq => hm_notdvd (heq ▸ hpd))
    rw [hn_eq, sum_divisors_pow_mul hq hcop k]
    have hzero : ∀ j ∈ range (k + 1), j ∉ ({0, 1} : Finset ℕ) →
        ∑ e ∈ m.divisors, rosserWeight D false (q ^ j * e) = 0 := by
      intro j hj hj2
      simp only [mem_insert, mem_singleton, not_or] at hj2
      apply Finset.sum_eq_zero
      intro e he
      have hnsq : ¬ Squarefree (q ^ j * e) := by
        intro hsf
        have hdvd : q * q ∣ q ^ j * e := by
          have : q ^ 2 ∣ q ^ j := pow_dvd_pow q (by omega)
          exact dvd_mul_of_dvd_left (by simpa [pow_two] using this) e
        have h1 : Squarefree (q * q) := Squarefree.squarefree_of_dvd hdvd hsf
        exact hq.ne_one (Nat.isUnit_iff.mp (h1 q (dvd_refl (q * q))))
      rw [rosserWeight_false_eq, ite_eq_right (by simp [hnsq])]
    rw [show ∑ j ∈ range (k + 1), (∑ e ∈ m.divisors, rosserWeight D false (q ^ j * e))
        = (∑ e ∈ m.divisors, rosserWeight D false (q ^ 0 * e))
          + (∑ e ∈ m.divisors, rosserWeight D false (q ^ 1 * e)) from ?_]
    · simp only [pow_zero, pow_one, one_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_nonpos
      intro e he
      have hedvd : e ∣ m := (Nat.mem_divisors.mp he).1
      have he0 : e ≠ 0 := by
        rintro rfl
        exact (Nat.mem_divisors.mp he).2 (Nat.zero_dvd.mp hedvd)
      exact add_mul_prime_nonpos he0 hq (fun p hp =>
        hlt p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
          (Nat.mem_primeFactors.mp hp).2.1.trans hedvd, hm0⟩))
    · have hsub : ({0, 1} : Finset ℕ) ⊆ range (k + 1) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [mem_range]
        rcases hx with rfl | rfl <;> omega
      rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by norm_num)]


/-- LEAF. Lower bound sieve inequality, the mirror of Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: if `Σ_{d∣n} λ_d ≤ [n=1]` for all `n` then
`S ≥ X Σ_{d∣P} λ_d g(d) − Σ_{d∣P} |λ_d||r_d|`. Iwaniec-Kowalski (6.17), (6.18).
Unit U-1527. -/
theorem siftedSum_ge_of_lower (s : BoundingSieve) (lam : ℕ → ℝ)
    (h : ∀ n : ℕ, ∑ d ∈ n.divisors, lam d ≤ if n = 1 then 1 else 0) :
    s.totalMass * s.mainSum lam - s.errSum lam ≤ s.siftedSum := by
  have hA : ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, lam d
      = ∑ n ∈ s.support, ∑ d ∈ Nat.divisors s.prodPrimes,
          (if d ∣ n then s.weights n * lam d else 0 : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_sum,
      ← Nat.divisors_filter_dvd_of_dvd BoundingSieve.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _),
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hdP : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
    by_cases hdn : d ∣ n
    · rw [ite_eq_left (Nat.dvd_gcd hdP hdn), ite_eq_left hdn]
    · rw [ite_eq_right hdn, ite_eq_right]
      intro hc
      exact hdn ((dvd_gcd_iff d s.prodPrimes n).mp hc).2
  have hB : ∑ n ∈ s.support, ∑ d ∈ Nat.divisors s.prodPrimes,
        (if d ∣ n then s.weights n * lam d else 0 : ℝ)
      = ∑ d ∈ Nat.divisors s.prodPrimes, lam d * s.multSum d := by
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]
  have hC : ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, lam d
      ≤ s.siftedSum := by
    rw [siftedSum_eq_sum_support_mul_ite]
    gcongr with n
    exact h _
  have hmain : s.totalMass * s.mainSum lam - s.errSum lam
      ≤ ∑ d ∈ Nat.divisors s.prodPrimes, lam d * s.multSum d := by
    rw [mainSum, errSum, mul_sum, ← sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d _
    rw [BoundingSieve.multSum_eq_main_err, ← abs_mul]
    linarith [neg_abs_le (lam d * s.rem d)]
  rw [← hB, ← hA] at hmain
  exact hmain.trans hC

/-- LEAF. Support of Rosser's weights: for `D > 1`, `λ^±_d ≠ 0` implies `d < D` or `d` prime
(only the lower weights reach the primes `p ≥ D^{1/3}`). For `r ≥ 2` use the condition at the
last or second to last index and `p_r < p_{r-1}`. Iwaniec-Kowalski Section 6.4, below (6.30).
Unit U-1527. -/
private lemma prod_decPrimes {d : ℕ} (hsq : Squarefree d) : (decPrimes d).prod = d := by
  rw [decPrimes, ← Multiset.prod_coe, Finset.sort_eq, Finset.prod_val]
  exact Nat.prod_primeFactors_of_squarefree hsq

private lemma prime_of_mem_decPrimes {d p : ℕ} (hp : p ∈ decPrimes d) : p.Prime := by
  rw [decPrimes, Finset.mem_sort] at hp
  exact Nat.prime_of_mem_primeFactors hp

private lemma decPrimes_strictAnti {d i j : ℕ} (hi : i < (decPrimes d).length)
    (hj : j < (decPrimes d).length) (hij : i < j) : (decPrimes d)[j] < (decPrimes d)[i] := by
  have hs : (decPrimes d).SortedGT := Finset.sortedGT_sort _
  rw [List.sortedGT_iff_pairwise] at hs
  rw [List.pairwise_iff_getElem] at hs
  exact hs i j hi hj hij

/-- The level condition at the last admissible index forces the whole product below `D`. -/
private lemma list_prod_lt_of_level {L : List ℕ} {D : ℝ} {e : ℕ}
    (he : e ≤ 1) (hlen : 2 ≤ L.length)
    (hprime : ∀ p ∈ L, p.Prime)
    (hdec : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j → L[j]'hj < L[i]'hi)
    (hlev : ∀ m, m < L.length → m % 2 = e →
      ((L.take m).prod : ℝ) * (L.getD m 0 : ℝ) ^ 3 < D) :
    ((L.prod : ℕ) : ℝ) < D := by
  set M : ℕ := if (L.length - 1) % 2 = e then L.length - 1 else L.length - 2 with hM
  have hMlt : M < L.length := by
    by_cases hc : (L.length - 1) % 2 = e
    · rw [hM, ite_eq_left hc]; omega
    · rw [hM, ite_eq_right hc]; omega
  have hMpar : M % 2 = e := by
    by_cases hc : (L.length - 1) % 2 = e
    · rw [hM, ite_eq_left hc]; exact hc
    · rw [hM, ite_eq_right hc]
      have := Nat.mod_lt (L.length - 1) (by norm_num : 0 < 2)
      omega
  have hMt : L.length ≤ M + 2 := by
    by_cases hc : (L.length - 1) % 2 = e
    · rw [hM, ite_eq_left hc]; omega
    · rw [hM, ite_eq_right hc]; omega
  set p : ℕ := L.getD M 0 with hp
  have hpget : p = L[M]'hMlt := by
    rw [hp]; exact List.getD_eq_getElem (l := L) (d := 0) (n := M) hMlt
  have hpmem : p ∈ L := by rw [hpget]; exact List.getElem_mem hMlt
  have hp2 : p.Prime := hprime p hpmem
  have hp1 : 1 ≤ p := hp2.one_lt.le
  have hcond : ((L.take M).prod : ℝ) * (p : ℝ) ^ 3 < D := by
    have hh := hlev M hMlt hMpar
    have hpc : (p : ℝ) = (L.getD M 0 : ℝ) := by rw [hp]
    rw [hpc]
    exact hh
  have htailnat : (L.drop (M + 1)).prod ≤ L[M]'hMlt := by
    by_cases hM1 : M + 1 < L.length
    · have hcons : L.drop (M + 1) = L[M + 1]'hM1 :: L.drop (M + 2) :=
        List.drop_eq_getElem_cons hM1
      have hnil : L.drop (M + 2) = [] := by
        apply List.drop_eq_nil_of_le
        omega
      rw [hcons, hnil, List.prod_cons, List.prod_nil, mul_one]
      exact (hdec M (M + 1) hMlt hM1 (by omega)).le
    · have hz : L.drop (M + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hz, List.prod_nil]
      rw [← hpget]
      exact hp1
  have hsplit' : L.take M ++ p :: L.drop (M + 1) = L := by
    have h1 : L.take M ++ [p] = L.take (M + 1) := by
      rw [hpget]
      exact List.take_concat_get' L M hMlt
    have h2 : L.take (M + 1) ++ L.drop (M + 1) = L := List.take_append_drop (M + 1) L
    rw [← List.singleton_append, ← List.append_assoc, h1, h2]
  have hprod : ((L.prod : ℕ) : ℝ) =
      ((L.take M).prod : ℝ) * (p : ℝ) * ((L.drop (M + 1)).prod : ℝ) := by
    conv_lhs => rw [← hsplit']
    rw [List.prod_append, List.prod_cons]
    push_cast
    ring
  have htail : ((L.drop (M + 1)).prod : ℝ) ≤ (p : ℝ) := by
    have hpc : (p : ℝ) = (L[M]'hMlt : ℝ) := by rw [hpget]
    rw [hpc]
    exact_mod_cast htailnat
  rw [hprod]
  have hT : (0:ℝ) ≤ ((L.take M).prod : ℝ) := Nat.cast_nonneg _
  have hpR : (1:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have step1 : ((L.take M).prod : ℝ) * (p : ℝ) * ((L.drop (M + 1)).prod : ℝ)
      ≤ ((L.take M).prod : ℝ) * (p : ℝ) * (p : ℝ) := by
    have hTp : (0:ℝ) ≤ ((L.take M).prod : ℝ) * (p : ℝ) := mul_nonneg hT (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left htail hTp]
  have step2 : ((L.take M).prod : ℝ) * (p : ℝ) * (p : ℝ)
      ≤ ((L.take M).prod : ℝ) * (p : ℝ) ^ 3 := by
    have hs : (p : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hT]
  linarith

theorem rosserWeight_support (D : ℝ) (hD : 1 < D) (b : Bool) (d : ℕ)
    (h : rosserWeight D b d ≠ 0) : (d : ℝ) < D ∨ d.Prime := by
  unfold rosserWeight at h
  split_ifs at h with hcond
  · obtain ⟨hsq, hlev0⟩ := hcond
    have hprod := prod_decPrimes hsq
    by_cases hlen : 2 ≤ (decPrimes d).length
    · left
      have main := list_prod_lt_of_level (L := decPrimes d) (D := D) (e := if b then 0 else 1)
        (by split <;> simp) hlen (fun p hp => prime_of_mem_decPrimes hp)
        (fun i j hi hj hij => decPrimes_strictAnti hi hj hij)
        (fun m hm hpar => by
          have hb : (b = true ↔ m % 2 = 0) := by
            cases b
            · have hne : m % 2 ≠ 0 := by rw [hpar]; norm_num
              simp [hne]
            · simpa using hpar
          exact hlev0 m hm hb)
      rwa [hprod] at main
    · have hlen1 : (decPrimes d).length ≤ 1 := by omega
      rcases hL : decPrimes d with _ | ⟨p, L'⟩
      · left
        have hd1 : d = 1 := by rw [← hprod, hL]; simp
        rw [hd1]; simpa using hD
      · rcases L' with _ | ⟨q, L''⟩
        · right
          have hdp : d = p := by rw [← hprod, hL]; simp
          rw [hdp]
          exact prime_of_mem_decPrimes (by rw [hL]; simp)
        · exfalso
          rw [hL] at hlen1
          simp at hlen1
  · exact absurd rfl h

/-- LEAF. Remainder bookkeeping: if every prime of `P` is `< z ≤ D`, then
`Σ_{d∣P} |λ^±_d||r_d| ≤ Σ_{d∣P, d<D} |r_d|`, by `rosserWeight_support` and `|λ| ≤ 1`.
Iwaniec-Kowalski (6.18), Theorem 11.13 remainder `R(D)`. Unit U-1527. -/
theorem errSum_rosser_le (s : BoundingSieve) (z D : ℝ) (hzD : z ≤ D) (hD : 1 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) (b : Bool) :
    s.errSum (rosserWeight D b) ≤
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  have hs_errSum : s.errSum (rosserWeight D b) = ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| := rfl
  rw [hs_errSum]
  have H : ∀ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d| ≤ if (d : ℝ) < D then |s.rem d| else 0 := by
    intro d hd
    by_cases hdD : (d : ℝ) < D
    · rw [ite_eq_left_iff.mpr (fun hh => False.elim (hh hdD))]
      have := abs_rosserWeight_le_one D b d
      nlinarith [abs_nonneg (s.rem d)]
    · rw [ite_eq_right_iff.mpr (fun hh => False.elim (hdD hh))]
      have h1 : rosserWeight D b d = 0 := by
        by_contra hc
        have := rosserWeight_support D hD b d hc
        rcases this with h_lt | h_prime
        · exact hdD h_lt
        · have hd_primeFactors : d ∈ s.prodPrimes.primeFactors := by
            rw [Nat.mem_primeFactors]
            exact ⟨h_prime, Nat.mem_divisors.mp hd |>.1, fun hh => by
              have hhh := s.prodPrimes_squarefree
              rw [hh] at hhh
              exact not_squarefree_zero hhh⟩
          have h_z := hP d hd_primeFactors
          linarith
      rw [h1]
      simp
  calc ∑ d ∈ s.prodPrimes.divisors, |rosserWeight D b d| * |s.rem d|
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) < D then |s.rem d| else 0 := Finset.sum_le_sum (fun d hd => H d hd)
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
      rw [Finset.sum_filter]

/-- LEAF. Deep. Iwaniec's linear sieve, upper main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z ≤ D ≤ z⁵`,
`Σ_{d∣P} λ⁺_d g(d) ≤ V(z)(F(s) + C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      s.mainSum (rosserWeight D true) ≤ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))) := by
  sorry

/-- LEAF. Deep. Iwaniec's linear sieve, lower main term: given `K ≥ 0` there is `C > 0` such
that for every sieve problem with all primes of `P` below `z`, density `Ω₁(K)`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `Σ_{d∣P} λ⁻_d g(d) ≥ V(z)(f(s) − C (log D)^{-1/3})`, `s = log D / log z`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3 (Jurkat-Richert form).
Unit U-1527. -/
theorem jr_mainSum_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))) ≤ s.mainSum (rosserWeight D false) := by
  sorry

/-- LEAF. Deep. Fundamental lemma of sieve theory, `κ = 1`: given `K ≥ 0` there is `C > 0`
such that whenever all primes of `P` are below `z`, `Ω₁(K)` holds, `z ≥ 2` and `D ≥ z^{10}`,
there are upper and lower bound sieve weights `λ^±` with `|λ^±_d| ≤ 1`, supported on `d ∣ P`,
`d < D`, `λ^±_1 = 1`, `Σ_{d∣n} λ⁺_d ≥ [n=1]` for all `n`,
`Σ_{d∣n} λ⁻_d ≤ [n=1]` for `n ∣ P`, and `|Σ_{d∣P} λ^±_d g(d) − V(z)| ≤ C e^{-s} V(z)`, `s = log D/log z`.
Iwaniec-Kowalski Lemma 6.3 and Theorem 6.9 (`D ≥ z^{9κ+1}`).
Unit U-1527. -/
theorem fundamental_lemma (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  sorry

/-! ### Assemblies: the Jurkat-Richert linear sieve bounds, from the leaves -/

lemma one_lt_of_two_le {z D : ℝ} (hz : 2 ≤ z) (hzD : z ≤ D) : 1 < D := by linarith

/-- **Jurkat-Richert upper bound**, assembled from the leaves `rosser_upper_isUpperMoebius`,
`jr_mainSum_upper`, `errSum_rosser_le` and Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius`: for `X ≥ 0`, `2 ≤ z ≤ D ≤ z⁵`,
`S(A, P) ≤ X V(z)(F(s) + C (log D)^{-1/3}) + Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.4. -/
theorem jr_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ≤ D → D ≤ z ^ 5 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.siftedSum ≤ s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ))))
        + ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_upper K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have h1 := s.siftedSum_le_mainSum_errSum_of_upperMoebius _ (rosser_upper_isUpperMoebius D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD (one_lt_of_two_le hz hzD) hP true
  have h4 : s.totalMass * s.mainSum (rosserWeight D true) ≤ s.totalMass *
      ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (Fsieve (log D / log z) + C * log D ^ (-(1 / 3 : ℝ)))) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-- **Jurkat-Richert lower bound**, assembled from the leaves `rosser_lower_le`,
`siftedSum_ge_of_lower`, `jr_mainSum_lower`, `errSum_rosser_le`: for `X ≥ 0`, `2 ≤ z`,
`z² ≤ D ≤ z⁴`, `S(A, P) ≥ X V(z)(f(s) − C (log D)^{-1/3}) − Σ_{d∣P, d<D} |r_d|`.
Iwaniec-Kowalski Theorem 11.13; Halberstam-Richert Theorem 8.3. -/
theorem jr_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 2 ≤ D → D ≤ z ^ 4 →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K → 0 ≤ s.totalMass →
      s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ))))
        - ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d| ≤ s.siftedSum := by
  obtain ⟨C, hC, hmain⟩ := jr_mainSum_lower K hK
  refine ⟨C, hC, fun s z D hz hzD hDz hP hK' hX => ?_⟩
  have hz2 : z ≤ z ^ 2 := by nlinarith
  have hzD' : z ≤ D := hz2.trans hzD
  have h1 := siftedSum_ge_of_lower s _ (rosser_lower_le D)
  have h2 := hmain s z D hz hzD hDz hP hK'
  have h3 := errSum_rosser_le s z D hzD' (one_lt_of_two_le hz hzD') hP false
  have h4 : s.totalMass * ((∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ)))) ≤
      s.totalMass * s.mainSum (rosserWeight D false) :=
    mul_le_mul_of_nonneg_left h2 hX
  linarith

/-! ### Vacuity -/

/-- The trivial sieve problem: empty support, `P = 1`, `g = ζ`. -/
noncomputable def trivialSieve : BoundingSieve where
  support := ∅
  prodPrimes := 1
  prodPrimes_squarefree := squarefree_one
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  nu_mult := isMultiplicative_zeta.natCast
  nu_pos_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one
  nu_lt_one_of_prime := fun _p hp h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one

/-- Vacuity of `LinearDensity`: it holds for the trivial sieve with `K = 0`, and the
hypotheses of `jr_upper` hold at `z = D = 2`. -/
example : LinearDensity trivialSieve 0 ∧
    (∀ p ∈ trivialSieve.prodPrimes.primeFactors, (p : ℝ) < 2) := by
  refine ⟨fun w w' hw hww' => ?_, by simp [trivialSieve]⟩
  have hlw : 0 < log w := log_pos (by linarith)
  have hl : log w ≤ log w' := log_le_log (by linarith) hww'.le
  simp only [trivialSieve, Nat.primeFactors_one, Finset.filter_empty, Finset.prod_empty,
    zero_div, add_zero, mul_one]
  rw [le_div_iff₀ hlw]; linarith

end LeanLab.AlmostPrimeSums.Decomp1527b
