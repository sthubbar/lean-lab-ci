import LeanLab.ChenDoubleSieve.Decomp347d

/-!
The second exact Buchstab substitution on page 36 of Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 36 second display.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- Split a prime sum at an intermediate half open cutoff.
Source: page 36 second display, finite interval bookkeeping. -/
theorem prime_sum_split (N : ℕ) (f : ℕ → ℕ) {w v z : ℝ}
    (hwv : w ≤ v) (hvz : v ≤ z) :
    (∑ p ∈ PS N w z, f p) = (∑ p ∈ PS N w v, f p) + ∑ p ∈ PS N v z, f p := by
  have hset : PS N w z = PS N w v ∪ PS N v z := by
    ext p
    simp only [mem_union, Wu41.mem_PS]
    constructor
    · rintro ⟨hp, hwp, hpz, hpc⟩
      by_cases hpv : (p : ℝ) < v
      · exact Or.inl ⟨hp, hwp, hpv, hpc⟩
      · exact Or.inr ⟨hp, le_of_not_gt hpv, hpz, hpc⟩
    · rintro (⟨hp, hwp, hpv, hpc⟩ | ⟨hp, hvp, hpz, hpc⟩)
      · exact ⟨hp, hwp, hpv.trans_le hvz, hpc⟩
      · exact ⟨hp, hwv.trans hvp, hpz, hpc⟩
  have hdis : Disjoint (PS N w v) (PS N v z) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact not_lt_of_ge (Wu41.mem_PS.mp hq).2.1 (Wu41.mem_PS.mp hp).2.2.1
  rw [hset, sum_union hdis]

/-- Lower the common sieve level of the upper prime band.
Source: page 36 second display before splitting its two positive pair domains. -/
theorem upper_prime_band_lowering (A : Finset ℕ) (N : ℕ) {w v z : ℝ}
    (hwv : w ≤ v) :
    Wu08.S₁ A N v z +
      (∑ p ∈ PS N v z, ∑ q ∈ PS N w v, S A (p * q) N q) =
      ∑ p ∈ PS N v z, S A p N w := by
  symm
  unfold Wu08.S₁
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  apply buchstab_divisor A p N hwv
  intro q hq
  obtain ⟨hpp, hvp, _, _⟩ := Wu41.mem_PS.mp hp
  obtain ⟨hqp, _, hqv, _⟩ := Wu41.mem_PS.mp hq
  apply (hqp.coprime_iff_not_dvd).mpr
  intro hd
  have heq := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp hd
  subst q
  exact not_lt_of_ge hvp hqv

/-- Reindex the separated prime bands into the ascending crossing pair domain.
Source: page 36 second display, the pair domains before splitting at rho. -/
theorem crossing_pairs_reindex (N : ℕ) (w v z : ℝ) (hz : z ≤ N)
    (f : ℕ → ℕ → ℕ) :
    (∑ p ∈ PS N v z, ∑ q ∈ PS N w v, f q p) =
      ∑ t ∈ Wu08Sum.P2 N (fun p q => w ≤ p ∧ (p : ℝ) < v ∧ v ≤ q ∧ (q : ℝ) < z),
        f t.1 t.2 := by
  symm
  apply Finset.sum_finset_product_right
  intro t
  simp only [Wu08Sum.P2, mem_filter, mem_product]
  constructor
  · rintro ⟨_, hp, hq, hpc, hqc, hwp, hpv, hvq, hqz⟩
    exact ⟨Wu41.mem_PS.mpr ⟨hq, hvq, hqz, hqc⟩,
      Wu41.mem_PS.mpr ⟨hp, hwp, hpv, hpc⟩⟩
  · rintro ⟨hq, hp⟩
    obtain ⟨hqp, hvq, hqz, hqc⟩ := Wu41.mem_PS.mp hq
    obtain ⟨hpp, hwp, hpv, hpc⟩ := Wu41.mem_PS.mp hp
    have hqN : t.2 < N := by exact_mod_cast hqz.trans_le hz
    have hpqN : t.1 < t.2 := by exact_mod_cast hpv.trans_le hvq
    exact ⟨⟨mem_range.mpr (hpqN.trans hqN), mem_range.mpr hqN⟩,
      hpp, hqp, hpc, hqc, hwp, hpv, hvq, hqz⟩

/-- The exact S1 substitution with the two crossing pair bands kept together.
Source: page 36 second display. Splitting the crossing sum at rho gives the two
printed pair terms. No asymptotic estimate is used. -/
theorem S1_buchstab_expansion (A : Finset ℕ) (N : ℕ) {w v z : ℝ}
    (hwv : w ≤ v) (hvz : v ≤ z) (hz : z ≤ N) :
    (Wu08.S₁ A N v z : ℝ) =
      (∑ p ∈ PS N w z, S A p N w : ℕ) -
      (∑ p ∈ PS N w v, S A p N w : ℕ) -
      (∑ t ∈ Wu08Sum.P2 N (fun p q => w ≤ p ∧ (p : ℝ) < v ∧ v ≤ q ∧ (q : ℝ) < z),
        S A (t.1 * t.2) N t.1 : ℕ) := by
  have hs := prime_sum_split N (fun p => S A p N w) hwv hvz
  have hb := upper_prime_band_lowering A N (z := z) hwv
  rw [crossing_pairs_reindex N w v z hz (fun p q => S A (q * p) N p)] at hb
  simp only [mul_comm] at hb
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  have hbR := congrArg (fun n : ℕ => (n : ℝ)) hb
  push_cast at hsR hbR ⊢
  linarith only [hsR, hbR]

end LeanLab.ChenDoubleSieve.Task347
