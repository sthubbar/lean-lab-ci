import LeanLab.ChenDoubleSieve.Decomp347c

/-!
Reindex the exact Buchstab expansion into Wu's ascending pair and triple domains.
Source: https://arxiv.org/pdf/0705.1652, page 36 first display.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- Descending nested prime sums equal the ascending pair sum.
Source: page 36 first display, exact reindexing of Upsilon 4. -/
theorem descending_pairs_reindex (N : ℕ) (w z : ℝ) (hz : z ≤ N)
    (f : ℕ → ℕ → ℕ) :
    (∑ p ∈ PS N w z, ∑ q ∈ PS N w p, f q p) =
      ∑ t ∈ Wu08Sum.P2 N (fun p q => w ≤ p ∧ p < q ∧ (q : ℝ) < z), f t.1 t.2 := by
  symm
  apply Finset.sum_finset_product_right
  intro t
  simp only [Wu08Sum.P2, mem_filter, mem_product]
  constructor
  · rintro ⟨_, hp, hq, hpc, hqc, hwp, hpq, hqz⟩
    have hpqR : (t.1 : ℝ) < t.2 := by exact_mod_cast hpq
    exact ⟨Wu41.mem_PS.mpr ⟨hq, hwp.trans hpqR.le, hqz, hqc⟩,
      Wu41.mem_PS.mpr ⟨hp, hwp, hpqR, hpc⟩⟩
  · rintro ⟨hq, hp⟩
    obtain ⟨hqp, _, hqz, hqc⟩ := Wu41.mem_PS.mp hq
    obtain ⟨hpp, hwp, hpq, hpc⟩ := Wu41.mem_PS.mp hp
    have hqN : t.2 < N := by exact_mod_cast hqz.trans_le hz
    have hpqN : t.1 < t.2 := by exact_mod_cast hpq
    exact ⟨⟨mem_range.mpr (hpqN.trans hqN), mem_range.mpr hqN⟩,
      hpp, hqp, hpc, hqc, hwp, hpqN, hqz⟩

/-- Descending nested prime sums equal the ascending triple sum.
Source: page 36 first display, exact reindexing of the first Delta one term. -/
theorem descending_triples_reindex (N : ℕ) (w z : ℝ) (hz : z ≤ N)
    (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ p ∈ PS N w z, ∑ q ∈ PS N w p, ∑ r ∈ PS N w q, f r q p) =
      ∑ t ∈ primeTriples N (fun p q r => w ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < z),
        f t.1 t.2.1 t.2.2 := by
  calc
    _ = ∑ t ∈ (PS N w z).sigma (fun p => (PS N w p).sigma (fun q => PS N w q)),
        f t.2.2 t.2.1 t.1 := by simp only [Finset.sum_sigma]
    _ = _ := by
      refine sum_bij (fun t _ => (t.2.2, t.2.1, t.1)) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro t ht
        obtain ⟨hp, hqr⟩ := mem_sigma.mp ht
        obtain ⟨hq, hr⟩ := mem_sigma.mp hqr
        obtain ⟨hpp, _, hpz, hpc⟩ := Wu41.mem_PS.mp hp
        obtain ⟨hqp, _, hqp_lt, hqc⟩ := Wu41.mem_PS.mp hq
        obtain ⟨hrp, hwr, hrq, hrc⟩ := Wu41.mem_PS.mp hr
        have hpN : t.1 < N := by exact_mod_cast hpz.trans_le hz
        have hqpN : t.2.1 < t.1 := by exact_mod_cast hqp_lt
        have hrqN : t.2.2 < t.2.1 := by exact_mod_cast hrq
        simp only [primeTriples, mem_filter, mem_product, mem_range]
        exact ⟨⟨hrqN.trans (hqpN.trans hpN), hqpN.trans hpN, hpN⟩,
          hrp, hqp, hpp, hrc, hqc, hpc, hwr, hrqN, hqpN, hpz⟩
      · rintro ⟨p, ⟨q, r⟩⟩ _ ⟨p', ⟨q', r'⟩⟩ _ he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        rfl
      · rintro ⟨p, q, r⟩ ht
        simp only [primeTriples, mem_filter, mem_product] at ht
        obtain ⟨_, hpp, hqp, hrp, hpc, hqc, hrc, hwp, hpq, hqr, hrz⟩ := ht
        have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
        have hqrR : (q : ℝ) < r := by exact_mod_cast hqr
        refine ⟨⟨r, ⟨q, p⟩⟩, ?_, rfl⟩
        apply mem_sigma.mpr
        refine ⟨Wu41.mem_PS.mpr ⟨hrp, (hwp.trans hpqR.le).trans hqrR.le, hrz, hrc⟩, ?_⟩
        exact mem_sigma.mpr ⟨Wu41.mem_PS.mpr ⟨hqp, hwp.trans hpqR.le, hqrR, hqc⟩,
          Wu41.mem_PS.mpr ⟨hpp, hwp, hpqR, hpc⟩⟩

/-- The exact first expansion in the proof of Lemma 9.2 in ascending coordinates.
Source: page 36 first display. No distribution estimate or square factor error is used. -/
theorem first_buchstab_expansion (A : Finset ℕ) (N : ℕ) {w z : ℝ}
    (hwz : w ≤ z) (hz : z ≤ N) :
    2 * (S A 1 N z : ℝ) = 2 * (S A 1 N w : ℝ) -
      (∑ p ∈ PS N w z, S A p N p : ℕ) -
      (∑ p ∈ PS N w z, S A p N w : ℕ) +
      (∑ q ∈ Wu08Sum.P2 N (fun p q => w ≤ p ∧ p < q ∧ (q : ℝ) < z),
        S A (q.1 * q.2) N w : ℕ) -
      (∑ q ∈ primeTriples N (fun p q r => w ≤ p ∧ p < q ∧ q < r ∧ (r : ℝ) < z),
        S A (q.1 * q.2.1 * q.2.2) N q.1 : ℕ) := by
  have h := three_step_buchstab A N hwz
  rw [descending_pairs_reindex N w z hz (fun p q => S A (q * p) N w)] at h
  rw [descending_triples_reindex N w z hz (fun p q r => S A (r * q * p) N p)] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- The first page 36 expansion at the exact sealed parameter values.
Source: page 36 first display and page 42 printed parameter choice. -/
theorem first_buchstab_printed (N : ℕ) (hN : 1 ≤ N) :
    2 * (S (primeSequence N) 1 N ((N : ℝ) ^ kappa2) : ℝ) =
      2 * sieveTerms N 0 - sieveTerms N 1 -
      (∑ p ∈ PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        S (primeSequence N) p N ((N : ℝ) ^ kappa1) : ℕ) +
      sieveTerms N 4 - tripleTerms N 0 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hwz : (N : ℝ) ^ kappa1 ≤ (N : ℝ) ^ kappa2 :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, kappa2])
  have hz : (N : ℝ) ^ kappa2 ≤ N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show kappa2 ≤ 1 by norm_num [kappa2])
  exact first_buchstab_expansion (primeSequence N) N hwz hz

end LeanLab.ChenDoubleSieve.Task347
