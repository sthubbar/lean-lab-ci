import LeanLab.ChenDoubleSieve.Decomp315a
import LeanLab.ChenDoubleSieve.Feed1122_S120_rho_compensation

/-!
SPLIT of `Task315.first_half`, Wu 2004 equation 9.7, into equation 9.6 and the
Buchstab step on page 36 that gives Delta at least Upsilon 5 plus Delta one.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 36 and 37.
This file imports Decomp315a because the parent's statement uses `deltaOne`, defined
there; the original is not edited, keeping imports acyclic.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122FirstHalf
open Task275
open Wu41 (S)
open Wu08Sum (P2)

/-- The third sum in Delta of Wu 2004 page 36, display after 9.6: pairs with
N to the kappa one at most p one below N to the kappa two at most p two below N to the rho,
sifted below p one, at Section 10's rho equal one quarter, which satisfies 3 kappa one plus rho
equal one half by `parameters_admissible`. -/
def pairRho (N : ℕ) : ℝ :=
  let A := primeSequence N
  let y := fun k : ℝ => (N : ℝ) ^ k
  (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y kappa2 ∧
      y kappa2 ≤ q ∧ (q : ℝ) < y (1 / 4)), S A (q.1 * q.2) N q.1 : ℕ)

/-- LEAF: Wu 2004 page 36 equation 9.6, which is 9.5, Lemma 9.1 at kappa two and sigma two,
after the Buchstab and switching rewrites of pages 35 and 36, with Delta written as minus the
first and third triple sums plus `pairRho`, and the nonnegative Upsilon 6, 11, 12 dropped;
the error O of N to the one minus kappa two is absorbed into C times N to the eleven twelfths.
The first Delta sum sifts below p one, so its paper modulus N p one equals N here. Class HARD. -/
theorem leaf_eq96 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 - 2 * sieveTerms N 7 - sieveTerms N 9 -
        tripleTerms N 0 - tripleTerms N 2 + pairRho N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, M, hM⟩ := Feed1122S120.crossing_compensation_rho
  obtain ⟨B, hB⟩ := Task347.baseline_bound
  refine ⟨C + 11, by linarith, max M (max B 1), fun N hEven hN => ?_⟩
  have hc := hM N hEven (le_trans (le_max_left _ _) hN)
  have hb := hB N hEven (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have hid := Task347.first_half_transport_identity N
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have eρ : pairRho N =
      ((∑ q ∈ P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧
          (p : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ q ∧
          (q : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ)),
        S (primeSequence N) (q.1 * q.2) N q.1 : ℕ) : ℝ) := rfl
  dsimp only [deltaOne, Task347.transportReserve] at hid
  rw [eρ]
  linarith

/-- The exact Buchstab step behind `leaf_buchstab`, Wu 2004 page 36: on the Upsilon 5 domain,
sifting below kappa one equals sifting below p one plus the triple sum whose smallest prime r
lies between kappa one and p one. Finite identity, no distribution input. -/
theorem pair_buchstab_split (A : Finset ℕ) (N : ℕ) (K1 K2 Z : ℝ) :
    (∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
      S A (q.1 * q.2) N K1 : ℕ) =
    (∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
      S A (q.1 * q.2) N q.1 : ℕ) +
    (∑ q ∈ primeTriples N (fun p q r => K1 ≤ p ∧ p < q ∧ (q : ℝ) < K2 ∧ K2 ≤ r ∧
      (r : ℝ) < Z / q), S A (q.1 * q.2.1 * q.2.2) N q.1 : ℕ) := by
  have step : ∀ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
      S A (q.1 * q.2) N K1 = S A (q.1 * q.2) N q.1 +
        ∑ r ∈ Wu41.PS N K1 q.1, S A (q.1 * q.2 * r) N r := by
    intro q hq
    simp only [P2, mem_filter, mem_product, mem_range] at hq
    obtain ⟨_, hp, hqq, _, _, h1, h2, h3, _⟩ := hq
    apply buchstab_divisor A _ N h1
    intro r hr
    obtain ⟨hrp, _, hrlt, _⟩ := Wu41.mem_PS.mp hr
    have hrq : (r : ℝ) < q.2 := hrlt.trans (h2.trans_le h3)
    have h1' : r ≠ q.1 := by
      intro h; rw [h] at hrlt; exact lt_irrefl _ hrlt
    have h2' : r ≠ q.2 := by
      intro h; rw [h] at hrq; exact lt_irrefl _ hrq
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hrp hp).mpr h1')
      ((Nat.coprime_primes hrp hqq).mpr h2')
  rw [sum_congr rfl step, sum_add_distrib]
  congr 1
  rw [sum_sigma']
  refine sum_nbij' (fun t => (t.2, t.1.1, t.1.2)) (fun t => ⟨(t.2.1, t.2.2), t.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨p, q⟩, r⟩ ht
    simp only [mem_sigma, P2, mem_filter, mem_product, mem_range] at ht
    obtain ⟨⟨⟨hpN, hqN⟩, hp, hq, hpc, hqc, h1, h2, h3, h4⟩, hr⟩ := ht
    obtain ⟨hrp, hr1, hrlt, hrc⟩ := Wu41.mem_PS.mp hr
    have hpq : p < q := by exact_mod_cast h2.trans_le h3
    have hrp' : r < p := by exact_mod_cast hrlt
    simp only [primeTriples, mem_filter, mem_product, mem_range]
    exact ⟨⟨hrp'.trans hpN, hpN, hqN⟩, hrp, hp, hq, hrc, hpc, hqc, hr1, hrp', h2, h3, h4⟩
  · rintro ⟨r, p, q⟩ ht
    simp only [primeTriples, mem_filter, mem_product, mem_range] at ht
    obtain ⟨⟨hrN, hpN, hqN⟩, hrp, hp, hq, hrc, hpc, hqc, hr1, hrp', h2, h3, h4⟩ := ht
    have hrpR : (r : ℝ) < p := by exact_mod_cast hrp'
    simp only [mem_sigma, P2, mem_filter, mem_product, mem_range]
    exact ⟨⟨⟨hpN, hqN⟩, hp, hq, hpc, hqc, hr1.trans hrpR.le, h2, h3, h4⟩,
      Wu41.mem_PS.mpr ⟨hrp, hr1, hrpR, hrc⟩⟩
  · rintro ⟨⟨p, q⟩, r⟩ _; rfl
  · rintro ⟨r, p, q⟩ _; rfl
  · rintro ⟨⟨p, q⟩, r⟩ _
    simp only
    congr 1
    ring

/-- LEAF: Wu 2004 page 36, the Buchstab identity step after 9.6: since 3 kappa one plus rho is
one half, N to the rho is at least N to the half minus two kappa one over p one, so
`pairRho` is at least Upsilon 5 minus the second triple sum of Delta one. Class MEDIUM. -/
theorem leaf_buchstab : ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 5 - tripleTerms N 1 ≤ pairRho N := by
  refine ⟨1, fun N _ hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set A := primeSequence N with hA
  set K1 : ℝ := (N : ℝ) ^ kappa1 with hK1
  set K2 : ℝ := (N : ℝ) ^ kappa2 with hK2
  set Z : ℝ := (N : ℝ) ^ (1 / 2 - 2 * kappa1) with hZ
  have e5 : sieveTerms N 5 =
      ((∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
        S A (q.1 * q.2) N K1 : ℕ) : ℝ) := rfl
  have e1 : tripleTerms N 1 =
      ((∑ q ∈ primeTriples N (fun p q r => K1 ≤ p ∧ p < q ∧ (q : ℝ) < K2 ∧ K2 ≤ r ∧
        (r : ℝ) < Z / q), S A (q.1 * q.2.1 * q.2.2) N q.1 : ℕ) : ℝ) := rfl
  have eρ : pairRho N =
      ((∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧
        (q : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ)), S A (q.1 * q.2) N q.1 : ℕ) : ℝ) := rfl
  have hZK : Z / K1 = (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hZ, hK1, ← Real.rpow_sub hNpos]
    norm_num [kappa1]
  have hK1pos : 0 < K1 := Real.rpow_pos_of_pos hNpos _
  have hsub : (∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
        S A (q.1 * q.2) N q.1 : ℕ) ≤
      (∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧
        (q : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ)), S A (q.1 * q.2) N q.1 : ℕ) := by
    apply sum_le_sum_of_subset
    intro q hq
    simp only [P2, mem_filter, mem_product, mem_range] at hq ⊢
    obtain ⟨hr, hp, hqq, hpc, hqc, h1, h2, h3, h4⟩ := hq
    refine ⟨hr, hp, hqq, hpc, hqc, h1, h2, h3, h4.trans_le ?_⟩
    rw [← hZK]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) hK1pos h1
  have hsplit := pair_buchstab_split A N K1 K2 Z
  rw [e5, e1, eρ, hsplit]
  have hsubR : ((∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧ (q : ℝ) < Z / p),
        S A (q.1 * q.2) N q.1 : ℕ) : ℝ) ≤
      ((∑ q ∈ P2 N (fun p q => K1 ≤ p ∧ (p : ℝ) < K2 ∧ K2 ≤ q ∧
        (q : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ)), S A (q.1 * q.2) N q.1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  push_cast at hsubR ⊢
  linarith

/-- The parent `first_half`, exactly as stated in Decomp315a, from the two leaves. -/
theorem first_half_of_leaves : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, M1, h1⟩ := leaf_eq96
  obtain ⟨M2, h2⟩ := leaf_buchstab
  refine ⟨C, hC, max M1 M2, fun N hN hle => ?_⟩
  have a := h1 N hN (le_trans (le_max_left _ _) hle)
  have b := h2 N hN (le_trans (le_max_right _ _) hle)
  dsimp only [deltaOne]
  linarith

end LeanLab.ChenDoubleSieve.Task315.Feed1122FirstHalf
