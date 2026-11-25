import LeanLab.ChenDoubleSieve.Decomp349bSwitching
import LeanLab.ChenDoubleSieve.Decomp349bCoprimeRemoval

/-!
Split of the LEAF `leaf_switch_exceptions` of Decomp349bSwitching, Wu 2004 page 40.
Source: https://arxiv.org/pdf/0705.1652.
For one pair the exceptional elements number at most 2 plus log N over log 2 plus
N over p squared q: at most one equals p q, the multiples of p squared q are counted
directly, and a common prime r with N forces p' equal r. The sum of these bounds over
the switched pairs is one new LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- The multiples of d in the prime sequence number at most N over d plus 1. -/
theorem swe_multiples_le (N d : ℕ) (hd : 0 < d) :
    (((primeSequence N).filter (fun a => d ∣ a)).card : ℝ) ≤ (N : ℝ) / d + 1 := by
  have hsub : (primeSequence N).filter (fun a => d ∣ a) ⊆
      (Finset.range (N + 1)).filter (fun a => d ∣ a) := by
    intro a ha
    obtain ⟨hA, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hda⟩
  have hmap : ∀ a ∈ (Finset.range (N + 1)).filter (fun a => d ∣ a), a / d ∈ Finset.range (N / d + 1) := by
    intro a ha
    have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  have hinj : Set.InjOn (fun a => a / d) ((Finset.range (N + 1)).filter (fun a => d ∣ a) : Set ℕ) := by
    intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    simp only at hab
    rw [← Nat.div_mul_cancel hda, ← Nat.div_mul_cancel hdb, hab]
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_le_card_of_injOn _ hmap hinj)
  rw [Finset.card_range] at h1
  have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have h3 : (((primeSequence N).filter (fun a => d ∣ a)).card : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  linarith

/-- Elements of the prime sequence sharing a prime with N are N minus a prime factor of N. -/
theorem swe_noncoprime_le (N : ℕ) (hN : 1 ≤ N) :
    (((primeSequence N).filter (fun a => ¬ Nat.Coprime a N)).card : ℝ) ≤ log N / log 2 := by
  have hsub : (primeSequence N).filter (fun a => ¬ Nat.Coprime a N) ⊆
      N.primeFactors.image (fun r => N - r) := by
    intro a ha
    obtain ⟨hA, hnc⟩ := Finset.mem_filter.mp ha
    obtain ⟨p', hp'm, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hp'r, hp'⟩ := Finset.mem_filter.mp hp'm
    have hp'N : p' ≤ N := by have := Finset.mem_range.mp hp'r; omega
    obtain ⟨r, hr, hra, hrN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hrp : r ∣ p' := by
      have := Nat.dvd_sub hrN hra
      rwa [Nat.sub_sub_self hp'N] at this
    have hreq : r = p' := (Nat.prime_dvd_prime_iff_eq hr hp').mp hrp
    exact Finset.mem_image.mpr ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hrN, by omega⟩, by rw [hreq]⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 := bc_card_primeFactors_le N hN
  have h3 : (((primeSequence N).filter (fun a => ¬ Nat.Coprime a N)).card : ℝ) ≤
      (N.primeFactors.card : ℝ) := by exact_mod_cast h1
  linarith

/-- Wu 2004 page 40: the exceptional count of one pair is at most 2 plus log N over
log 2 plus N over p squared q. -/
theorem swe_pair_le (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hN : 1 ≤ N) :
    (((primeSequence N).filter (fun a => p * q ∣ a ∧
      (a = p * q ∨ p * (p * q) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℝ) ≤
      2 + log N / log 2 + (N : ℝ) / ((p : ℝ) * (p * q)) := by
  set A := primeSequence N
  have hsub : A.filter (fun a => p * q ∣ a ∧ (a = p * q ∨ p * (p * q) ∣ a ∨ ¬ Nat.Coprime a N)) ⊆
      ({p * q} ∪ A.filter (fun a => p * (p * q) ∣ a)) ∪ A.filter (fun a => ¬ Nat.Coprime a N) := by
    intro a ha
    obtain ⟨hA, _, h⟩ := Finset.mem_filter.mp ha
    rcases h with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, h⟩)
  have hd : 0 < p * (p * q) := Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hq.pos)
  have hm := swe_multiples_le N (p * (p * q)) hd
  have hc := swe_noncoprime_le N hN
  have hu := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  rw [Finset.card_singleton] at hu
  have hu' : (((A.filter (fun a => p * q ∣ a ∧
      (a = p * q ∨ p * (p * q) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℕ) : ℝ) ≤
      1 + ((A.filter (fun a => p * (p * q) ∣ a)).card : ℝ) +
        ((A.filter (fun a => ¬ Nat.Coprime a N)).card : ℝ) := by exact_mod_cast hu
  push_cast at hm
  linarith

/-- LEAF: Wu 2004 page 40, the exceptions of Chen's switching summed: over the switched
pairs the per pair bounds 2 plus log N over log 2 plus N over p squared q sum to
o of Theta N. There are at most N to 5/6 pairs, and the sum of N over p squared q is
O of N to 1 minus kappa2 times log N squared, using the lower bound C_N at least the
twin prime constant. Class MEDIUM. -/
theorem leaf_switch_exceptions_sum :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        ∑ q ∈ switchedPairs N i,
          (2 + log N / log 2 + (N : ℝ) / ((q.1 : ℝ) * (q.1 * q.2))) ≤ η * Θ N := by
  sorry

/-- `leaf_switch_exceptions`, exactly as stated in Decomp349bSwitching, from the per pair
bound `swe_pair_le` and the summed LEAF. CONDITIONAL ON leaf_switch_exceptions_sum. -/
theorem leaf_switch_exceptions_proved :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        ∑ q ∈ switchedPairs N i, (((primeSequence N).filter (fun a => q.1 * q.2 ∣ a ∧
          (a = q.1 * q.2 ∨ q.1 * (q.1 * q.2) ∣ a ∨ ¬ Nat.Coprime a N))).card : ℝ) ≤
          η * Θ N := by
  intro η hη
  obtain ⟨N0, hN0⟩ := leaf_switch_exceptions_sum η hη
  refine ⟨max N0 1, fun N hEven hN i hi => le_trans ?_ (hN0 N hEven (le_of_max_le_left hN) i hi)⟩
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hp, hq', _, _⟩ := sw_mem hq
  exact_mod_cast swe_pair_le N q.1 q.2 hp hq' (le_of_max_le_right hN)

end LeanLab.ChenDoubleSieve.Task349

