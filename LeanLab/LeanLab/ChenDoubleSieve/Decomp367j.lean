import LeanLab.ChenDoubleSieve.Decomp367i

/-!
Regroup the actual pair discrepancy by its full progression modulus.
Source: https://arxiv.org/pdf/0705.1652, page 39 error display and equation 10.5.
The comparison is elementary. The single modulus mean value input is not proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348

/-- Actual pairs together with their residual discrepancy moduli. -/
def pairTriples5 (B : ℝ) (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  (lowerPairs5 N).sigma (pairModuli5 B N)

/-- The full progression modulus attached to an actual pair and residual modulus. -/
def tripleModulus5 (t : Σ _ : ℕ × ℕ, ℕ) : ℕ := t.1.1 * t.1.2 * t.2

/-- Each triple maps into the original single modulus discrepancy domain. -/
theorem tripleModulus5_mem {B : ℝ} {N : ℕ} (hN : 2 ≤ N)
    {t : Σ _ : ℕ × ℕ, ℕ} (ht : t ∈ pairTriples5 B N) :
    tripleModulus5 t ∈ Task363.remainderModuli B N := by
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp ht
  exact pairModuli5_product_mem hN hp hq

/-- A full modulus has at most 144 preimages among the actual discrepancy triples. -/
theorem tripleModulus5_fiber_card {B : ℝ} {N d : ℕ} (hN : 2 ≤ N)
    (hd : 0 < d) (hdN : d ≤ N) :
    ((pairTriples5 B N).filter (fun t => tripleModulus5 t = d)).card ≤ 144 := by
  apply le_trans _ (candidatePairs5_card hN hd hdN)
  apply card_le_card_of_injOn (fun t : Σ _ : ℕ × ℕ, ℕ => t.1)
  · intro t ht
    obtain ⟨htT, htd⟩ := mem_filter.mp ht
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp htT
    rw [← htd]
    exact pair_mem_candidatePairs5 hp t.2
  · intro t ht u hu heq
    obtain ⟨htT, htd⟩ := mem_filter.mp ht
    obtain ⟨huT, hud⟩ := mem_filter.mp hu
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp htT
    rcases t with ⟨p, q⟩
    rcases u with ⟨r, s⟩
    dsimp only at heq
    subst r
    have hpfull : p ∈ fullPairs5 N := by
      rw [lowerPairs5_eq_filter] at hp
      exact (mem_filter.mp hp).1
    have hpos : 0 < p.1 * p.2 := (fullPairs5_product hpfull).1
    have he : p.1 * p.2 * q = p.1 * p.2 * s := htd.trans hud.symm
    have hqs : q = s := Nat.eq_of_mul_eq_mul_left hpos he
    subst s
    rfl

/-- The absolute pair discrepancy is bounded by 144 times the single modulus discrepancy.
Only the explicit finite level bound is needed beyond N at least two. -/
theorem rawRemainder5_le_single {B : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hQ : Task363.sieveLevel B N ≤ N) :
    rawRemainder5 B N ≤ 144 * Task363.rawRemainder B N := by
  let T := pairTriples5 B N
  let S := Task363.remainderModuli B N
  let g : ℕ → ℝ := fun d =>
    |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) - Wu04.li N / (d.totient : ℝ)|
  have hmap : ∀ t ∈ T, tripleModulus5 t ∈ S := fun _ ht => tripleModulus5_mem hN ht
  have he : rawRemainder5 B N = ∑ t ∈ T, g (tripleModulus5 t) := by
    simp only [T, pairTriples5, Finset.sum_sigma, g, tripleModulus5, rawRemainder5]
  rw [he]
  have hgroup := Finset.sum_fiberwise_of_maps_to hmap (fun t => g (tripleModulus5 t))
  rw [← hgroup]
  calc
    _ ≤ ∑ d ∈ S, (144 : ℝ) * g d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdI, _⟩ := mem_filter.mp hd
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hdI
      have hdN : d ≤ N := by
        have he := (Nat.le_floor_iff' (by omega : d ≠ 0)).1 hdQ
        exact_mod_cast he.trans hQ
      have hc := tripleModulus5_fiber_card (B := B) hN hd1 hdN
      have hcR : (((T.filter (fun t => tripleModulus5 t = d)).card : ℕ) : ℝ) ≤ 144 := by
        exact_mod_cast hc
      calc
        _ = ∑ _t ∈ T.filter (fun t => tripleModulus5 t = d), g d := by
          apply sum_congr rfl
          intro t ht
          rw [(mem_filter.mp ht).2]
        _ = ((T.filter (fun t => tripleModulus5 t = d)).card : ℝ) * g d := by simp
        _ ≤ 144 * g d := mul_le_mul_of_nonneg_right hcR (abs_nonneg _)
    _ = 144 * Task363.rawRemainder B N := by
      simp only [S, Task363.rawRemainder, g, mul_sum]

end LeanLab.ChenDoubleSieve.Task367
