/- AI wrote the Lean code for CODEX task236.
Finite prime count reduction for journal Lemma 14 pp. 1237 to 1239.
Goldbach is open. -/
import LeanLab.BS2022GRH.SliceModel236
import LeanLab.BS2022GRH.PaperInputs148
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The larger triple family in journal display 30 p. 1237. -/
def relaxedTriples (n : ℕ) (ε₁ : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  ((range K ×ˢ range K) ×ˢ range K).filter (fun t =>
    t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.Prime ∧
    U7153.zz n ≤ t.1.1 ∧ (t.1.1 : ℝ) < U7153.yy n ∧
    U7153.yy n ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧
    (t.1.1 : ℝ) * t.1.2 * t.2 < (1 + ε₁) * n)

/-- The pair indices after eliminating p3, journal p. 1237. -/
def pairRange (n : ℕ) (ε₁ : ℝ) : Finset (ℕ × ℕ) :=
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  (range K ×ˢ range K).filter (fun q =>
    q.1.Prime ∧ q.2.Prime ∧ U7153.zz n ≤ q.1 ∧
    (q.1 : ℝ) < U7153.yy n ∧ U7153.yy n ≤ q.2 ∧
    (q.1 : ℝ) * q.2 ^ 2 < (1 + ε₁) * n)

/-- The disjoint slice mass is at most the relaxed triple count, p. 1237 display 30. -/
theorem mass_le_relaxed (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    mass n ε₁ ≤ ((relaxedTriples n ε₁).card : ℝ) := by
  rw [mass_eq_card_union n ε₁ hn hε]
  apply Nat.cast_le.mpr
  apply card_le_card
  intro t ht
  obtain ⟨j, _, ht⟩ := mem_biUnion.mp ht
  obtain ⟨htr, hp1, hp2, hp3, hz, hy, hyp2, hp23, _⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨htr, hp1, hp2, hp3, hz, hy, hyp2, hp23, slice_product_lt hε ht⟩

/-- A relaxed triple projects to a pair in the stated range, p. 1237. -/
theorem pair_mem_of_triple {n : ℕ} {ε₁ : ℝ} {t : (ℕ × ℕ) × ℕ}
    (ht : t ∈ relaxedTriples n ε₁) : t.1 ∈ pairRange n ε₁ := by
  obtain ⟨htr, hp1, hp2, hp3, hz, hy, hyp2, hp23, hprod⟩ := mem_filter.mp ht
  apply mem_filter.mpr
  refine ⟨(mem_product.mp htr).1, hp1, hp2, hz, hy, hyp2, ?_⟩
  have hp23R : (t.1.2 : ℝ) ≤ t.2 := by exact_mod_cast hp23
  calc
    (t.1.1 : ℝ) * t.1.2 ^ 2 ≤ (t.1.1 : ℝ) * t.1.2 * t.2 := by
      nlinarith [mul_le_mul_of_nonneg_left hp23R (mul_nonneg (Nat.cast_nonneg t.1.1) (Nat.cast_nonneg t.1.2))]
    _ < _ := hprod

/-- For fixed p1 and p2 the possible p3 are counted by pi, journal p. 1237.
The prime counting function uses a non-strict upper endpoint, which is an upper bound. -/
theorem triple_fiber_le_pi (n : ℕ) (ε₁ : ℝ) (q : ℕ × ℕ) (hq : q ∈ pairRange n ε₁) :
    (((relaxedTriples n ε₁).filter (fun t => t.1 = q)).card : ℝ) ≤
      PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) := by
  let T := (relaxedTriples n ε₁).filter (fun t => t.1 = q)
  have hq1 : q.1.Prime := (mem_filter.mp hq).2.1
  have hq2 : q.2.Prime := (mem_filter.mp hq).2.2.1
  have hq0 : (0 : ℝ) < (q.1 : ℝ) * q.2 := by
    have h1 : (0 : ℝ) < q.1 := by exact_mod_cast hq1.pos
    have h2 : (0 : ℝ) < q.2 := by exact_mod_cast hq2.pos
    positivity
  have hinj : Set.InjOn (fun t : (ℕ × ℕ) × ℕ => t.2) T := by
    intro t ht u hu heq
    have htq := (mem_filter.mp ht).2
    have huq := (mem_filter.mp hu).2
    exact Prod.ext (htq.trans huq.symm) heq
  have hsub : T.image (fun t => t.2) ⊆
      (range (⌊(1 + ε₁) * n / ((q.1 : ℝ) * q.2)⌋₊ + 1)).filter (fun p => p.Prime) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
    obtain ⟨htt, htq⟩ := mem_filter.mp ht
    obtain ⟨_, _, _, hp3, _, _, _, _, hprod⟩ := mem_filter.mp htt
    have hlt : (t.2 : ℝ) < (1 + ε₁) * n / ((q.1 : ℝ) * q.2) := by
      rw [lt_div_iff₀ hq0]
      rw [htq] at hprod
      nlinarith
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hlt.le)), hp3⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  dsimp only [T] at hc
  unfold PaperInputs148.primeCount
  exact_mod_cast hc

/-- The complete first finite reduction of Lemma 14, journal pp. 1237 and 1238. -/
theorem mass_le_pi_sum (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    mass n ε₁ ≤ ∑ q ∈ pairRange n ε₁,
      PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) := by
  have hc := card_eq_sum_card_fiberwise
    (s := relaxedTriples n ε₁) (t := pairRange n ε₁) (f := fun t => t.1)
    (fun t ht => pair_mem_of_triple ht)
  calc
    mass n ε₁ ≤ ((relaxedTriples n ε₁).card : ℝ) := mass_le_relaxed n ε₁ hn hε
    _ = ∑ q ∈ pairRange n ε₁,
        (((relaxedTriples n ε₁).filter (fun t => t.1 = q)).card : ℝ) := by exact_mod_cast hc
    _ ≤ _ := sum_le_sum (fun q hq => triple_fiber_le_pi n ε₁ q hq)

/-- The reciprocal double sum in Lemma 14, journal p. 1238. -/
def pairWeightSum (n : ℕ) (ε₁ : ℝ) : ℝ :=
  ∑ q ∈ pairRange n ε₁,
    (1 : ℝ) / ((q.1 : ℝ) * q.2 * log ((n : ℝ) / ((q.1 : ℝ) * q.2)))

/-- The Schoenfeld count reduces mass to the explicit reciprocal double sum, p. 1238.
CONDITIONAL ON the uniform prime count envelope. -/
theorem mass_le_pairWeight (n : ℕ) (ε₁ K : ℝ) (hn : 0 < n) (hε : 0 < ε₁)
    (hpi : ∀ q ∈ pairRange n ε₁,
      PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) ≤
        K / ((q.1 : ℝ) * q.2 * log ((n : ℝ) / ((q.1 : ℝ) * q.2)))) :
    mass n ε₁ ≤ K * pairWeightSum n ε₁ := by
  calc
    mass n ε₁ ≤ _ := mass_le_pi_sum n ε₁ hn hε
    _ ≤ ∑ q ∈ pairRange n ε₁,
        K / ((q.1 : ℝ) * q.2 * log ((n : ℝ) / ((q.1 : ℝ) * q.2))) := sum_le_sum hpi
    _ = K * pairWeightSum n ε₁ := by
      unfold pairWeightSum
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring

/-- The partial summation primitive for the inner prime sum, journal p. 1238. -/
def kernelPrimitive (N p t : ℝ) : ℝ :=
  (log (log t) - log (log N - log p - log t)) / (log N - log p)

/-- The exact derivative behind the first partial summation, journal p. 1238. -/
theorem kernelPrimitive_hasDeriv (N p t : ℝ) (ht : 1 < t)
    (hgap : 0 < log N - log p - log t) :
    HasDerivAt (kernelPrimitive N p)
      (1 / (t * log t * (log N - log p - log t))) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht
  have hA : log N - log p ≠ 0 := by linarith
  have hd1 := (hasDerivAt_log ht0.ne').log hl.ne'
  have hd2 := ((hasDerivAt_const t (log N - log p)).sub
    (hasDerivAt_log ht0.ne')).log hgap.ne'
  convert (hd1.sub hd2).div_const (log N - log p) using 1
  · rfl
  · dsimp only [Pi.sub_apply]
    field_simp [ht0.ne', hl.ne', hgap.ne', hA]
    <;> ring

/-- The unrelaxed inner integral, journal p. 1238. -/
def H (N u : ℝ) : ℝ :=
  (log (log N - log u - log (N ^ (1 / 3 : ℝ))) -
    log (log (N ^ (1 / 3 : ℝ)))) / (log N - log u)

/-- The outer partial summation weight vanishes at y, journal p. 1238. -/
theorem H_at_y (N : ℝ) (hN : 1 < N) : H N (N ^ (1 / 3 : ℝ)) = 0 := by
  have hN0 : 0 < N := by linarith
  unfold H
  rw [log_rpow hN0]
  have heq : log N - (1 / 3 : ℝ) * log N - (1 / 3 : ℝ) * log N =
      (1 / 3 : ℝ) * log N := by ring
  rw [heq, sub_self, zero_div]

/-- The substitution u equals N to beta in the outer weight, journal pp. 1238 and 1239. -/
theorem H_rpow (N β : ℝ) (hN : 1 < N) (hβ : β < 2 / 3) :
    H N (N ^ β) = log (2 - 3 * β) / ((1 - β) * log N) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hg : 0 < (2 / 3 - β) * log N := mul_pos (by linarith) hL
  have h3 : 0 < (1 / 3 : ℝ) * log N := by positivity
  unfold H
  rw [log_rpow hN0, log_rpow hN0]
  have heq : log N - β * log N - (1 / 3 : ℝ) * log N = (2 / 3 - β) * log N := by ring
  rw [heq, ← log_div hg.ne' h3.ne']
  have hquot : ((2 / 3 - β) * log N) / ((1 / 3) * log N) = 2 - 3 * β := by field_simp
  rw [hquot]
  congr 1
  ring

end
end LeanLab.BS2022GRH.SliceMass236

#print axioms LeanLab.BS2022GRH.SliceMass236.mass_le_relaxed
#print axioms LeanLab.BS2022GRH.SliceMass236.pair_mem_of_triple
#print axioms LeanLab.BS2022GRH.SliceMass236.triple_fiber_le_pi
#print axioms LeanLab.BS2022GRH.SliceMass236.mass_le_pi_sum
#print axioms LeanLab.BS2022GRH.SliceMass236.mass_le_pairWeight
#print axioms LeanLab.BS2022GRH.SliceMass236.kernelPrimitive_hasDeriv
#print axioms LeanLab.BS2022GRH.SliceMass236.H_at_y
#print axioms LeanLab.BS2022GRH.SliceMass236.H_rpow
