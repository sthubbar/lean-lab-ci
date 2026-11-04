/- AI wrote the Lean code for CODEX task236.
Finite slice model for journal Theorem 7. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148d
namespace LeanLab.BS2022GRH.DecompC164c
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- The main part of the sealed bracket, pp. 1235 and 1237, display 29. -/
def mainBracket (α ε C₁ X₂ ε₁ : ℝ) : ℝ :=
(1 + 0.06 * log X₂ / X₂ ^ (1 / 6 : ℝ)) *
      (2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁) * (1 + ε₁) *
      (log (X₂ ^ (1 / 3 : ℝ)) * (liPV (X₂ ^ (1 / 3 : ℝ))
        + X₂ ^ (1 / 6 : ℝ) * log (X₂ ^ (1 / 3 : ℝ)) / (8 * π)) / X₂ ^ (1 / 3 : ℝ)) *
      (LeanLab.ChenExplicit.BJS.cbar + 36 / log X₂ ^ 2 + (log (8 / 3) + 64 / log X₂ ^ 2) *
        (log √(1 + ε₁) / (log (X₂ ^ (1 / 3 : ℝ)) ^ 2 - log √(1 + ε₁) ^ 2) + 27 / log X₂ ^ 2))
/-- The bilinear error part, p. 1241 display 33. -/
def errorBracket (A X₂ ε₁ : ℝ) : ℝ :=
  invTw * (1 + ε₁) / (log (1 + ε₁) * log X₂ ^ (A - 4)) *
      (0.053 * mbarJ X₂ A (X₂ ^ (1 / 8 : ℝ)) * (1 + ε₁) ^ (-(1 / 2) : ℝ)
        + 0.08 * X₂ ^ (-(1 / 8) : ℝ) * log X₂ ^ (A + 1))
/-- Multiplicative slices of p1, pp. 1235 and 1236 display 26. -/
def w (n : ℕ) (ε₁ : ℝ) (j : ℕ) : ℝ := U7153.zz n * (1 + ε₁) ^ j
/-- The number of slices, p. 1236 display 26. -/
def slices (n : ℕ) (ε₁ : ℝ) : Finset ℕ :=
  range ⌈log (U7153.yy n / U7153.zz n) / log (1 + ε₁)⌉₊
/-- Triples in one relaxed slice, p. 1235 before display 26.
We count triples so no uniqueness of representations is assumed. -/
def slice (n : ℕ) (ε₁ : ℝ) (j : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  ((range K ×ˢ range K) ×ˢ range K).filter (fun t =>
    t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.Prime ∧
    U7153.zz n ≤ t.1.1 ∧ (t.1.1 : ℝ) < U7153.yy n ∧
    U7153.yy n ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧
    Nat.Coprime (t.1.2 * t.2) n ∧
    w n ε₁ j * t.1.2 * t.2 < n ∧
    w n ε₁ j ≤ t.1.1 ∧ (t.1.1 : ℝ) < w n ε₁ j * (1 + ε₁))
/-- Sum of the slice cardinalities, p. 1237 display 30. -/
def mass (n : ℕ) (ε₁ : ℝ) : ℝ :=
  ∑ j ∈ slices n ε₁, ((slice n ε₁ j).card : ℝ)
/-- Squarefree sifting divisors below D star, pp. 1236 and 1239. -/
def divisors (n : ℕ) (A : ℝ) : Finset ℕ :=
  (((range ⌈U7153.yy n⌉₊).filter (fun p => p.Prime ∧ ¬ p ∣ n)).powerset.image
    (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < √(n : ℝ) / log (n : ℝ) ^ (A + 1))
/-- The residue error in a slice, pp. 1236 and 1239 display 32. -/
def residueError (n : ℕ) (ε₁ : ℝ) (j d : ℕ) : ℝ :=
  (((slice n ε₁ j).filter
    (fun t => (t.1.1 * t.1.2 * t.2) % d = n % d)).card : ℝ) -
    ((slice n ε₁ j).card : ℝ) / (d.totient : ℝ)
/-- Total remainder with DQ enlarged to D star, p. 1241 display 33. -/
def remainder (n : ℕ) (A ε₁ : ℝ) : ℝ :=
  ∑ j ∈ slices n ε₁, ∑ d ∈ divisors n A, |residueError n ε₁ j d|
/-- The sieve coefficient of the total slice mass, p. 1237 display 29. -/
def sieveCoefficient (n : ℕ) (α ε C₁ : ℝ) : ℝ :=
  UNfull n / log n * (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ)) *
    (2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁)
/-- Cardinality coefficient from Lemma 14, p. 1237. -/
def massBound (n : ℕ) (ε₁ : ℝ) : ℝ :=
  (1 + ε₁) *
    (log (U7153.yy n) * (liPV (U7153.yy n) +
      √(U7153.yy n) * log (U7153.yy n) / (8 * π)) / U7153.yy n) * n *
    (LeanLab.ChenExplicit.BJS.cbar / log n + 36 / log n ^ 3 +
      (log (8 / 3) + 64 / log n ^ 2) *
        (log √(1 + ε₁) / (log (U7153.yy n) ^ 2 - log √(1 + ε₁) ^ 2) +
          27 / log n ^ 3))

/-- Positive slice endpoints for positive n, journal display 26 p. 1236. -/
theorem w_pos (n j : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    0 < w n ε₁ j := by
  unfold w U7153.zz
  exact mul_pos (rpow_pos_of_pos (by exact_mod_cast hn) _) (pow_pos (by linarith) _)

/-- Successive multiplicative endpoints, journal display 26 p. 1236. -/
theorem w_succ (n j : ℕ) (ε₁ : ℝ) :
    w n ε₁ (j + 1) = w n ε₁ j * (1 + ε₁) := by
  simp only [w, pow_succ, mul_assoc]

/-- Slice membership is exactly the strict logarithmic index bound, p. 1236. -/
theorem mem_slices_iff (n j : ℕ) (ε₁ : ℝ) :
    j ∈ slices n ε₁ ↔ (j : ℝ) < log (U7153.yy n / U7153.zz n) / log (1 + ε₁) := by
  simp only [slices, mem_range, Nat.lt_ceil]

/-- An indexed endpoint stays below y, journal display 26 p. 1236. -/
theorem w_lt_y {n j : ℕ} {ε₁ : ℝ} (hn : 0 < n) (hε : 0 < ε₁)
    (hj : j ∈ slices n ε₁) : w n ε₁ j < U7153.yy n := by
  have hz : 0 < U7153.zz n := rpow_pos_of_pos (by exact_mod_cast hn) _
  have hy : 0 < U7153.yy n := rpow_pos_of_pos (by exact_mod_cast hn) _
  have hb : 0 < 1 + ε₁ := by linarith
  have hl : 0 < log (1 + ε₁) := log_pos (by linarith)
  have hj' := (mem_slices_iff n j ε₁).mp hj
  have hjl := (lt_div_iff₀ hl).mp hj'
  apply (log_lt_log_iff (w_pos n j ε₁ hn hε) hy).mp
  rw [w, log_mul (ne_of_gt hz) (ne_of_gt (pow_pos hb _)), log_pow] 
  rw [log_div (ne_of_gt hy) (ne_of_gt hz)] at hjl
  linarith

/-- The endpoint sequence is strictly increasing, journal display 26 p. 1236. -/
theorem w_strictMono (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    StrictMono (w n ε₁) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [w_succ]
  nlinarith [w_pos n j ε₁ hn hε]

/-- Two distinct slices contain no common triple, journal display 27 p. 1236. -/
theorem slices_disjoint (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (slice n ε₁ i) (slice n ε₁ j) := by
  apply disjoint_left.mpr
  intro t hi hj
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hiw : w n ε₁ i ≤ (t.1.1 : ℝ) := hi'.2.2.2.2.2.2.2.2.2.1
  have hit : (t.1.1 : ℝ) < w n ε₁ i * (1 + ε₁) := hi'.2.2.2.2.2.2.2.2.2.2
  have hjw : w n ε₁ j ≤ (t.1.1 : ℝ) := hj'.2.2.2.2.2.2.2.2.2.1
  have hjt : (t.1.1 : ℝ) < w n ε₁ j * (1 + ε₁) := hj'.2.2.2.2.2.2.2.2.2.2
  rcases lt_or_gt_of_ne hij with h | h
  · have hw := (w_strictMono n ε₁ hn hε).monotone (Nat.succ_le_of_lt h)
    rw [w_succ] at hw
    linarith
  · have hw := (w_strictMono n ε₁ hn hε).monotone (Nat.succ_le_of_lt h)
    rw [w_succ] at hw
    linarith

/-- Summed mass counts each relaxed triple once, journal displays 27 and 30. -/
theorem mass_eq_card_union (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    mass n ε₁ = (((slices n ε₁).biUnion (slice n ε₁)).card : ℝ) := by
  have h := card_biUnion (s := slices n ε₁) (t := slice n ε₁)
    (fun i _ j _ hij => slices_disjoint n ε₁ hn hε hij)
  unfold mass
  exact_mod_cast h.symm

/-- Every original prime triple has an admissible slice, p. 1236 display 27. -/
theorem triple_mem_slice {n : ℕ} {ε₁ : ℝ} (hn : 0 < n) (hε : 0 < ε₁)
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ U7153.Triples n) :
    ∃ j ∈ slices n ε₁, t ∈ slice n ε₁ j := by
  obtain ⟨htrange, ht⟩ := mem_filter.mp ht
  obtain ⟨hp1, hp2, hp3, hz, hy, hyp2, hp23, hprod, hcop⟩ := ht
  have hz0 : 0 < U7153.zz n := rpow_pos_of_pos (by exact_mod_cast hn) _
  have hp0 : (0 : ℝ) < t.1.1 := by exact_mod_cast hp1.pos
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near ((le_div_iff₀ hz0).mpr (by simpa using hz))
    (by linarith : (1 : ℝ) < 1 + ε₁)
  have hwlo : w n ε₁ j ≤ (t.1.1 : ℝ) := by
    unfold w
    nlinarith [(le_div_iff₀ hz0).mp hjlo]
  have hwhi : (t.1.1 : ℝ) < w n ε₁ j * (1 + ε₁) := by
    have := (div_lt_iff₀ hz0).mp hjhi
    simpa only [pow_succ, w, mul_assoc, mul_comm, mul_left_comm] using this
  have hjmem : j ∈ slices n ε₁ := by
    rw [mem_slices_iff, lt_div_iff₀ (log_pos (by linarith : (1 : ℝ) < 1 + ε₁))]
    have hy0 : 0 < U7153.yy n := rpow_pos_of_pos (by exact_mod_cast hn) _
    have hw0 := w_pos n j ε₁ hn hε
    have hlog := log_lt_log hw0 (hwlo.trans_lt hy)
    rw [w, log_mul (ne_of_gt hz0) (ne_of_gt (pow_pos (by linarith : (0 : ℝ) < 1 + ε₁) _)), log_pow] at hlog
    rw [log_div (ne_of_gt hy0) (ne_of_gt hz0)]
    linarith
  refine ⟨j, hjmem, mem_filter.mpr ⟨?_, hp1, hp2, hp3, hz, hy, hyp2, hp23, ?_, ?_, hwlo, hwhi⟩⟩
  · have hnK : n ≤ ⌈(1 + ε₁) * n⌉₊ + 1 := by
      have hc := Nat.le_ceil ((1 + ε₁) * n)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hnK' : (n : ℝ) ≤ ⌈(1 + ε₁) * n⌉₊ := by nlinarith
      exact Nat.le_succ_of_le (by exact_mod_cast hnK')
    obtain ⟨ht12, ht3⟩ := mem_product.mp htrange
    obtain ⟨ht1, ht2⟩ := mem_product.mp ht12
    exact mem_product.mpr ⟨mem_product.mpr ⟨mem_range.mpr ((mem_range.mp ht1).trans_le hnK),
      mem_range.mpr ((mem_range.mp ht2).trans_le hnK)⟩,
      mem_range.mpr ((mem_range.mp ht3).trans_le hnK)⟩
  · rw [mul_assoc] at hcop
    exact (Nat.coprime_mul_iff_left.mp hcop).2
  · have hpR : (t.1.1 : ℝ) * t.1.2 * t.2 < n := by exact_mod_cast hprod
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hwlo (Nat.cast_nonneg t.1.2)) (Nat.cast_nonneg t.2)
    exact hm.trans_lt hpR

/-- The strict relaxed product bound, journal display 30 p. 1237. -/
theorem slice_product_lt {n j : ℕ} {ε₁ : ℝ} (hε : 0 < ε₁)
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j) :
    (t.1.1 : ℝ) * t.1.2 * t.2 < (1 + ε₁) * n := by
  obtain ⟨_, hp1, hp2, hp3, _, _, _, _, _, hw, _, hpw⟩ := mem_filter.mp ht
  have h2 : (0 : ℝ) < t.1.2 := by exact_mod_cast hp2.pos
  have h3 : (0 : ℝ) < t.2 := by exact_mod_cast hp3.pos
  have hmul := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hpw h2) h3
  have hmain := mul_lt_mul_of_pos_left hw (by linarith : (0 : ℝ) < 1 + ε₁)
  nlinarith

/-- The logarithmic slice length, journal display 26 p. 1236. -/
theorem log_y_div_z (n : ℕ) (hn : 0 < n) :
    log (U7153.yy n / U7153.zz n) = (5 / 24 : ℝ) * log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [U7153.yy, U7153.zz,
    log_div (ne_of_gt (rpow_pos_of_pos hn0 _)) (ne_of_gt (rpow_pos_of_pos hn0 _)),
    log_rpow hn0, log_rpow hn0]
  ring

/-- The slice count includes the final rounded interval, p. 1236 display 26. -/
theorem slices_card_lt (n : ℕ) (ε₁ : ℝ) (hn : 1 ≤ n) (hε : 0 < ε₁) :
    ((slices n ε₁).card : ℝ) < (5 / 24 : ℝ) * log n / log (1 + ε₁) + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  simp only [slices, card_range, log_y_div_z n hn0]
  exact Nat.ceil_lt_add_one (div_nonneg (by positivity) (log_pos (by linarith)).le)

/-- Rounding fits the printed 0.053 coefficient when summed with one quarter,
p. 1240 before display 33. The bound is on the number of terms, not the last index. -/
theorem slices_card_le (n : ℕ) (ε₁ : ℝ)
    (hL : 22000 ≤ log (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    ((slices n ε₁).card : ℝ) ≤ 0.212 * log n / log (1 + ε₁) := by
  have hn1 : 1 ≤ n := by
    by_contra hn
    have : n = 0 := by omega
    subst n
    norm_num at hL
  have hlogb : 0 < log (1 + ε₁) := log_pos (by linarith)
  have hb : log (1 + ε₁) ≤ 1 := by
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ε₁)
    linarith
  have hcount := slices_card_lt n ε₁ hn1 hε
  apply hcount.le.trans
  rw [div_add_one hlogb.ne', div_le_div_iff_of_pos_right hlogb]
  nlinarith

/-- Sum the per-slice estimates with both rounding constants, journal display 33.
CONDITIONAL ON the per-slice estimate. Analytic inputs remain outside this sum. -/
theorem remainder_sum_of_slice_bounds (n : ℕ) (A ε₁ B C : ℝ)
    (hL : 22000 ≤ log (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hSlice : ∀ j ∈ slices n ε₁,
      (∑ d ∈ divisors n A, |residueError n ε₁ j d|) ≤ B / 4 + 0.374 * C) :
    remainder n A ε₁ ≤
      0.053 * log n / log (1 + ε₁) * B +
      0.08 * log n / log (1 + ε₁) * C := by
  have hlogb : 0 < log (1 + ε₁) := log_pos (by linarith)
  have hratio : 0 ≤ log (n : ℝ) / log (1 + ε₁) := div_nonneg (by linarith) hlogb.le
  calc
    remainder n A ε₁ ≤ ∑ _j ∈ slices n ε₁, (B / 4 + 0.374 * C) := sum_le_sum hSlice
    _ = ((slices n ε₁).card : ℝ) * (B / 4 + 0.374 * C) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (0.212 * log n / log (1 + ε₁)) * (B / 4 + 0.374 * C) :=
      mul_le_mul_of_nonneg_right (slices_card_le n ε₁ hL hε hε1) (by positivity)
    _ ≤ _ := by
      apply le_of_sub_nonneg
      convert mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.000712) (mul_nonneg hratio hC) using 1 <;> ring

/-- The congruence sieve on a triple slice, journal display 27 p. 1236. -/
def siftedSlice (n : ℕ) (ε₁ : ℝ) (j : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (slice n ε₁ j).filter (fun t => ∀ p : ℕ,
    p.Prime → (p : ℝ) < U7153.yy n → ¬ p ∣ n →
      (t.1.1 * t.1.2 * t.2) % p ≠ n % p)

/-- The switching map covers B by the sifted triple slices, journal display 27.
No injectivity of the map from triples to B is required. -/
theorem SB_le_sum_siftedSlice (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    (U7153.SB n : ℝ) ≤ ∑ j ∈ slices n ε₁, ((siftedSlice n ε₁ j).card : ℝ) := by
  let f : ((ℕ × ℕ) × ℕ) → ℕ := fun t => n - t.1.1 * t.1.2 * t.2
  let T := (slices n ε₁).biUnion (siftedSlice n ε₁)
  have hsub : (U7153.Bset n).filter (U7153.NoSmallP n (U7153.yy n)) ⊆ T.image f := by
    intro b hb
    obtain ⟨hbB, hbS⟩ := mem_filter.mp hb
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hbB
    obtain ⟨j, hj, htj⟩ := triple_mem_slice hn hε ht
    apply mem_image.mpr
    refine ⟨t, mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨htj, ?_⟩⟩, rfl⟩
    intro p hp hpy hpn hmod
    have hprod : t.1.1 * t.1.2 * t.2 < n := (mem_filter.mp ht).2.2.2.2.2.2.2.2.1
    exact hbS p hp hpy hpn ((Nat.modEq_iff_dvd' hprod.le).mp hmod)
  have hcard := (card_le_card hsub).trans card_image_le
  have hsum : T.card ≤ ∑ j ∈ slices n ε₁, (siftedSlice n ε₁ j).card := card_biUnion_le
  have hfinal : U7153.SB n ≤ ∑ j ∈ slices n ε₁, (siftedSlice n ε₁ j).card := hcard.trans hsum
  exact_mod_cast hfinal

/-- Sum the upper sieve inequality on the slices, journal displays 27 to 29.
CONDITIONAL ON the per-slice upper sieve bound. -/
theorem sieve_slices_of_pointwise (n : ℕ) (α ε C₁ A ε₁ : ℝ)
    (hn : 0 < n) (hε : 0 < ε₁)
    (hSlice : ∀ j ∈ slices n ε₁,
      ((siftedSlice n ε₁ j).card : ℝ) ≤
        ((slice n ε₁ j).card : ℝ) * sieveCoefficient n α ε C₁ +
          ∑ d ∈ divisors n A, |residueError n ε₁ j d|) :
    (U7153.SB n : ℝ) ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + remainder n A ε₁ := by
  calc
    (U7153.SB n : ℝ) ≤ ∑ j ∈ slices n ε₁, ((siftedSlice n ε₁ j).card : ℝ) :=
      SB_le_sum_siftedSlice n ε₁ hn hε
    _ ≤ ∑ j ∈ slices n ε₁,
        (((slice n ε₁ j).card : ℝ) * sieveCoefficient n α ε C₁ +
          ∑ d ∈ divisors n A, |residueError n ε₁ j d|) := sum_le_sum hSlice
    _ = _ := by rw [sum_add_distrib, ← sum_mul]; rfl

end
end LeanLab.BS2022GRH.DecompC164c

#print axioms LeanLab.BS2022GRH.DecompC164c.w_pos
#print axioms LeanLab.BS2022GRH.DecompC164c.w_succ
#print axioms LeanLab.BS2022GRH.DecompC164c.mem_slices_iff
#print axioms LeanLab.BS2022GRH.DecompC164c.w_lt_y
#print axioms LeanLab.BS2022GRH.DecompC164c.w_strictMono
#print axioms LeanLab.BS2022GRH.DecompC164c.slices_disjoint
#print axioms LeanLab.BS2022GRH.DecompC164c.mass_eq_card_union
#print axioms LeanLab.BS2022GRH.DecompC164c.triple_mem_slice
#print axioms LeanLab.BS2022GRH.DecompC164c.slice_product_lt
#print axioms LeanLab.BS2022GRH.DecompC164c.log_y_div_z
#print axioms LeanLab.BS2022GRH.DecompC164c.slices_card_lt
#print axioms LeanLab.BS2022GRH.DecompC164c.slices_card_le
#print axioms LeanLab.BS2022GRH.DecompC164c.remainder_sum_of_slice_bounds
#print axioms LeanLab.BS2022GRH.DecompC164c.SB_le_sum_siftedSlice
#print axioms LeanLab.BS2022GRH.DecompC164c.sieve_slices_of_pointwise
