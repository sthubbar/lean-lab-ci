/- AI wrote the Lean code for CODEX task236.
Weighted finite transport for journal Theorem 7 p. 1236. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceModel236
import LeanLab.BS2022GRH.DecompC169b
import LeanLab.BS2022GRH.SieveModelC169
import LeanLab.BS2022GRH.PublishedInputs236

namespace LeanLab.BS2022GRH.SliceSieve236
open Real Finset Classical ChenThresholdGRH DecompC169a DecompC164c
noncomputable section

/-- The multiplicity of a fiber preserves the triple count, p. 1236 display 27. -/
def fiberWeight {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℕ) (x : ℕ) : ℝ :=
  ((T.filter (fun t => f t = x)).card : ℝ)

/-- Sum the fiber multiplicities, p. 1236 display 27. -/
theorem fiberWeight_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℕ) :
    (∑ x ∈ T.image f, fiberWeight T f x) = (T.card : ℝ) := by
  unfold fiberWeight
  exact_mod_cast (card_eq_sum_card_image f T).symm

/-- Filtering after transport equals filtering before transport, p. 1236 display 27. -/
theorem fiberWeight_sum_filter {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (f : ι → ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (∑ x ∈ (T.image f).filter q, fiberWeight T f x) =
      ((T.filter (fun t => q (f t))).card : ℝ) := by
  have h := sum_card_fiberwise_eq_card_filter T ((T.image f).filter q) f
  have heq : T.filter (fun t => f t ∈ (T.image f).filter q) =
      T.filter (fun t => q (f t)) := by
    apply filter_congr
    intro t ht
    simp [mem_image_of_mem f ht]
  rw [heq] at h
  unfold fiberWeight
  exact_mod_cast h

/-- Fiber multiplicities vanish off their finite support, p. 1236. -/
theorem fiberWeight_support {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (f : ι → ℕ) (x : ℕ) (hx : x ∉ T.image f) :
    fiberWeight T f x = 0 := by
  unfold fiberWeight
  have he : T.filter (fun t => f t = x) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, htx⟩ := mem_filter.mp ht
    exact hx (mem_image.mpr ⟨t, ht, htx⟩)
  simp [he]

/-- Multiplicative slice endpoints satisfy the Lemma 7 source range, pp. 1221 and 1236. -/
theorem y_gt_exp2753 (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    exp 2753 < U7153.yy n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  apply (log_lt_log_iff (exp_pos _) (rpow_pos_of_pos hn0 _)).mp
  rw [log_exp, log_rpow hn0]
  linarith

/-- The product premise of the sieve at any large endpoint, pp. 1221 and 1236.
CONDITIONAL ON the cited Lemma 7 input. -/
theorem product_guard (n : ℕ) (z u ε : ℝ) (hL : Lemma7J)
    (hz : exp 2753 < z) (hu : 400 ≤ u) (huz : u < z)
    (he : epsJ u ≤ ε) (he0 : 0 < ε) :
    ∀ (x : ℕ) (v : ℝ), 1 < v → v < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p =>
        p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
        p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ (1 + ε) * (log z / log v) := by
  intro x v hv hvz
  let w := max v u
  let F := (range ⌈z⌉₊).filter (fun p : ℕ =>
    p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
    p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z)
  let B := (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hwz : w < z := max_lt hvz huz
  have huw : u ≤ w := le_max_right _ _
  obtain ⟨hband, _⟩ := hL z u w hz hu huw hwz
  have hsub : F ⊆ B := by
    intro p hp
    obtain ⟨hr, hpP, hpQ, hvp, hpz⟩ := mem_filter.mp hp
    have hup : u ≤ (p : ℝ) := by
      by_contra h
      have hpu : (p : ℝ) < u := lt_of_not_ge h
      apply hpQ
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpu), hpP.1, hpP.2, hpu⟩
    exact mem_filter.mpr ⟨hr, hpP.1, max_le hvp hup, hpz⟩
  have hone : ∀ p ∈ B, 1 ≤ (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    obtain ⟨_, _, hwp, _⟩ := mem_filter.mp hp
    have hden : 1 < (p : ℝ) - 1 := by linarith
    have ha : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      rw [sub_pos, div_lt_one (by linarith : (0 : ℝ) < p - 1)]
      exact hden
    exact (one_le_inv₀ ha).mpr (sub_le_self _ (by positivity))
  have hprod : ∏ p ∈ F, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hp
      exact le_trans (by norm_num) (hone p (hsub hp))
    · intro p hp _
      exact hone p hp
  have hlv : 0 < log v := log_pos hv
  have hlw : 0 < log w := log_pos (by dsimp [w]; linarith [le_max_left v u])
  have hlz : 0 < log z := log_pos (lt_trans hv hvz)
  have hlog : log v ≤ log w := log_le_log (by linarith) (le_max_left v u)
  apply le_of_lt
  calc
    _ ≤ ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ := hprod
    _ < (1 + epsJ u) * (log z / log w) := hband
    _ ≤ (1 + ε) * (log z / log v) :=
      mul_le_mul (by linarith) (div_le_div_of_nonneg_left hlz.le hlv hlog)
        (div_nonneg hlz.le hlw.le) (by linarith)

/-- The upper sieve on an arbitrary finite family with multiplicities, p. 1236.
CONDITIONAL ON the supplied linear sieve and its product premise. -/
theorem indexed_upper_sieve {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (f : ι → ℕ) (n : ℕ) (z D u ε C₁ C₂ : ℝ)
    (hT : LinearSieveT4 ε C₁ C₂) (hev : Even n)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hz : 2 ≤ z)
    (hprod : ∀ (x : ℕ) (v : ℝ), 1 < v → v < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p =>
        p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
        p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ (1 + ε) * (log z / log v))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    ((T.filter (fun t => ∀ p ∈ primesBelow n z, ¬ p ∣ f t)).card : ℝ) ≤
      (2 * exp eulerMascheroniConstant / (log D / log z) +
        ε * C₁ * exp 2 * hS (log D / log z)) *
        ((T.card : ℝ) * ∏ p ∈ primesBelow n z, (1 - 1 / ((p : ℝ) - 1))) +
      ∑ U ∈ (primesBelow n z).powerset.filter
        (fun U => ((∏ p ∈ U, p : ℕ) : ℝ) < (∏ p ∈ primesBelow n u, p : ℕ) * D),
        |((T.filter (fun t => (∏ p ∈ U, p) ∣ f t)).card : ℝ) -
          (T.card : ℝ) / ((∏ p ∈ U, p : ℕ).totient : ℝ)| := by
  have hg : ∀ x : ℕ, ∀ p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ),
      0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
    intro x p hp
    have hp3 : 3 ≤ p := by
      have hp2 := hp.1.two_le
      have hpne : p ≠ 2 := by rintro rfl; exact hp.2 hev.two_dvd
      omega
    have hd : (1 : ℝ) < (p : ℝ) - 1 := by
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    constructor
    · positivity
    · exact (div_lt_one (by linarith : (0 : ℝ) < p - 1)).mpr hd
  have hQ : (↑(primesBelow n u) : Set ℕ) ⊆ {p : ℕ | p.Prime ∧ ¬ p ∣ n} := by
    intro p hp
    obtain ⟨_, hp, hpn, _⟩ := mem_filter.mp (mem_coe.mp hp)
    exact ⟨hp, hpn⟩
  have key := hT (T.image f) (fiberWeight T f) {p : ℕ | p.Prime ∧ ¬ p ∣ n}
    (primesBelow n u) (fun _ p => 1 / ((p : ℝ) - 1)) z D
    (fun x => Nat.cast_nonneg _) (fiberWeight_support T f) (fun _ hp => hp.1) hQ
    hg he0 he1 hz (by
      intro x v hv hvz
      convert hprod x v hv hvz using 1 <;> congr 2)
  have hmain := key.1 hzD hs
  have hP : @Finset.filter ℕ (fun p =>
      p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧ (p : ℝ) < z)
      (fun p => @instDecidableAnd _ _ (Classical.propDecidable _) (by infer_instance)) (range ⌈z⌉₊)
      = primesBelow n z := by
    ext p
    simp [primesBelow, and_assoc]
  dsimp only at hmain
  rw [hP, fiberWeight_sum_filter, ← sum_mul, fiberWeight_sum] at hmain
  have hrem : ∀ U ∈ (primesBelow n z).powerset,
      (∑ x ∈ (T.image f).filter (fun x => (∏ p ∈ U, p) ∣ x), fiberWeight T f x) -
        ∑ x ∈ T.image f, fiberWeight T f x *
          ∏ p ∈ (∏ p ∈ U, p : ℕ).primeFactors, (1 / ((p : ℝ) - 1)) =
      ((T.filter (fun t => (∏ p ∈ U, p) ∣ f t)).card : ℝ) -
        (T.card : ℝ) / ((∏ p ∈ U, p : ℕ).totient : ℝ) := by
    intro U hU
    have hprime : ∀ p ∈ U, p.Prime := by
      intro p hp
      exact (mem_filter.mp (mem_powerset.mp hU hp)).2.1
    have hsq : Squarefree (∏ p ∈ U, p : ℕ) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
      · intro p hp
        exact (hprime p hp).squarefree
    rw [fiberWeight_sum_filter, ← sum_mul, fiberWeight_sum,
      SieveModelC169.squarefree_model _ hsq]
    ring
  convert hmain using 1
  congr 1
  apply sum_congr rfl
  intro U hU
  rw [hrem U (mem_filter.mp hU).1]

/-- A positive congruent lift handles products above n after relaxation, p. 1236.
The lift is a multiple of every sifting divisor plus n. -/
def sliceLift (n : ℕ) (ε₁ : ℝ) : ℕ :=
  n + (∏ p ∈ primesBelow n (U7153.yy n), p) * (⌈(1 + ε₁) * n⌉₊ + 1) ^ 3

/-- The lifted endpoint exceeds each slice product, p. 1236 display 27. -/
theorem sliceLift_ge_product {n j : ℕ} {ε₁ : ℝ}
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j) :
    t.1.1 * t.1.2 * t.2 ≤ sliceLift n ε₁ := by
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  obtain ⟨htr, hp1, hp2, hp3, _⟩ := mem_filter.mp ht
  obtain ⟨h12, h3⟩ := mem_product.mp htr
  obtain ⟨h1, h2⟩ := mem_product.mp h12
  have ht1 : t.1.1 < K := mem_range.mp h1
  have ht2 : t.1.2 < K := mem_range.mp h2
  have ht3 : t.2 < K := mem_range.mp h3
  have h12 : t.1.1 * t.1.2 < K * K :=
    (Nat.mul_lt_mul_of_pos_right ht1 hp2.pos).trans_le (Nat.mul_le_mul_left K ht2.le)
  have hpK : t.1.1 * t.1.2 * t.2 ≤ K ^ 3 := by
    calc
      t.1.1 * t.1.2 * t.2 ≤ K * K * t.2 := Nat.mul_le_mul_right _ h12.le
      _ ≤ K * K * K := Nat.mul_le_mul_left _ ht3.le
      _ = K ^ 3 := by ring
  have hM : 1 ≤ ∏ p ∈ primesBelow n (U7153.yy n), p := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact (mem_filter.mp hp).2.1.ne_zero
  have hK := Nat.mul_le_mul_right (K ^ 3) hM
  simp only [one_mul] at hK
  exact hpK.trans (hK.trans (Nat.le_add_left _ _))

/-- Divisibility of the lift is exactly the original residue condition, p. 1236. -/
theorem sliceLift_dvd_iff {n j d : ℕ} {ε₁ : ℝ}
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j)
    (hd : d ∣ ∏ p ∈ primesBelow n (U7153.yy n), p) :
    d ∣ sliceLift n ε₁ - t.1.1 * t.1.2 * t.2 ↔
      (t.1.1 * t.1.2 * t.2) % d = n % d := by
  rw [← Nat.modEq_iff_dvd' (sliceLift_ge_product ht)]
  change (t.1.1 * t.1.2 * t.2) % d = sliceLift n ε₁ % d ↔ _
  have hm : d ∣ (∏ p ∈ primesBelow n (U7153.yy n), p) *
      (⌈(1 + ε₁) * n⌉₊ + 1) ^ 3 := dvd_mul_of_dvd_left hd _
  simp [sliceLift, Nat.add_mod, Nat.mod_eq_zero_of_dvd hm]

/-- Every prime subset product divides the full sifting product, p. 1236. -/
theorem subset_prod_dvd (n : ℕ) (z : ℝ) (T : Finset ℕ)
    (hT : T ⊆ primesBelow n z) : (∏ p ∈ T, p) ∣ ∏ p ∈ primesBelow n z, p := by
  exact Finset.prod_dvd_prod_of_subset T (primesBelow n z) (fun p => p) hT

/-- Products uniquely index subsets of distinct primes, p. 1236. -/
theorem subset_product_injective (n : ℕ) (z : ℝ) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (primesBelow n z).powerset := by
  intro T hT U hU heq
  have hpf (V : Finset ℕ) (hV : V ∈ (primesBelow n z).powerset) :
      (∏ p ∈ V, p : ℕ).primeFactors = V := by
    apply Nat.primeFactors_prod
    intro p hp
    exact (mem_filter.mp (mem_powerset.mp hV hp)).2.1
  change (∏ p ∈ T, p : ℕ) = ∏ p ∈ U, p at heq
  rw [← hpf T hT, ← hpf U hU, heq]

/-- The explicit prime interval agrees with the sealed divisor support, p. 1236. -/
theorem primesBelow_y_eq (n : ℕ) :
    primesBelow n (U7153.yy n) =
      (range ⌈U7153.yy n⌉₊).filter (fun p => p.Prime ∧ ¬ p ∣ n) := by
  ext p
  simp only [primesBelow, mem_filter, mem_range]
  constructor
  · intro h; exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h; exact ⟨h.1, h.2.1, h.2.2, Nat.lt_ceil.mp h.1⟩

/-- Enlarge the subset-indexed sieve remainder to D star, p. 1236.
CONDITIONAL ON the product cutoff comparison. -/
theorem slice_remainder_enlarge (n j : ℕ) (A ε₁ D u : ℝ)
    (hcut : (smallProduct n u : ℝ) * D ≤ √(n : ℝ) / log n ^ (A + 1)) :
    (∑ U ∈ (primesBelow n (U7153.yy n)).powerset.filter
      (fun U => ((∏ p ∈ U, p : ℕ) : ℝ) < (∏ p ∈ primesBelow n u, p : ℕ) * D),
      |residueError n ε₁ j (∏ p ∈ U, p)|) ≤
        ∑ d ∈ divisors n A, |residueError n ε₁ j d| := by
  let P := primesBelow n (U7153.yy n)
  let V := P.powerset.filter
    (fun U => ((∏ p ∈ U, p : ℕ) : ℝ) < (smallProduct n u : ℝ) * D)
  have hi : Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p) V :=
    (subset_product_injective n (U7153.yy n)).mono (filter_subset _ _)
  have hsub : V.image (fun U => ∏ p ∈ U, p) ⊆ divisors n A := by
    intro d hd
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hd
    obtain ⟨hU, hcutU⟩ := mem_filter.mp hU
    apply mem_filter.mpr
    refine ⟨?_, hcutU.trans_le hcut⟩
    apply mem_image.mpr
    refine ⟨U, ?_, rfl⟩
    rw [← primesBelow_y_eq]
    exact hU
  calc
    _ = ∑ d ∈ V.image (fun U => ∏ p ∈ U, p), |residueError n ε₁ j d| :=
      (sum_image hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- Apply the existing weighted upper sieve to a congruent lift of one slice,
p. 1236 display 29. CONDITIONAL ON LinearSieveT4 and its stated premises. -/
theorem slice_sieve_raw (n j : ℕ) (A ε₁ D u ε C₁ C₂ : ℝ)
    (hT : LinearSieveT4 ε C₁ C₂) (hev : Even n)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hy : 2 ≤ U7153.yy n)
    (hprod : ∀ (x : ℕ) (v : ℝ), 1 < v → v < U7153.yy n →
      ∏ p ∈ (range ⌈U7153.yy n⌉₊).filter (fun p =>
        p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
        p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < U7153.yy n),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ (1 + ε) * (log (U7153.yy n) / log v))
    (hyD : U7153.yy n ≤ D) (hs : log D / log (U7153.yy n) ≤ 3)
    (hcut : (smallProduct n u : ℝ) * D ≤ √(n : ℝ) / log n ^ (A + 1)) :
    ((siftedSlice n ε₁ j).card : ℝ) ≤
      (2 * exp eulerMascheroniConstant / (log D / log (U7153.yy n)) +
        ε * C₁ * exp 2 * hS (log D / log (U7153.yy n))) *
        (((slice n ε₁ j).card : ℝ) *
          ∏ p ∈ primesBelow n (U7153.yy n), (1 - 1 / ((p : ℝ) - 1))) +
      ∑ d ∈ divisors n A, |residueError n ε₁ j d| := by
  let f : ((ℕ × ℕ) × ℕ) → ℕ := fun t => sliceLift n ε₁ - t.1.1 * t.1.2 * t.2
  have key := indexed_upper_sieve (slice n ε₁ j) f n (U7153.yy n) D u ε C₁ C₂
    hT hev he0 he1 hy hprod hyD hs
  have hS : (slice n ε₁ j).filter
      (fun t => ∀ p ∈ primesBelow n (U7153.yy n), ¬ p ∣ f t) = siftedSlice n ε₁ j := by
    apply filter_congr
    intro t ht
    constructor
    · intro h p hp hpy hpn
      have hpP : p ∈ primesBelow n (U7153.yy n) :=
        mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpy), hp, hpn, hpy⟩
      exact mt (sliceLift_dvd_iff ht (dvd_prod_of_mem (fun p : ℕ => p) hpP)).mpr (h p hpP)
    · intro h p hpP
      obtain ⟨_, hp, hpn, hpy⟩ := mem_filter.mp hpP
      have hpd : p ∣ ∏ p ∈ primesBelow n (U7153.yy n), p :=
        dvd_prod_of_mem (fun p : ℕ => p) hpP
      exact mt (sliceLift_dvd_iff ht hpd).mp (h p hp hpy hpn)
  rw [hS] at key
  have hres : ∀ U ∈ (primesBelow n (U7153.yy n)).powerset,
      (((slice n ε₁ j).filter (fun t => (∏ p ∈ U, p) ∣ f t)).card : ℝ) -
        ((slice n ε₁ j).card : ℝ) / ((∏ p ∈ U, p : ℕ).totient : ℝ) =
      residueError n ε₁ j (∏ p ∈ U, p) := by
    intro U hU
    unfold residueError
    congr 2
    apply congrArg Finset.card
    apply filter_congr
    intro t ht
    exact sliceLift_dvd_iff ht (subset_prod_dvd n (U7153.yy n) U (mem_powerset.mp hU))
  have heq : (∑ U ∈ (primesBelow n (U7153.yy n)).powerset.filter
      (fun U => ((∏ p ∈ U, p : ℕ) : ℝ) < (∏ p ∈ primesBelow n u, p : ℕ) * D),
      |(((slice n ε₁ j).filter (fun t => (∏ p ∈ U, p) ∣ f t)).card : ℝ) -
        ((slice n ε₁ j).card : ℝ) / ((∏ p ∈ U, p : ℕ).totient : ℝ)|) =
      ∑ U ∈ (primesBelow n (U7153.yy n)).powerset.filter
      (fun U => ((∏ p ∈ U, p : ℕ) : ℝ) < (∏ p ∈ primesBelow n u, p : ℕ) * D),
      |residueError n ε₁ j (∏ p ∈ U, p)| := by
    apply sum_congr rfl
    intro U hU
    rw [hres U (mem_filter.mp hU).1]
  rw [heq] at key
  exact key.trans (add_le_add_right (slice_remainder_enlarge n j A ε₁ D u hcut) _)


end
end LeanLab.BS2022GRH.SliceSieve236

#print axioms LeanLab.BS2022GRH.SliceSieve236.fiberWeight_sum
#print axioms LeanLab.BS2022GRH.SliceSieve236.fiberWeight_sum_filter
#print axioms LeanLab.BS2022GRH.SliceSieve236.fiberWeight_support
#print axioms LeanLab.BS2022GRH.SliceSieve236.y_gt_exp2753
#print axioms LeanLab.BS2022GRH.SliceSieve236.product_guard
#print axioms LeanLab.BS2022GRH.SliceSieve236.indexed_upper_sieve
#print axioms LeanLab.BS2022GRH.SliceSieve236.sliceLift_ge_product
#print axioms LeanLab.BS2022GRH.SliceSieve236.sliceLift_dvd_iff
#print axioms LeanLab.BS2022GRH.SliceSieve236.subset_prod_dvd
#print axioms LeanLab.BS2022GRH.SliceSieve236.subset_product_injective
#print axioms LeanLab.BS2022GRH.SliceSieve236.primesBelow_y_eq
#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_remainder_enlarge
#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_sieve_raw
