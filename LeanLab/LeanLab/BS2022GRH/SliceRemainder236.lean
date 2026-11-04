/- AI wrote the Lean code for CODEX task236.
Coprimality correction for journal Theorem 7 pp. 1239 and 1240.
Goldbach is open. -/
import LeanLab.BS2022GRH.SliceSieve236
namespace LeanLab.BS2022GRH.SliceRemainder236
open Real Finset Classical ChenThresholdGRH DecompC164c DecompC169a
noncomputable section

/-- The residue after inserting coprimality, journal p. 1239 display 32. -/
def reducedResidue (n j d : ℕ) (ε₁ : ℝ) : ℝ :=
  (((slice n ε₁ j).filter
    (fun t => (t.1.1 * t.1.2 * t.2) % d = n % d)).card : ℝ) -
    (((slice n ε₁ j).filter (fun t => Nat.Coprime (t.1.1 * t.1.2 * t.2) d)).card : ℝ) /
      (d.totient : ℝ)

/-- Triples excluded by the coprimality insertion, journal p. 1239. -/
def badCount (n j d : ℕ) (ε₁ : ℝ) : ℝ :=
  (((slice n ε₁ j).filter (fun t => ¬ Nat.Coprime (t.1.1 * t.1.2 * t.2) d)).card : ℝ)

/-- The exact signed insertion identity, journal p. 1239.
Taking absolute values removes the sign of the correction. -/
theorem residue_split (n j d : ℕ) (ε₁ : ℝ) :
    residueError n ε₁ j d = reducedResidue n j d ε₁ - badCount n j d ε₁ / d.totient := by
  have hc := card_filter_add_card_filter_not
    (s := slice n ε₁ j) (p := fun t => Nat.Coprime (t.1.1 * t.1.2 * t.2) d)
  have hcR : (((slice n ε₁ j).filter (fun t => Nat.Coprime (t.1.1 * t.1.2 * t.2) d)).card : ℝ) +
      badCount n j d ε₁ = ((slice n ε₁ j).card : ℝ) := by
    unfold badCount
    exact_mod_cast hc
  unfold residueError reducedResidue
  rw [← hcR, add_div]
  ring

/-- The absolute residue correction, journal display 32 p. 1240. -/
theorem residue_abs_le (n j d : ℕ) (ε₁ : ℝ) :
    |residueError n ε₁ j d| ≤ |reducedResidue n j d ε₁| + badCount n j d ε₁ / d.totient := by
  rw [residue_split]
  have hb : 0 ≤ badCount n j d ε₁ / (d.totient : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hb])

/-- A large prime is coprime to a product of smaller primes, journal p. 1239. -/
theorem large_prime_coprime (n p : ℕ) (z : ℝ) (hp : p.Prime) (hzp : z ≤ (p : ℝ))
    (T : Finset ℕ) (hT : T ⊆ primesBelow n z) : Nat.Coprime p (∏ q ∈ T, q) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp hdvd
  obtain ⟨_, hqprime, _, hqz⟩ := mem_filter.mp (hT hq)
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  subst q
  linarith

/-- Sifting divisors are squarefree and coprime to n, journal p. 1239. -/
theorem divisor_spec {n d : ℕ} {A : ℝ} (hd : d ∈ divisors n A) :
    Squarefree d ∧ Nat.Coprime d n ∧ 0 < d ∧
      (d : ℝ) < √(n : ℝ) / log n ^ (A + 1) := by
  obtain ⟨hdI, hdlt⟩ := mem_filter.mp hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hdI
  rw [← SliceSieve236.primesBelow_y_eq] at hT
  have hp (p : ℕ) (hp : p ∈ T) : p.Prime ∧ ¬ p ∣ n := by
    have h := mem_filter.mp (mem_powerset.mp hT hp)
    exact ⟨h.2.1, h.2.2.1⟩
  have hsq : Squarefree (∏ p ∈ T, p : ℕ) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpT q hqT hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hpT).1 (hp q hqT).1).mpr hpq)
    · intro p hpT
      exact (hp p hpT).1.squarefree
  have hcop : Nat.Coprime (∏ p ∈ T, p) n := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hpT
    exact ((hp p hpT).1.coprime_iff_not_dvd).mpr (hp p hpT).2
  exact ⟨hsq, hcop, Nat.pos_of_ne_zero hsq.ne_zero, hdlt⟩

/-- The two large primes are automatically coprime to each sifting divisor, p. 1239. -/
theorem slice_large_coprime {n j d : ℕ} {A ε₁ : ℝ}
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j) (hd : d ∈ divisors n A) :
    Nat.Coprime (t.1.2 * t.2) d := by
  obtain ⟨_, _, hp2, hp3, _, _, hy2, h23, _⟩ := mem_filter.mp ht
  obtain ⟨hdI, _⟩ := mem_filter.mp hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hdI
  rw [← SliceSieve236.primesBelow_y_eq] at hT
  apply Nat.coprime_mul_iff_left.mpr
  constructor
  · exact large_prime_coprime n t.1.2 (U7153.yy n) hp2 hy2 T (mem_powerset.mp hT)
  · exact large_prime_coprime n t.2 (U7153.yy n) hp3
      (hy2.trans (by exact_mod_cast h23)) T (mem_powerset.mp hT)

/-- Only p1 can cause a failed coprimality condition, journal p. 1239. -/
theorem slice_not_coprime_iff {n j d : ℕ} {A ε₁ : ℝ}
    {t : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j) (hd : d ∈ divisors n A) :
    ¬ Nat.Coprime (t.1.1 * t.1.2 * t.2) d ↔ t.1.1 ∣ d := by
  have hp1 : t.1.1.Prime := (mem_filter.mp ht).2.1
  rw [mul_assoc, Nat.coprime_mul_iff_left,
    and_iff_left (slice_large_coprime ht hd), hp1.coprime_iff_not_dvd, not_not]

/-- Sum the coprimality corrections before applying Lemmas 4 and 5, p. 1240. -/
theorem slice_remainder_split (n j : ℕ) (A ε₁ : ℝ) :
    (∑ d ∈ divisors n A, |residueError n ε₁ j d|) ≤
      (∑ d ∈ divisors n A, |reducedResidue n j d ε₁|) +
      ∑ d ∈ divisors n A, badCount n j d ε₁ / d.totient := by
  rw [← sum_add_distrib]
  exact sum_le_sum (fun d _ => residue_abs_le n j d ε₁)

/-- An ordered prime pair is determined by its product, journal p. 1239.
Use Mathlib uniqueness of prime factorization up to permutation and sortedness. -/
theorem slice_pair_product_injective {n j : ℕ} {ε₁ : ℝ}
    {t u : (ℕ × ℕ) × ℕ} (ht : t ∈ slice n ε₁ j) (hu : u ∈ slice n ε₁ j)
    (hfirst : t.1.1 = u.1.1) (hprod : t.1.2 * t.2 = u.1.2 * u.2) : t = u := by
  obtain ⟨_, _, ht2, ht3, _, _, _, ht23, _⟩ := mem_filter.mp ht
  obtain ⟨_, _, hu2, hu3, _, _, _, hu23, _⟩ := mem_filter.mp hu
  have hperm : [t.1.2, t.2].Perm [u.1.2, u.2] := perm_of_prod_eq_prod
    (by simpa using hprod)
    (by intro p hp; simp at hp
        rcases hp with rfl | rfl; exact ht2.prime; exact ht3.prime)
    (by intro p hp; simp at hp
        rcases hp with rfl | rfl; exact hu2.prime; exact hu3.prime)
  have heq : [t.1.2, t.2] = [u.1.2, u.2] := List.Perm.eq_of_pairwise'
    (r := (· ≤ ·)) (by simpa using ht23) (by simpa using hu23) hperm
  have hp : t.1.2 = u.1.2 ∧ t.2 = u.2 := by simpa using heq
  exact Prod.ext (Prod.ext hfirst hp.1) hp.2

/-- Fixing p1 bounds its slice fiber by the number of possible integer products p2 p3,
journal p. 1239. The endpoint is non-strict for this upper bound. -/
theorem slice_fiber_le (n j p : ℕ) (ε₁ : ℝ) (hε : 0 < ε₁) (hp : 0 < p) :
    (((slice n ε₁ j).filter (fun t => t.1.1 = p)).card : ℝ) ≤ (1 + ε₁) * n / p := by
  let F := (slice n ε₁ j).filter (fun t => t.1.1 = p)
  let f : ((ℕ × ℕ) × ℕ) → ℕ := fun t => t.1.2 * t.2
  have hinj : Set.InjOn f F := by
    intro t ht u hu heq
    exact slice_pair_product_injective (mem_filter.mp ht).1 (mem_filter.mp hu).1
      ((mem_filter.mp ht).2.trans (mem_filter.mp hu).2.symm) heq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmap : Set.MapsTo f F (Icc 1 ⌊(1 + ε₁) * n / p⌋₊) := by
    intro t ht
    obtain ⟨ht, htp⟩ := mem_filter.mp ht
    have ht2 : t.1.2.Prime := (mem_filter.mp ht).2.2.1
    have ht3 : t.2.Prime := (mem_filter.mp ht).2.2.2.1
    have hprod := slice_product_lt hε ht
    have hlt : (f t : ℝ) < (1 + ε₁) * n / p := by
      rw [lt_div_iff₀ hpR]
      rw [htp] at hprod
      dsimp [f]
      push_cast
      nlinarith
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ht2.ne_zero ht3.ne_zero), Nat.le_floor hlt.le⟩
  have hc := card_le_card_of_injOn f hmap hinj
  have hc' : F.card ≤ ⌊(1 + ε₁) * n / p⌋₊ := by simpa using hc
  have hN : 0 ≤ (1 + ε₁) * (n : ℝ) / p := by positivity
  exact (by exact_mod_cast hc' : (F.card : ℝ) ≤ ⌊(1 + ε₁) * (n : ℝ) / p⌋₊).trans (Nat.floor_le hN)

/-- A uniform fiber bound uses p1 at least z, journal p. 1239. -/
theorem slice_fiber_le_uniform (n j p : ℕ) (ε₁ : ℝ) (hε : 0 < ε₁) (hn : 0 < n) :
    (((slice n ε₁ j).filter (fun t => t.1.1 = p)).card : ℝ) ≤ (1 + ε₁) * n / U7153.zz n := by
  have hz : 0 < U7153.zz n := rpow_pos_of_pos (by exact_mod_cast hn) _
  by_cases hF : ((slice n ε₁ j).filter (fun t => t.1.1 = p)).Nonempty
  · obtain ⟨t, ht⟩ := hF
    obtain ⟨ht, htp⟩ := mem_filter.mp ht
    have hp : 0 < p := htp ▸ (mem_filter.mp ht).2.1.pos
    have hzp : U7153.zz n ≤ (p : ℝ) := htp ▸ (mem_filter.mp ht).2.2.2.2.1
    exact (slice_fiber_le n j p ε₁ hε hp).trans
      (div_le_div_of_nonneg_left (by positivity) hz hzp)
  · rw [not_nonempty_iff_eq_empty.mp hF]
    simp only [card_empty, Nat.cast_zero]
    positivity

/-- The excluded mass has the printed omega correction, journal p. 1239. -/
theorem badCount_le {n j d : ℕ} {A ε₁ : ℝ} (hd : d ∈ divisors n A)
    (hε : 0 < ε₁) (hn : 0 < n) :
    badCount n j d ε₁ ≤ (1 + ε₁) * n / U7153.zz n * (d.primeFactors.card : ℝ) := by
  let B := (slice n ε₁ j).filter (fun t => ¬ Nat.Coprime (t.1.1 * t.1.2 * t.2) d)
  have hmap : Set.MapsTo (fun t : (ℕ × ℕ) × ℕ => t.1.1) B d.primeFactors := by
    intro t ht
    obtain ⟨ht, hbad⟩ := mem_filter.mp ht
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp ht).2.1,
      (slice_not_coprime_iff ht hd).mp hbad, (divisor_spec hd).1.ne_zero⟩
  have hc := card_eq_sum_card_fiberwise hmap
  calc
    badCount n j d ε₁ = ∑ p ∈ d.primeFactors, ((B.filter (fun t => t.1.1 = p)).card : ℝ) := by
      unfold badCount
      exact_mod_cast hc
    _ ≤ ∑ p ∈ d.primeFactors, (1 + ε₁) * n / U7153.zz n := by
      apply sum_le_sum
      intro p _
      have hsub : B.filter (fun t => t.1.1 = p) ⊆ (slice n ε₁ j).filter (fun t => t.1.1 = p) := by
        intro t ht
        obtain ⟨ht, htp⟩ := mem_filter.mp ht
        exact mem_filter.mpr ⟨(mem_filter.mp ht).1, htp⟩
      exact (Nat.cast_le.mpr (card_le_card hsub)).trans (slice_fiber_le_uniform n j p ε₁ hε hn)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- Sum the excluded mass with the reciprocal totient estimate, journal display 32.
CONDITIONAL ON Lemma 5 and the uniform omega estimate supplied by Lemma 4. -/
theorem correction_sum_of_omega_phi (n j : ℕ) (A ε₁ Ω : ℝ)
    (hPhi : PaperInputs148.Lemma5PhiJ) (hn : 0 < n) (hε : 0 < ε₁) (hΩ : 0 ≤ Ω)
    (hD : 1 < √(n : ℝ) / log n ^ (A + 1))
    (hOmega : ∀ d ∈ divisors n A, (d.primeFactors.card : ℝ) ≤ Ω) :
    (∑ d ∈ divisors n A, badCount n j d ε₁ / d.totient) ≤
      ((1 + ε₁) * n / U7153.zz n) * Ω *
        Mphi (√(n : ℝ) / log n ^ (A + 1)) * log (√(n : ℝ) / log n ^ (A + 1)) := by
  have hz : 0 < U7153.zz n := rpow_pos_of_pos (by exact_mod_cast hn) _
  have hB : 0 ≤ (1 + ε₁) * (n : ℝ) / U7153.zz n := by positivity
  have htot := DecompC169b.squarefree_totient_sum_le hPhi (divisors n A)
    (√(n : ℝ) / log n ^ (A + 1)) hD (fun d hd =>
      ⟨(divisor_spec hd).1, (divisor_spec hd).2.2.1, (divisor_spec hd).2.2.2.le⟩)
  calc
    _ ≤ ∑ d ∈ divisors n A, (((1 + ε₁) * n / U7153.zz n) * Ω) / d.totient := by
      apply sum_le_sum
      intro d hd
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (badCount_le hd hε hn).trans (mul_le_mul_of_nonneg_left (hOmega d hd) hB)
    _ = (((1 + ε₁) * n / U7153.zz n) * Ω) * ∑ d ∈ divisors n A, (1 : ℝ) / d.totient := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (((1 + ε₁) * n / U7153.zz n) * Ω) *
        (Mphi (√(n : ℝ) / log n ^ (A + 1)) * log (√(n : ℝ) / log n ^ (A + 1))) :=
      mul_le_mul_of_nonneg_left htot (mul_nonneg hB hΩ)
    _ = _ := by ring

/-- Apply the existing Lemma 8 after identifying a slice bilinear form, pp. 1239 and 1240.
CONDITIONAL ON Lemma 8, the finite identification and the stated correction bound. -/
theorem slice_remainder_of_lemma8 (n j : ℕ) (A ε₁ X Y Z D C : ℝ)
    (c : ℕ → ℂ) (h8 : Decomp148a.Lemma8J) (hG : ChenThresholdGRH.GRH)
    (hc : ∀ m, ‖c m‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hbal : √(X * Y) / D ≤ Decomp148a.cutoff Y)
    (hcut : Decomp148a.cutoff Y ≤ min D (√Z)) (hev : Even n)
    (hId : (∑ d ∈ divisors n A, |reducedResidue n j d ε₁|) ≤
      Decomp148a.bilinear c X Y Z D (n : ℤ))
    (hCorrection : (∑ d ∈ divisors n A, badCount n j d ε₁ / d.totient) ≤ C) :
    (∑ d ∈ divisors n A, |residueError n ε₁ j d|) ≤
      Decomp148a.mJ X Y D * Decomp148a.scale X Y D + C := by
  have hevZ : Even (n : ℤ) := by exact_mod_cast hev
  exact (slice_remainder_split n j A ε₁).trans
    (add_le_add (hId.trans (h8 hG c X Y Z D n hc hX hY hZ hZY hD hDX hbal hcut hevZ)) hCorrection)

end
end LeanLab.BS2022GRH.SliceRemainder236

#print axioms LeanLab.BS2022GRH.SliceRemainder236.residue_split
#print axioms LeanLab.BS2022GRH.SliceRemainder236.residue_abs_le
#print axioms LeanLab.BS2022GRH.SliceRemainder236.large_prime_coprime
#print axioms LeanLab.BS2022GRH.SliceRemainder236.divisor_spec
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_large_coprime
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_not_coprime_iff
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_remainder_split

#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_pair_product_injective
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_fiber_le
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_fiber_le_uniform
#print axioms LeanLab.BS2022GRH.SliceRemainder236.badCount_le

#print axioms LeanLab.BS2022GRH.SliceRemainder236.correction_sum_of_omega_phi
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_remainder_of_lemma8
