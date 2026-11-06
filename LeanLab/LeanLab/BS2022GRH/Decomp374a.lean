/- AI wrote this Lean code for CODEX task374. Goldbach is open.
The two separate large sieve moments behind journal display 15, p. 1225.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.PNTPort.LargeSieve.Bilinear

namespace LeanLab.BS2022GRH.Decomp374a
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The moduli in one dyadic block, journal p. 1225 display 15. -/
def blockModuli (R : ℝ) : Finset ℕ :=
  (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ))

/-- Primitive characters in that block, journal p. 1225 display 15. -/
def blockCharacters (R : ℝ) : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
  (blockModuli R).sigma (fun r =>
    (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive))

/-- One quadratic moment with the standard r over phi r weight, display 15. -/
def blockEnergy (R : ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ blockCharacters R, ((i.1 : ℝ) / i.1.totient) *
    ‖∑ n ∈ S, a n * i.2 n‖ ^ 2

/-- LEAF. Journal p. 1225 display 15, the first large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the coefficients restricted by n coprime to s.
This is one quadratic factor, not the bilinear block estimate. -/
theorem coefficient_energy (c : ℕ → ℂ) (X R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hR : 1 ≤ R) :
    blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c ≤
      (X + 4 * R ^ 2) * X := by
  sorry

/-! ### Private helpers for `prime_energy`

The second large-sieve moment is the lab's `multiplicative_large_sieve` (constant `N + 2Q²`)
applied to the indicator of the primes `Z ≤ p < ⌈Y⌉`. The exact constant `N + Q²` is not
available, so the factor two is recovered from the elementary fact that every prime counted
is at least `25`, hence odd: at most half of the integers up to `⌈Y⌉` are counted. -/

/-- The canonical inclusion `P ⊆ ℤ` agrees with the `Ioc` interval index set. -/
private lemma transfer_set (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) :
    (Ioc (0:ℤ) (0 + (m : ℕ))).filter (fun n => (n.toNat : ℕ) ∈ P)
      = P.image (fun p : ℕ => (p : ℤ)) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨hn0, hnm⟩, hp⟩
    exact ⟨n.toNat, hp, Int.toNat_of_nonneg (le_of_lt hn0)⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, by simpa using hp⟩
    · exact_mod_cast hpos p hp
    · have := hlt p hp
      push_cast
      omega

/-- `χ` applied to a nonnegative integer through `ℤ` or through `ℕ` agree. -/
private lemma char_cast (r : ℕ) (χ : DirichletCharacter ℂ r) (n : ℤ) (hn : 0 ≤ n) :
    χ ((n.toNat : ℕ)) = χ n := by
  have h : ((n.toNat : ℕ) : ZMod r) = (n : ZMod r) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
  exact congrArg χ h

/-- The interval sum of the indicator of `P` is the character sum over `P`. -/
private lemma sum_transfer (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) (r : ℕ) (χ : DirichletCharacter ℂ r) :
    (∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
        (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n) = ∑ p ∈ P, χ p := by
  have h1 : ∀ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
      (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n
        = if ((n.toNat : ℕ) ∈ P) then χ n.toNat else 0 := by
    intro n hn
    rw [ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [char_cast r χ n (le_of_lt (mem_Ioc.mp hn).1)]
    · rfl
  rw [sum_congr rfl h1, ← sum_filter, transfer_set P m hpos hlt]
  have hinj : Set.InjOn (fun p : ℕ => (p : ℤ)) (↑P) := fun a _ b _ h => by simpa using h
  rw [Finset.sum_image (f := fun n : ℤ => χ n.toNat) (g := fun p : ℕ => (p : ℤ)) hinj]
  push_cast
  rfl

/-- The squared norms of the indicator sum to the cardinality of `P`. -/
private lemma sum_norm_sq_indicator (P : Finset ℕ) (m : ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hlt : ∀ p ∈ P, p < m) :
    (∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)), ‖(if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0)‖ ^ 2)
      = (P.card : ℝ) := by
  have h1 : ∀ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
      ‖(if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0)‖ ^ 2
        = if ((n.toNat : ℕ) ∈ P) then (1:ℝ) else 0 := by
    intro n hn
    split_ifs with h <;> simp
  rw [sum_congr rfl h1, ← sum_filter, transfer_set P m hpos hlt]
  rw [sum_const, card_image_of_injective _ (fun a b h => by simpa using h), nsmul_eq_mul, mul_one]

/-- A prime `p ≥ 25` is odd. -/
private lemma odd_of_prime_ge (p : ℕ) (Z : ℝ) (hp : p.Prime) (hZ : 25 ≤ Z)
    (hge : Z ≤ (p : ℝ)) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    norm_num at hge
    linarith
  · exact h

/-- Primes `25 ≤ Z ≤ p < ⌈Y⌉` are at most half of the integers up to `Y`. -/
private lemma prime_card_le (P : Finset ℕ) (Y Z : ℝ) (m : ℕ) (hm : m = ⌈Y⌉₊)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hprime : ∀ p ∈ P, p.Prime) (hge : ∀ p ∈ P, Z ≤ (p:ℝ))
    (hlt : ∀ p ∈ P, p < m) : (P.card : ℝ) ≤ Y / 2 := by
  have hmY : (m : ℝ) ≤ Y + 1 := by
    rw [hm]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hsub : P ⊆ (Ico 12 ((m - 2) / 2 + 1)).image (fun k => 2 * k + 1) := by
    intro p hp
    have hodd := odd_of_prime_ge p Z (hprime p hp) hZ (hge p hp)
    have h25 : 25 ≤ p := by
      have h' : (25:ℝ) ≤ (p:ℝ) := le_trans hZ (hge p hp)
      exact_mod_cast h'
    have hpm : p < m := hlt p hp
    rw [mem_image]
    refine ⟨(p - 1) / 2, ?_, ?_⟩
    · rw [mem_Ico]
      omega
    · omega
  have hcard : P.card ≤ ((m - 2) / 2 + 1) - 12 := by
    refine (card_le_card hsub).trans ?_
    rw [card_image_of_injective _ (fun a b h => by omega), Nat.card_Ico]
  have hmhalf : (((m - 2) / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
    have h1 : ((m - 2) / 2 : ℕ) ≤ m / 2 := Nat.div_le_div_right (by omega)
    have h2 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      push_cast
      exact_mod_cast Nat.div_mul_le_self m 2
    exact le_trans (by exact_mod_cast h1) h2
  rcases Nat.lt_or_ge ((m - 2) / 2 + 1) 12 with h | h
  · have hz : ((m - 2) / 2 + 1) - 12 = 0 := by omega
    rw [hz] at hcard
    have hP0 : P.card = 0 := by omega
    rw [hP0]
    push_cast
    linarith
  · have hstep : ((((m - 2) / 2 + 1) - 12 : ℕ) : ℝ) = ((m - 2) / 2 : ℕ) - 11 := by
      have he : (((m - 2) / 2 + 1) - 12 : ℕ) = (m - 2) / 2 - 11 := by omega
      rw [he, Nat.cast_sub (by omega)]
      push_cast
      ring
    have hcard' : (P.card : ℝ) ≤ ((m - 2) / 2 : ℕ) - 11 := by
      calc (P.card : ℝ) ≤ ((((m - 2) / 2 + 1) - 12 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = ((m - 2) / 2 : ℕ) - 11 := hstep
    have hm2 : (m : ℝ) / 2 ≤ (Y + 1) / 2 := by linarith
    linarith

/-- The block energy, read as a double sum, is dominated by the lab's multiplicative
large-sieve sum over moduli `≤ Q`. -/
private lemma block_energy_le_ls (P : Finset ℕ) (m Mr Q : ℕ) (R : ℝ) (hQ : Q + 1 = Mr)
    (hMr : Mr = ⌈2 * R⌉₊) (hpos : ∀ p ∈ P, 0 < p) (hlt : ∀ p ∈ P, p < m) :
    (∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      ≤ ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
  have hsub : blockModuli R ⊆ Ico 1 Mr := by
    intro r hr
    rw [blockModuli, mem_filter, mem_Ico] at hr
    rw [mem_Ico]
    rw [hMr]
    omega
  have hpt : ∀ r : ℕ, (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
            (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
    intro r
    apply sum_congr rfl
    intro χ hχ
    rw [sum_transfer P m hpos hlt r χ]
  calc (∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2)
      = ∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 :=
        sum_congr rfl (fun r _ => hpt r)
    _ ≤ ∑ r ∈ Ico 1 Mr, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive),
            ((r : ℝ) / r.totient) * ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => ?_)
        apply sum_nonneg
        intro χ _
        positivity
    _ = ∑ r ∈ Ico 1 Mr, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2 := by
        apply sum_congr rfl
        intro r _
        exact (hpt r).symm
    _ = ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Ioc (0:ℤ) (0 + (m : ℕ)),
              (if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) * χ n‖ ^ 2 := by
        rw [← hQ, Finset.sum_Ico_eq_sum_range]
        apply sum_congr rfl
        intro k _
        rw [show 1 + k = k + 1 by omega, hpt, mul_sum]

/-- LEAF. Journal p. 1225 display 15, the second large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the prime indicator with p not dividing s.
This factor has no arbitrary coefficient sequence. -/
theorem prime_energy (Y Z R : ℝ) (s : ℕ)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) ≤
      (Y + 4 * R ^ 2) * Y := by
  set P : Finset ℕ := (pRange Y Z).filter (fun p => ¬ p ∣ s) with hPdef
  set m : ℕ := ⌈Y⌉₊ with hmdef
  set Mr : ℕ := ⌈2 * R⌉₊ with hMrdef
  set Q : ℕ := Mr - 1 with hQdef
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  -- membership facts for the prime block
  have hmem : ∀ p ∈ P, p ∈ range m ∧ p.Prime ∧ Z ≤ (p : ℝ) := by
    intro p hp
    rw [hPdef, mem_filter, pRange, mem_filter, mem_range] at hp
    exact ⟨by rw [hmdef]; exact mem_range.mpr hp.1.1, hp.1.2.1, hp.1.2.2⟩
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (hmem p hp).2.1
  have hge : ∀ p ∈ P, Z ≤ (p : ℝ) := fun p hp => (hmem p hp).2.2
  have hltP : ∀ p ∈ P, p < m := fun p hp => mem_range.mp (hmem p hp).1
  have hposP : ∀ p ∈ P, 0 < p := fun p hp => (hprime p hp).pos
  -- ceiling arithmetic
  have hmMr : 2 ≤ Mr := by
    have h2R : (2:ℝ) ≤ 2 * R := by linarith
    have : (2:ℕ) ≤ ⌈2 * R⌉₊ := by
      have h' : (2:ℝ) ≤ (⌈2 * R⌉₊ : ℝ) := le_trans h2R (Nat.le_ceil (2 * R))
      exact_mod_cast h'
    rw [hMrdef]; exact this
  have hQ1 : 1 ≤ Q := by omega
  have hQsucc : Q + 1 = Mr := by omega
  have hQcast : (Q : ℝ) = (Mr : ℝ) - 1 := by
    rw [hQdef, Nat.cast_sub (show 1 ≤ Mr by omega)]
    push_cast
    ring
  have hMrlt : (Mr : ℝ) < 2 * R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hQlt : (Q : ℝ) < 2 * R := by rw [hQcast]; linarith
  -- the two moments
  have hEQ : blockEnergy R P (fun _ => 1)
      = ∑ r ∈ blockModuli R, ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
          (fun χ => χ.IsPrimitive), ((r : ℝ) / r.totient) * ‖∑ p ∈ P, χ p‖ ^ 2 := by
    rw [blockEnergy, blockCharacters, sum_sigma]
    simp only [one_mul]
  have hstep := block_energy_le_ls P m Mr Q R hQsucc hMrdef hposP hltP
  have hLS := LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve (Q := Q) hQ1
    (fun n : ℤ => if ((n.toNat : ℕ) ∈ P) then (1:ℂ) else 0) 0 m
  have hcard := sum_norm_sq_indicator P m hposP hltP
  have hpc := prime_card_le P Y Z m hmdef hY hZ hprime hge hltP
  rw [hEQ]
  refine hstep.trans ?_
  refine hLS.trans ?_
  rw [hcard]
  -- final constant comparison
  have hmY : (m : ℝ) ≤ 2 * Y := by
    have : (m : ℝ) ≤ Y + 1 := by
      rw [hmdef]; exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
    linarith
  have hP0 : (0:ℝ) ≤ (P.card : ℝ) := by positivity
  have hA0 : (0:ℝ) ≤ (m : ℝ) + 2 * (Q : ℝ) ^ 2 := by positivity
  have hA : (m : ℝ) + 2 * (Q : ℝ) ^ 2 ≤ 2 * Y + 8 * R ^ 2 := by
    have hsq : (Q : ℝ) ^ 2 < (2 * R) ^ 2 := by
      have := hQlt
      nlinarith [hR0]
    nlinarith
  have hB0 : (0:ℝ) ≤ 2 * Y + 8 * R ^ 2 := by positivity
  have hmul := mul_le_mul hA hpc hP0 hB0
  nlinarith [hmul]

/-- Weighted Cauchy Schwarz before the two analytic moments, journal display 15. -/
theorem block_cauchy (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ) (hR : 1 ≤ R) :
    (∑ r ∈ blockModuli R, (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √(blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1)) / R := by
  let f : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * i.2 n‖
  let g : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), i.2 p‖
  let w : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    (i.1 : ℝ) / i.1.totient
  have hRp : 0 < R := by linarith
  have hcs := LeanLab.PNTPort.LargeSieve.cs_weighted (blockCharacters R) w f g
    (fun _ _ => by dsimp [w]; positivity)
  have hsq : (∑ i ∈ blockCharacters R, w i * (f i * g i)) ^ 2 ≤
      blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    simpa only [blockEnergy, w, f, g, one_mul] using hcs
  have hroot := Real.le_sqrt_of_sq_le hsq
  apply le_trans _ (div_le_div_of_nonneg_right hroot hRp.le)
  rw [sum_div]
  change _ ≤ ∑ i ∈ (blockModuli R).sigma (fun r =>
      (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive)),
      w i * (f i * g i) / R
  rw [sum_sigma]
  apply sum_le_sum
  intro r hr
  rw [primitiveTerm, mul_sum]
  apply sum_le_sum
  intro χ hχ
  change (r.totient : ℝ)⁻¹ * (_ * _) ≤
    ((r : ℝ) / r.totient) * (_ * _) / R
  have hrr : R ≤ (r : ℝ) := (mem_filter.mp hr).2
  have hφ : (0 : ℝ) ≤ (r.totient : ℝ)⁻¹ := by positivity
  have hweight : (r.totient : ℝ)⁻¹ ≤ ((r : ℝ) / r.totient) / R := by
    apply (le_div_iff₀ hRp).mpr
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hrr hφ
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right hweight (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Exact statement of Decomp148c.dyadic_block, assembled from the two separate moments.
CONDITIONAL ON coefficient_energy and prime_energy. No direct sorry. -/
theorem dyadic_block (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    (∑ r ∈ (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R := by
  apply (block_cauchy c X Y Z R s hR).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Real.sqrt_le_sqrt
  have ha := coefficient_energy c X R s hc hX hR
  have hb := prime_energy Y Z R s hY hZ hZY hR
  have hnon : 0 ≤ blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    unfold blockEnergy
    exact sum_nonneg (fun _ _ => by positivity)
  have hx : 0 ≤ (X + 4 * R ^ 2) * X := by positivity
  convert mul_le_mul ha hb hnon hx using 1 <;> ring

end
end LeanLab.BS2022GRH.Decomp374a

#print axioms LeanLab.BS2022GRH.Decomp374a.coefficient_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.prime_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.block_cauchy
#print axioms LeanLab.BS2022GRH.Decomp374a.dyadic_block
