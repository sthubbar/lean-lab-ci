import LeanLab.MissingDigit.SingularSeries

/-!
Elementary digit constructions for the upper bound audit of Kim section 1.3.
A block of ones with zero digits between them avoids every digit b at least 2.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.MissingDigit.KimSeries

/-- r ones in base g, separated by L minus 1 zero digits. -/
def blockOnes (g L : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => g ^ (L * r) + blockOnes g L r

/-- The block lies strictly below the next available digit position. -/
theorem blockOnes_lt {g L : ℕ} (hg : 2 ≤ g) (hL : 1 ≤ L) :
    ∀ r : ℕ, blockOnes g L r < g ^ (L * r) := by
  intro r
  induction r with
  | zero => simp [blockOnes]
  | succ r ih =>
    rw [blockOnes, Nat.mul_succ, pow_add]
    have hpow : 2 ≤ g ^ L := le_trans hg (Nat.le_self_pow (by omega) g)
    nlinarith

/-- All nonzero digits of the block are 1. -/
theorem blockOnes_noDigit {g b L : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) (hL : 1 ≤ L) :
    ∀ r : ℕ, NoDigit g b (blockOnes g L r) := by
  intro r
  induction r with
  | zero => exact md_zero g b
  | succ r ih =>
    rw [blockOnes, md_pow_add hg hb _ _ (blockOnes_lt hg hL r)]
    exact ih

/-- If each block position is 1 modulo M, the block is its number of ones modulo M. -/
theorem blockOnes_modEq {g L M : ℕ} (h : g ^ L ≡ 1 [MOD M]) :
    ∀ r : ℕ, blockOnes g L r ≡ r [MOD M] := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [blockOnes, pow_mul]
    simpa only [one_pow, Nat.add_comm 1 r] using (h.pow r).add ih

/-- Multiplication by a power of the base appends only zero digits. -/
theorem noDigit_pow_mul {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (k n : ℕ) :
    NoDigit g b (g ^ k * n) ↔ NoDigit g b n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, md_mul_base hg hb, ih]

/-- Digit restricted even multiples of any modulus coprime to the base. -/
theorem digit_multiple_quarter {g b M : ℕ} (hg : 3 ≤ g) (hge : Even g)
    (hb : 2 ≤ b) (hM : 2 ≤ M) (hcop : Nat.Coprime g M) (T : ℕ) :
    ∃ r m : ℕ, T ≤ r ∧ 1 ≤ r ∧
      m ∈ (starSet g b (g ^ (4 * r)) ((g ^ (3 * r) : ℕ) : ℝ)).filter Even ∧ M ∣ m := by
  let L := M.totient
  have hL : 1 ≤ L := Nat.totient_pos.mpr (by omega)
  have hperiod : g ^ L ≡ 1 [MOD M] := Nat.ModEq.pow_totient hcop
  let r := L * M * (T + 1)
  let c := g ^ L * blockOnes g L (M - 1)
  let m := g ^ (4 * r) + c
  have hLM : 1 ≤ L * M := by nlinarith
  have hLMr : L * M ≤ r := by
    simpa [r] using Nat.mul_le_mul_left (L * M) (show 1 ≤ T + 1 by omega)
  have hr : 1 ≤ r := le_trans hLM hLMr
  have hTr : T ≤ r := by
    have h := Nat.mul_le_mul_right (T + 1) hLM
    dsimp [r]
    nlinarith
  have hcp : 0 < c := by
    dsimp [c]
    have hgL : 0 < g ^ L := by positivity
    have hblock : 0 < blockOnes g L (M - 1) := by
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (show M - 1 ≠ 0 by omega)
      rw [ha, blockOnes]
      positivity
    exact Nat.mul_pos hgL hblock
  have hcLM : c < g ^ (L * M) := by
    have h := Nat.mul_lt_mul_of_pos_left (blockOnes_lt (g := g) (by omega) hL (M - 1))
      (show 0 < g ^ L by positivity)
    have hexp : L + L * (M - 1) = L * M := by
      have hsub : M - 1 + 1 = M := by omega
      nlinarith
    simpa only [c, ← pow_add, hexp] using h
  have hc3 : c < g ^ (3 * r) := lt_of_lt_of_le hcLM
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hc4 : c < g ^ (4 * r) := lt_of_lt_of_le hc3
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hnd : NoDigit g b c := by
    change NoDigit g b (g ^ L * blockOnes g L (M - 1))
    rw [noDigit_pow_mul (by omega) (by omega)]
    exact blockOnes_noDigit (by omega) hb hL (M - 1)
  have hmemb : m ∈
      (starSet g b (g ^ (4 * r)) ((g ^ (3 * r) : ℕ) : ℝ)).filter Even := by
    simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
    refine ⟨⟨⟨by dsimp [m]; omega, by dsimp [m]; omega⟩, ?_⟩, ?_⟩
    · exact (md_pow_add (by omega) hb (4 * r) c hc4).mpr hnd
    · have hx : Even (g ^ (4 * r)) := hge.pow_of_ne_zero (by omega)
      have hc : Even c := (hge.pow_of_ne_zero (by omega : L ≠ 0)).mul_right _
      exact hx.add hc
  have hcmod : c ≡ M - 1 [MOD M] := by
    simpa only [c, one_mul] using hperiod.mul (blockOnes_modEq hperiod (M - 1))
  have hxmod : g ^ (4 * r) ≡ 1 [MOD M] := by
    have h := hperiod.pow (4 * M * (T + 1))
    have hexp : L * (4 * M * (T + 1)) = 4 * r := by dsimp [r]; ring
    simpa only [← pow_mul, hexp, one_pow] using h
  have hmmod : m ≡ M [MOD M] := by
    have hsub : 1 + (M - 1) = M := by omega
    simpa only [m, hsub] using hxmod.add hcmod
  refine ⟨r, m, hTr, hr, hmemb, ?_⟩
  exact Nat.modEq_zero_iff_dvd.mp
    (hmmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl M)))

end LeanLab.MissingDigit.KimSeries
