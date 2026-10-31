/-
I-0030. Almost equal binary Goldbach gives almost equal ternary Goldbach, with no other input.
If every even m in a range is p + q with |p − m/2| ≤ r, then every odd n in that range is
p₁ + p₂ + p₃ with every |pᵢ − n/3| ≤ 3r/2 + 1. The prime near n/3 comes from the binary
hypothesis itself, applied at m = 2⌊n/3⌋.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; the hypothesis here is stronger than binary Goldbach.
-/
import Mathlib
import LeanLab.Ternary.AlmostEqual

namespace LeanLab.Ternary

/-- `m` is a sum of two primes, each within `r` of `m/2`. -/
def IsAlmostEqualBinary (m : ℕ) (r : ℝ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m ∧ |(p : ℝ) - m / 2| ≤ r

/-- Both summands are within `r` of `m/2`. -/
theorem IsAlmostEqualBinary.abs_snd {m p q : ℕ} {r : ℝ} (hs : p + q = m)
    (h : |(p : ℝ) - m / 2| ≤ r) : |(q : ℝ) - m / 2| ≤ r := by
  have hs' : (p : ℝ) + q = m := by exact_mod_cast hs
  have : (q : ℝ) - m / 2 = -((p : ℝ) - m / 2) := by linarith
  rw [this, abs_neg]; exact h

/-- One step: a prime `p₃` near `n/3` and an almost equal binary representation of `n − p₃`
give an almost equal ternary representation of `n`. -/
theorem almostEqualTernary_of_binary_step {n p₃ : ℕ} {g r : ℝ} (hp₃ : p₃.Prime)
    (hle : p₃ ≤ n) (hg : |(p₃ : ℝ) - n / 3| ≤ g) (hb : IsAlmostEqualBinary (n - p₃) r) :
    IsAlmostEqualTernary n (max g (r + g / 2)) := by
  obtain ⟨p, q, hp, hq, hs, hr⟩ := hb
  have hq' := IsAlmostEqualBinary.abs_snd hs hr
  have hm : ((n - p₃ : ℕ) : ℝ) = n - p₃ := by push_cast [Nat.cast_sub hle]; ring
  rw [hm] at hr hq'
  refine ⟨p, q, p₃, hp, hq, hp₃, by omega, ?_, ?_, le_max_of_le_left hg⟩
  · apply le_max_of_le_right
    have e : (p : ℝ) - n / 3 = ((p : ℝ) - (n - p₃) / 2) - ((p₃ : ℝ) - n / 3) / 2 := by ring
    rw [e]
    calc |((p : ℝ) - (n - p₃) / 2) - ((p₃ : ℝ) - n / 3) / 2|
        ≤ |(p : ℝ) - (n - p₃) / 2| + |((p₃ : ℝ) - n / 3) / 2| := abs_sub _ _
      _ ≤ r + g / 2 := by
          rw [abs_div, abs_two]; linarith
  · apply le_max_of_le_right
    have e : (q : ℝ) - n / 3 = ((q : ℝ) - (n - p₃) / 2) - ((p₃ : ℝ) - n / 3) / 2 := by ring
    rw [e]
    calc |((q : ℝ) - (n - p₃) / 2) - ((p₃ : ℝ) - n / 3) / 2|
        ≤ |(q : ℝ) - (n - p₃) / 2| + |((p₃ : ℝ) - n / 3) / 2| := abs_sub _ _
      _ ≤ r + g / 2 := by
          rw [abs_div, abs_two]; linarith

/-- Uniform transfer. If every even `m` with `M₀ ≤ m ≤ n` is an almost equal binary sum
with window `r`, and `n` is odd and large compared with `r` and `M₀`, then `n` is an almost
equal ternary sum with window `3r/2 + 1`. -/
theorem almostEqualTernary_of_binary {n M₀ : ℕ} {r : ℝ} (ho : Odd n) (hr0 : 0 ≤ r)
    (H : ∀ m : ℕ, Even m → M₀ ≤ m → m ≤ n → IsAlmostEqualBinary m r)
    (h1 : (M₀ : ℝ) + r + 1 ≤ n / 2) (h2 : r + 3 ≤ n / 3) :
    IsAlmostEqualTernary n (3 * r / 2 + 1) := by
  set k := n / 3 with hk
  have hk3 : 3 * k ≤ n ∧ n < 3 * k + 3 := ⟨Nat.mul_div_le n 3, by omega⟩
  have hkR1 : (3 * k : ℝ) ≤ n := by exact_mod_cast hk3.1
  have hkR2 : (n : ℝ) < 3 * k + 3 := by exact_mod_cast hk3.2
  have hn9 : (9 : ℝ) ≤ n := by linarith
  have hM : M₀ ≤ 2 * k := by
    have : (M₀ : ℝ) ≤ 2 * k := by linarith
    exact_mod_cast this
  obtain ⟨p, q, hp, hq, hs, hr⟩ := H (2 * k) (even_two_mul k) hM (by omega)
  have hkk : ((2 * k : ℕ) : ℝ) / 2 = k := by push_cast; ring
  rw [hkk, abs_le] at hr
  have hple : p ≤ n := by omega
  have hg : |(p : ℝ) - n / 3| ≤ r + 1 := by
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  -- p is odd: p ≥ k − r > 2
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : (k : ℝ) ≤ 2 + r := by push_cast at hr; linarith [hr.1]
    linarith
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hmEven : Even (n - p) := by
    obtain ⟨a, ha⟩ := ho; obtain ⟨b, hb⟩ := hpodd
    exact ⟨a - b, by omega⟩
  have hmM : M₀ ≤ n - p := by
    have hpR : (p : ℝ) ≤ k + r := by linarith [hr.2]
    have : (M₀ : ℝ) ≤ (n : ℝ) - p := by linarith
    have h' : ((n - p : ℕ) : ℝ) = n - p := by push_cast [Nat.cast_sub hple]; ring
    exact_mod_cast (h' ▸ this)
  have hb := H (n - p) hmEven hmM (Nat.sub_le n p)
  have step := almostEqualTernary_of_binary_step hp hple hg hb
  refine isAlmostEqualTernary_mono ?_ step
  apply max_le <;> linarith

/-- Almost equal binary Goldbach with window `m^θ` for every large even `m`. Stronger than
binary Goldbach, which is OPEN; no such theorem is known for any θ < 1. -/
def AlmostEqualBinaryGoldbach (θ : ℝ) : Prop :=
  ∃ M₀ : ℕ, ∀ m : ℕ, Even m → M₀ ≤ m → IsAlmostEqualBinary m ((m : ℝ) ^ θ)

theorem isAlmostEqualBinary_mono {m : ℕ} {r r' : ℝ} (h : r ≤ r')
    (H : IsAlmostEqualBinary m r) : IsAlmostEqualBinary m r' := by
  obtain ⟨p, q, hp, hq, hs, hr⟩ := H
  exact ⟨p, q, hp, hq, hs, hr.trans h⟩

/-- Asymptotic transfer, assuming the window is eventually small against `n`. -/
theorem almostEqualTernary_of_binaryGoldbach {θ : ℝ} (hθ : 0 ≤ θ)
    (H : AlmostEqualBinaryGoldbach θ)
    (hsmall : ∀ M₀ : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (M₀ : ℝ) + (n : ℝ) ^ θ + 1 ≤ n / 2 ∧ (n : ℝ) ^ θ + 3 ≤ n / 3) :
    ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n →
      IsAlmostEqualTernary n (3 * (n : ℝ) ^ θ / 2 + 1) := by
  obtain ⟨M₀, hM⟩ := H
  obtain ⟨N₀, hN⟩ := hsmall M₀
  refine ⟨N₀, fun n ho hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  refine almostEqualTernary_of_binary ho (Real.rpow_nonneg (Nat.cast_nonneg n) θ) (fun m hm hMm hmn => ?_) h1 h2
  exact isAlmostEqualBinary_mono
    (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) hθ) (hM m hm hMm)

/-- For `θ < 1` the side condition of the asymptotic transfer holds. -/
theorem hsmall_of_lt_one {θ : ℝ} (hθ1 : θ < 1) (M₀ : ℕ) : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    (M₀ : ℝ) + (n : ℝ) ^ θ + 1 ≤ n / 2 ∧ (n : ℝ) ^ θ + 3 ≤ n / 3 := by
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (-(1 - θ))) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(1 - θ)) < 1 / 12 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max X (12 * (M₀ : ℝ) + 36))
  refine ⟨N₀, fun n hn => ?_⟩
  have hnR : max X (12 * (M₀ : ℝ) + 36) ≤ n := hN₀.trans (by exact_mod_cast hn)
  have hnX : X ≤ n := (le_max_left _ _).trans hnR
  have hnM : 12 * (M₀ : ℝ) + 36 ≤ n := (le_max_right _ _).trans hnR
  have hnpos : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg M₀ : (0 : ℝ) ≤ M₀)]
  have key : (n : ℝ) ^ θ ≤ n / 12 := by
    have e : (n : ℝ) ^ θ = n * (n : ℝ) ^ (-(1 - θ)) := by
      rw [show θ = 1 + -(1 - θ) by ring, Real.rpow_add hnpos, Real.rpow_one]
      ring_nf
    rw [e]
    have := hX n hnX
    nlinarith
  constructor <;> linarith [(Nat.cast_nonneg M₀ : (0 : ℝ) ≤ M₀)]

/-- Headline: almost equal binary Goldbach with any exponent `θ` in `[0, 1)` implies almost
equal ternary Goldbach with window `3n^θ/2 + 1`, hence `AlmostEqualVinogradov θ'` for every
`θ' > θ`. No short-interval prime input is needed. The hypothesis is OPEN for every θ < 1. -/
theorem almostEqualTernary_of_binaryGoldbach' {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : AlmostEqualBinaryGoldbach θ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n →
      IsAlmostEqualTernary n (3 * (n : ℝ) ^ θ / 2 + 1) :=
  almostEqualTernary_of_binaryGoldbach hθ H (hsmall_of_lt_one hθ1)

end LeanLab.Ternary

#print axioms LeanLab.Ternary.almostEqualTernary_of_binaryGoldbach'
#print axioms LeanLab.Ternary.almostEqualTernary_of_binary
