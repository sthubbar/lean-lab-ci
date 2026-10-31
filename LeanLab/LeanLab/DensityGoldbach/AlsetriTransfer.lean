/-
P0085 A. Alsetri 2025, Density ternary Goldbach for primes in a fixed residue class,
arXiv 2505.09648 v3, read 2026-10-17 (WebFetch). How Theorem 1.1 follows from Theorem 1.2.

Section 4, Proposition 4.1 (transference principle, restated by the author from Shao [4]):
N a sufficiently large prime, ν_i, f_i : Z_N → R^+ (i = 1, 2, 3) with
  (4.1) 0 ≤ f_i ≤ ν_i;
  (4.2) min(δ₁, δ₂, δ₃, δ₁ + δ₂ + δ₃ − 1) ≥ δ > 0, where δ_i = Σ_{x ∈ Z_N} f_i(x);
  (4.3) |ν̂_i(r) − δ_{r,0}| ≤ η for all r;
  (4.4) ‖f̂_i‖_q ≤ M for some 2 < q < 3;
with f̂(r) = Σ_n f(n) e_N(rn). If η = η(δ, M, q) is small enough, then for every x ∈ Z_N,
  Σ_{y,z} f₁(y) f₂(z) f₃(x − y − z) ≥ c(δ)/N.
Stated below as `AlsetriProp41`, cited with sorry as `alsetri_prop_4_1`.

Section 5 (proof of Theorem 1.1) is NOT elementary given Prop 4.1 and Theorem 1.2: with
W = ∏_{p ≤ z} p, z = z(δ), m = W/2, it builds
  f(b) = max( (3 φ(W) / 2n) Σ_{x ∈ A ∩ [1, 2n/3], x ≡ b (W)} log x − δ/8, 0 )
and needs the prime number theorem in arithmetic progressions (to get Σ f > φ(W)/4 and the
r = 0 case of (4.3)), Green's Lemma 6.6 (Lemma 5.1, for (4.4)), Green's Lemma 6.2
(Lemma 5.2, |ν̂_i(r)| ≤ 2 log log z / z for r ≠ 0, for (4.3)), and a prime N in
[(1+κ)n/W, (1+2κ)n/W]. None of that is formalized here.

What IS proved, zero sorry: the paper's combinatorial skeleton of Section 5. `AlsetriSection5`
packages exactly the analytic output of Section 5 steps 1-3 and 6-9 (lab packaging, not a
quoted statement): for A as in Theorem 1.1 there is z ≥ 3 such that, with m = z#/2, for all
large odd n ≡ 0 mod 3 there is f : Z_m → [0,1] satisfying the hypotheses of Theorem 1.2, and
every triple b₁ + b₂ + b₃ ≡ n (mod m) of units that Theorem 1.2's conclusion produces gives
n ∈ A + A + A. Then `alsetri_1_1_of_section5 : AlsetriSection5 → Alsetri11` uses
`alsetri12_proved` (m = z#/2 is odd, squarefree, divisible by 3; n ≡ 0 mod 3 gives the
residue n mod m class 0 mod 3). The lift mod 2 ("since n is odd, n ≡ b₁+b₂+b₃ (mod W)") is
inside the analytic package.

Note: Lemma 5.1 is applied with p = 3, but (4.4) needs 2 < q < 3; Lemma 5.1 holds for every
p > 2, so q = 5/2 works. Harmless.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem; binary Goldbach is OPEN.
-/
import LeanLab.DensityGoldbach.Alsetri2025
import LeanLab.DensityGoldbach.AlsetriFull

open Finset

noncomputable section
namespace LeanLab.DensityGoldbach

/-- The Fourier transform on `Z_N`, `f̂(r) = Σ_n f(n) e(rn/N)`. -/
def fourierZN (N : ℕ) [NeZero N] (f : ZMod N → ℝ) (r : ZMod N) : ℂ :=
  ∑ n : ZMod N, (f n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (r.val * n.val : ℕ) / N)

/-- **P0085 Proposition 4.1** (transference, from Shao [4]), quantifiers as in the paper:
`c` depends on `δ` only; `η` small in terms of `δ, M, q`; `N` a sufficiently large prime. -/
def AlsetriProp41 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ, 2 < q → q < 3 → ∀ M : ℝ, 0 < M →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ ν f : Fin 3 → ZMod N → ℝ,
        (∀ i x, 0 ≤ f i x ∧ f i x ≤ ν i x) →                                   -- (4.1)
        (∀ i, δ ≤ ∑ x, f i x) → δ ≤ (∑ x, f 0 x) + (∑ x, f 1 x) + (∑ x, f 2 x) - 1 → -- (4.2)
        (∀ i r, ‖fourierZN N (ν i) r - (if r = 0 then 1 else 0)‖ ≤ η) →          -- (4.3)
        (∀ i, (∑ r, ‖fourierZN N (f i) r‖ ^ q) ^ (1 / q) ≤ M) →                    -- (4.4)
        ∀ x : ZMod N, c / N ≤ ∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z)

/-- Cited: Alsetri arXiv 2505.09648 v3, Proposition 4.1 (Shao, arXiv 1206.6139). -/
theorem alsetri_prop_4_1 : AlsetriProp41 := by sorry

/-- The analytic output of Section 5 of P0085 (lab packaging; see header). `m = z#/2`. -/
def AlsetriSection5 : Prop := ∀ A : Set ℕ, A ⊆ P → (∀ a ∈ A, a % 3 = 1) →
  1 / 2 < lowerDensityRes A 1 3 →
  ∃ z : ℕ, 3 ≤ z ∧ ∀ (m : ℕ) [NeZero m], m = primorial z / 2 →
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → Odd n → n % 3 = 0 →
      ∃ f : ZMod m → ℝ, (∀ a, 0 ≤ f a ∧ f a ≤ 1) ∧ (∀ a, a.val % 3 ≠ 1 → f a = 0) ∧
        (m.totient : ℝ) / 4 < ∑ a ∈ unitsMod m, f a ∧
        ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
          (n : ZMod m) = b₁ + b₂ + b₃ → 0 < f b₁ → 0 < f b₂ → 0 < f b₃ →
          3 / 2 < f b₁ + f b₂ + f b₃ → IsSum3 A A A n

lemma prime_dvd_primorial {p z : ℕ} (hp : p.Prime) (hz : p ≤ z) : p ∣ primorial z :=
  Finset.dvd_prod_of_mem _ (by simp [Finset.mem_filter, hp]; omega)

/-- For `z ≥ 3`, `m = z#/2` is odd, squarefree and divisible by `3`. -/
lemma half_primorial_props {z : ℕ} (hz : 3 ≤ z) :
    0 < primorial z / 2 ∧ Odd (primorial z / 2) ∧ Squarefree (primorial z / 2) ∧
      3 ∣ primorial z / 2 := by
  have h2 := prime_dvd_primorial Nat.prime_two (by omega : 2 ≤ z)
  have h3 := prime_dvd_primorial Nat.prime_three hz
  have hsq := squarefree_primorial z
  obtain ⟨m, hm⟩ := h2
  have hm2 : primorial z / 2 = m := by rw [hm]; omega
  rw [hm2]
  have hsqm : Squarefree (2 * m) := hm ▸ hsq
  refine ⟨?_, ?_, hsqm.of_mul_right, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hm; exact (primorial_pos z).ne' hm
    · exact h
  · rcases Nat.even_or_odd m with ⟨k, hk⟩ | h
    · exfalso
      have := hsqm 2 ⟨k, by rw [hk]; ring⟩
      have h21 := Nat.isUnit_iff.mp this
      omega
    · exact h
  · rw [hm] at h3
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

/-- **Theorem 1.1 from the analytic package of Section 5 and Theorem 1.2**, zero sorry. -/
theorem alsetri_1_1_of_section5 (H : AlsetriSection5) : Alsetri11 := by
  intro A hA h1 hd
  obtain ⟨z, hz, hH⟩ := H A hA h1 hd
  obtain ⟨hpos, hodd, hsq, h3⟩ := half_primorial_props hz
  set m := primorial z / 2 with hmdef
  have : NeZero m := ⟨hpos.ne'⟩
  obtain ⟨N₀, hN⟩ := hH m rfl
  refine ⟨N₀, fun n hn hno hn3 => ?_⟩
  obtain ⟨f, hf, hsupp, hsum, hfin⟩ := hN n hn hno hn3
  have hx : (n : ZMod m).val % 3 = 0 := by
    rw [ZMod.val_natCast]
    have : 3 ∣ n % m := (Nat.dvd_mod_iff h3).mpr (Nat.dvd_of_mod_eq_zero hn3)
    omega
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, p₁, p₂, p₃, hs⟩ :=
    alsetri12_proved m hodd hsq h3 f hf hsupp hsum (n : ZMod m) hx
  exact hfin b₁ hb₁ b₂ hb₂ b₃ hb₃ he p₁ p₂ p₃ hs

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri_1_1_of_section5
#print axioms LeanLab.DensityGoldbach.half_primorial_props
#print axioms LeanLab.DensityGoldbach.alsetri_prop_4_1
