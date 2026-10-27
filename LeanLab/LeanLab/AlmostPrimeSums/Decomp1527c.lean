/-
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176. Unit U-1527, run 20261025T2003Z-426, type
DECOMPOSE, file c of three.

Chen's lower bound from the linear sieve, in the switching form of Bordignon-Johnston-
Starichkova (arXiv 2207.09452, Lemma 37, Theorems 44, 50, 51, Lemma 52; Nathanson, Additive
Number Theory: The Classical Bases, Theorem 10.2) with `z = N^{1/8}`, `y = N^{1/3}`, sieve
level `D = N^{1/2}/(log N)^B`, and the normalisation `M(N) = 2e^γ U_N N / log² N`, so that
`S(A,P(z)) ≈ 2 log 3 · M`, `½ Σ_q S(A_q,P(z)) ≈ log 6 · M`, `½ S(B,P(y)) ≈ c̄ · M`,
`c̄ = ∫_{1/8}^{1/3} log(2-3β)/(β(1-β)) dβ = 0.3630837`, margin `log(3/2) − c̄ = 0.0423814`.
Chen's own cut-off is `z = N^{1/10}` with sharper weights and gives `0.67`; the `N^{1/8}` form
is the shortest complete route and is what the existing lab file `Chen1973.lean` uses.

The level of distribution enters as two explicit hypotheses:
* `LevelBV`: the Bombieri-Vinogradov theorem for primes, level `x^{1/2}/(log x)^B`
  (Iwaniec-Kowalski Theorem 17.1; Halberstam-Richert ch. 3; Davenport ch. 28), with
  `π(y)/φ(q)` in place of `li(y)/φ(q)`, which changes the sum by `O(x e^{-c√log x} log x)`;
* `LevelBVTriples`: the Bombieri-Vinogradov theorem for the Chen sequence
  `m = p₁p₂p₃`, `N^{1/8} ≤ p₁ < N^{1/3} ≤ p₂ ≤ p₃`, `m < N`, `(m, N) = 1`, the input of the
  switching principle (Bombieri's theorem for convolutions, Motohashi 1976; Pan-Ding-Wang 1975;
  Halberstam-Richert ch. 11; Iwaniec-Kowalski Theorem 17.4).
The assemblies `chen_lower_conditional` and `chen_conditional` are CONDITIONAL ON both.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.ChenExplicit.Bridge
import LeanLab.ChenExplicit.Reductions
import LeanLab.AlmostPrimeSums.Decomp1527b
import LeanLab.ChenExplicit.BJSCbar

namespace LeanLab.AlmostPrimeSums.Decomp1527c
open Finset Real Filter Topology LeanLab.ChenExplicit
attribute [local instance] Classical.propDecidable

/-! ### Definitions -/

/-- `π(y; q, a)`: primes `p ≤ y` with `p ≡ a (mod q)`. -/
noncomputable def primesAP (y q a : ℕ) : ℕ :=
  #((range (y + 1)).filter fun p => p.Prime ∧ p % q = a % q)

/-- **Bombieri-Vinogradov, level `x^{1/2}/(log x)^B`**: for every `A > 0` there are `B, C` with
`Σ_{q ≤ √x/(log x)^B} max_{y ≤ x} max_{(a,q)=1} |π(y;q,a) − π(y)/φ(q)| ≤ C x/(log x)^A`
for all `x ≥ 2`; the maxima are written as arbitrary choices `y q ≤ x`, `(a q, q) = 1`.
Iwaniec-Kowalski Theorem 17.1; Davenport ch. 28. -/
def LevelBV : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ x : ℕ, 2 ≤ x → ∀ y a : ℕ → ℕ,
    (∀ q, y q ≤ x) → (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Icc 1 ⌊√(x : ℝ) / log x ^ B⌋₊,
      |(primesAP (y q) q (a q) : ℝ) - (Nat.primeCounting (y q) : ℝ) / (q.totient : ℝ)|
      ≤ C * x / log x ^ A

/-- Chen's switched sequence `T`: `m = p₁p₂p₃ < N`, `(m, N) = 1`, `z ≤ p₁ < y ≤ p₂ ≤ p₃`;
`B = {N − m : m ∈ T}` is the lab's `BSet`, BJS (108). -/
noncomputable def TSet (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (range N).filter fun m => Nat.Coprime m N ∧ ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
    z ≤ p₁ ∧ (p₁ : ℝ) < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧ m = p₁ * p₂ * p₃

/-- **Bombieri-Vinogradov for the Chen sequence `T` at `z = N^{1/8}`, `y = N^{1/3}`**: for every
`A > 0` there are `B, C` with
`Σ_{q ≤ √N/(log N)^B} max_{(a,q)=1} |#{m ∈ T : m ≡ a (q)} − #{m ∈ T : (m,q)=1}/φ(q)| ≤ C N/(log N)^A`.
Motohashi 1976; Iwaniec-Kowalski Theorem 17.4; Halberstam-Richert ch. 11. -/
def LevelBVTriples : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
    ∑ q ∈ Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊,
      |(#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
          fun m => m % q = a q % q) : ℝ)
        - (#((TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter
          fun m => Nat.Coprime m q) : ℝ) / (q.totient : ℝ)|
      ≤ C * N / log N ^ A

/-- The normalisation `M(N) = 2 e^γ U_N N / log² N = 4 C_N N / log² N`. -/
noncomputable def Mchen (N : ℕ) : ℝ :=
  2 * exp eulerMascheroniConstant * U N * N / log N ^ 2

/-- `M(N) > 0` for `N ≥ 2`. -/
theorem Mchen_pos (N : ℕ) (hN : 2 ≤ N) : 0 < Mchen N := by
  unfold Mchen
  have hU := U_pos N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  positivity

/-! ### Switching bookkeeping -/

/-- LEAF. Switching: `B = {N − m : m ∈ T}` as finite sets, from the definitions of `BSet`,
`InB` and `TSet`, BJS (108). Nathanson Theorem 10.2 proof; Halberstam-Richert ch. 11, p. 338.
Unit U-1527. -/
theorem bset_eq_image (N : ℕ) (z y : ℝ) :
    BSet N z y = (TSet N z y).image (fun m => N - m) := by
  ext b
  simp only [BSet, InB, TSet, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨hbN, ⟨p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, hlt, hcop, rfl⟩⟩
    refine ⟨p1 * p2 * p3, ⟨hlt, hcop, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, rfl⟩, rfl⟩
  · rintro ⟨m, ⟨hmN, hcop, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, rfl⟩, rfl⟩
    have hpos : 0 < p1 * p2 * p3 := Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos
    have h1 : N - p1 * p2 * p3 < N := Nat.sub_lt (by omega) hpos
    refine ⟨h1, p1, p2, p3, hp1, hp2, hp3, hz, hy1, hy2, hy3, hmN, hcop, rfl⟩

/-- LEAF. Switching: `|B| = |T|`, since `m ↦ N − m` is injective on `m < N`.
Halberstam-Richert ch. 11, p. 338. Unit U-1527. -/
theorem card_bset (N : ℕ) (z y : ℝ) : #(BSet N z y) = #(TSet N z y) := by
  rw [bset_eq_image N z y, card_image_of_injOn]
  intro a ha b hb hab
  dsimp only at hab
  have h1 : a < N := by
    have := (mem_filter.1 ha).1
    exact mem_range.1 this
  have h2 : b < N := by
    have := (mem_filter.1 hb).1
    exact mem_range.1 this
  omega

/-- LEAF. Switching of divisibility into congruence, the heart of Chen's switching principle:
`#{b ∈ B : d ∣ b} = #{m ∈ T : m ≡ N (mod d)}`, because `d ∣ N − m ↔ m ≡ N (mod d)` for `m ≤ N`.
Halberstam-Richert ch. 11, p. 338 bookkeeping. Unit U-1527. -/
theorem card_bset_dvd (N : ℕ) (z y : ℝ) (d : ℕ) :
    #((BSet N z y).filter (d ∣ ·)) = #((TSet N z y).filter fun m => m % d = N % d) := by
  rw [bset_eq_image N z y]
  rw [filter_image]
  have H : ((TSet N z y).filter fun x => d ∣ N - x) = (TSet N z y).filter fun m => m % d = N % d := by
    apply filter_congr
    intro x hx
    have h1 : x ≤ N := by
      have := (mem_filter.1 hx).1
      exact le_of_lt (mem_range.1 this)
    have hdvd : d ∣ N - x ↔ x ≡ N [MOD d] := (Nat.modEq_iff_dvd' h1).symm
    have hmodeq : x ≡ N [MOD d] ↔ x % d = N % d := Iff.rfl
    rw [hdvd, hmodeq]
  rw [H]
  apply card_image_of_injOn
  intro a ha b hb hab
  dsimp only at hab
  have h1 : a < N := by
    have := (mem_filter.1 (mem_filter.1 ha).1).1
    exact mem_range.1 this
  have h2 : b < N := by
    have := (mem_filter.1 (mem_filter.1 hb).1).1
    exact mem_range.1 this
  omega

/-- LEAF. On `B`, sifting by the primes `r < y` with `r ∤ N` is the same as sifting by all
primes `r < y`: if `r ∣ N` and `r ∣ N − m` then `r ∣ m`, against `(m, N) = 1`. BJS (109).
Unit U-1527. -/
theorem siftedBy_iff_of_mem_bset {N : ℕ} {z y : ℝ} {b : ℕ} (hb : b ∈ BSet N z y) :
    SiftedBy N y b ↔ ∀ r : ℕ, r.Prime → (r : ℝ) < y → ¬ r ∣ b := by
  unfold SiftedBy
  constructor
  · intro h r hr hy hrb
    by_cases hN : r ∣ N
    · have hInB : InB N z y b := (mem_filter.1 hb).2
      obtain ⟨p1, p2, p3, hp1, hp2, hp3, hz1, hz2, hy2, hy3, hlt, hcop, rfl⟩ := hInB
      have h1 : r ∣ N - p1 * p2 * p3 := hrb
      have h2 : r ∣ p1 * p2 * p3 := by
        have h3 : p1 * p2 * p3 + (N - p1 * p2 * p3) = N := by omega
        have h4 : r ∣ p1 * p2 * p3 + (N - p1 * p2 * p3) := by
          rw [h3]
          exact hN
        exact (Nat.dvd_add_left h1).mp h4
      have h3 : r ∣ Nat.gcd (p1 * p2 * p3) N := Nat.dvd_gcd h2 hN
      have h4 : Nat.gcd (p1 * p2 * p3) N = 1 := hcop
      rw [h4] at h3
      exact hr.not_dvd_one h3
    · exact h r hr hy hN hrb
  · intro h r hr hy hN hrb
    exact h r hr hy hrb

/-- LEAF. Sieve setup for `A = {N − p}`: `|A_d| = #{p < N : p ∤ N, d ∣ N − p}` equals
`π(N−1; d, N)` up to at most `ω(N)` primes `p ∣ N`. BJS (105), (107); Halberstam-Richert
ch. 11, p. 338. Unit U-1527. -/
theorem card_A_dvd (N d : ℕ) :
    #((range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p) ≤ primesAP (N - 1) d N ∧
    primesAP (N - 1) d N ≤
      #((range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p) + N.primeFactors.card := by
  by_cases hN0 : N = 0
  · subst hN0; unfold primesAP;
    have h1 : ((range 0).filter fun p => p.Prime ∧ ¬p ∣ 0 ∧ d ∣ 0 - p) = ∅ := filter_false_of_mem (by intro x hx; simp at hx)
    have h2 : ((range 1).filter fun p => p.Prime ∧ p % d = 0 % d) = ∅ := by
      apply filter_false_of_mem
      intro x hx
      simp only [mem_range] at hx
      have : x = 0 := by omega
      subst this
      intro h
      have : Nat.Prime 0 := h.1
      exact Nat.not_prime_zero this
    rw [h1, h2]; simp
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
  unfold primesAP
  have hr : range (N - 1 + 1) = range N := by
    ext x
    simp only [mem_range]
    omega
  rw [hr]

  set S := (range N).filter fun p => p.Prime ∧ p % d = N % d
  set S1 := (range N).filter fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p

  have H1 : S1 ⊆ S := by
    intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨hp.1, hp.2.1, ?_⟩
    have h1 : p ≤ N := le_of_lt (mem_range.1 hp.1)
    have h2 : p ≡ N [MOD d] := (Nat.modEq_iff_dvd' h1).mpr hp.2.2.2
    exact h2

  have H2 : S \ S1 ⊆ N.primeFactors := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    rw [Nat.mem_primeFactors]
    obtain ⟨hp_in_S, hp_not_S1⟩ := hp
    rw [mem_filter] at hp_in_S
    obtain ⟨hp1, hp2, hp3⟩ := hp_in_S
    have h1 : p ≤ N := le_of_lt (mem_range.1 hp1)
    have h2 : p ≡ N [MOD d] := hp3
    have h3 : d ∣ N - p := (Nat.modEq_iff_dvd' h1).mp h2
    have h4 : p ∣ N := by
      by_contra hn
      have : p ∈ S1 := by
        rw [mem_filter]
        exact ⟨hp1, hp2, hn, h3⟩
      exact hp_not_S1 this
    exact ⟨hp2, h4, hN_pos.ne.symm⟩

  constructor
  · exact card_mono H1
  · have H3 : S ⊆ S1 ∪ N.primeFactors := by
      intro p hp
      by_cases h : p ∈ S1
      · rw [mem_union]
        left
        exact h
      · rw [mem_union]
        right
        have : p ∈ S \ S1 := by
          rw [Finset.mem_sdiff]
          exact ⟨hp, h⟩
        exact H2 this
    calc
      #S ≤ #(S1 ∪ N.primeFactors) := card_mono H3
      _ ≤ #S1 + #N.primeFactors := card_union_le _ _

/-- LEAF. The remainder of the sieve on `A` is controlled by `LevelBV`: for every `A > 0`
there are `B, C` with `Σ_{d ≤ √N/(log N)^B, (d,N)=1} |π(N−1; d, N) − π(N−1)/φ(d)| ≤ C N/(log N)^A`.
Take `y q = N − 1`, `a q = N` when `(N, q) = 1`. Iwaniec-Kowalski Theorem 17.1;
Halberstam-Richert ch. 11. Unit U-1527. -/
theorem remainder_of_levelBV (h : LevelBV) :
    ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
        ≤ C * N / log N ^ A := by
  intro A hA
  unfold LevelBV at h
  obtain ⟨B, C, hBC⟩ := h A hA
  use B, C
  intro N hN
  have h1 : ∀ d : ℕ, N - 1 ≤ N := fun d => by omega

  set a : ℕ → ℕ := fun q => if Nat.Coprime q N then N else 1
  have ha : ∀ q, Nat.Coprime (a q) q := by
    intro q
    unfold a
    split_ifs with h_cop
    · exact h_cop.symm
    · exact Nat.coprime_one_left q

  have h3 := hBC N hN (fun d => N - 1) a h1 ha

  have h4 : ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
      ≤ ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊),
        |(primesAP (N - 1) d (a d) : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)| := by
    have H : ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d N : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)|
      = ∑ d ∈ (Icc 1 ⌊√(N : ℝ) / log N ^ B⌋₊).filter (fun d => Nat.Coprime d N),
        |(primesAP (N - 1) d (a d) : ℝ) - (Nat.primeCounting (N - 1) : ℝ) / (d.totient : ℝ)| := by
      apply sum_congr rfl
      intro i hi
      have h_cop : Nat.Coprime i N := (mem_filter.1 hi).2
      have ha_eq : a i = N := by
        unfold a
        split_ifs
        · rfl
      rw [ha_eq]
    rw [H]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (mem_filter.1 hx).1
    · intro i _ _
      exact abs_nonneg _
  exact le_trans h4 h3

/-- LEAF. Mertens' product for the twin density: for `0 < θ ≤ 1`, as `N → ∞`,
`∏_{2<p<N^θ, p∤N} (1 − 1/(p−1)) · log N^θ / U_N → 1`; from Mertens' third theorem
`∏_{p<z}(1−1/p) ~ e^{-γ}/log z`, `(p−2)/(p−1) = (1−1/p)(1−1/(p−1)²)`, and at most `1/θ` primes
`p ∣ N` with `p ≥ N^θ`. Halberstam-Richert ch. 2 and ch. 11 p. 339; Iwaniec-Kowalski Section 2.2.
Unit U-1527. -/
theorem mertens_twin (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1) :
    Tendsto (fun N : ℕ =>
      (∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧ (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))) * log ((N : ℝ) ^ θ) / U N) atTop (𝓝 1) := by
  sorry

/-! ### The three sieve estimates, from the linear sieve and the level of distribution -/

/-- LEAF. Lower bound for `S(A, P(z))`, `z = N^{1/8}`: CONDITIONAL ON `LevelBV`, for every
`η > 0` and large even `N`, `S(A,P(z)) ≥ (2 log 3 − η) M(N)`. Apply `Decomp1527b.jr_lower` with
`X = π(N)`, `g(d) = 1/φ(d)` on `d ∣ P(z)`, `D = N^{1/2}/(log N)^B`, `s → 4`,
`f(4) = e^γ log 3/2` (`Decomp1527a.fsieve_four`, continuity), `mertens_twin 1/8`,
`card_A_dvd`, `remainder_of_levelBV`. BJS Theorem 44; Halberstam-Richert Theorem 11.1 proof.
Unit U-1527. -/
theorem SA_lower (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (2 * log 3 - η) * Mchen N ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  sorry

/-- LEAF. Upper bound for `½ Σ_{z≤q<y, q∤N} S(A_q, P(z))`: CONDITIONAL ON `LevelBV`, for every
`η > 0` and large even `N`, `≤ (log 6 + η) M(N)`. Apply `Decomp1527b.jr_upper` to each `A_q`
at level `D/q`, `s_q = 4 − 8 log q/log N ∈ (4/3, 3]`, `F(s_q) = 2e^γ/s_q`, and
`Σ_q 1/(q s_q) → ∫_{1/8}^{1/3} dα/(α(4−8α)) = (log 6)/4`. BJS Theorem 50.
Unit U-1527. -/
theorem sumSAq_upper (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (log 6 + η) * Mchen N := by
  sorry

/-- LEAF. Upper bound for `½ S(B, P(y))`, `y = N^{1/3}`: CONDITIONAL ON `LevelBVTriples`, for
every `η > 0` and large even `N`, `≤ (c̄ + η) M(N)`. Apply `Decomp1527b.jr_upper` to `B` with
`X = |T| ~ c̄ N/log N`, `g(d) = 1/φ(d)`, `s → 3/2`, `F(3/2) = 4e^γ/3`, `mertens_twin 1/3`,
`card_bset_dvd`, `siftedBy_iff_of_mem_bset`. BJS Theorem 51 and Lemma 52; Chen's switching.
Unit U-1527. -/
theorem SB_upper (h : LevelBVTriples) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * Mchen N := by
  sorry

/-- LEAF. The trivial terms of Chen's inequality are small: for every `η > 0`, eventually
`2N^{7/8} + N^{1/3} ≤ η M(N)`, since `U_N ≥ 2e^{-γ} C₂ > 0` and `M(N) ≫ N/log² N`.
BJS Lemma 37 and Section 9. Unit U-1527. -/
theorem error_small :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3) ≤ η * Mchen N := by
  sorry

/-- LEAF. `c̄ = ∫_{1/8}^{1/3} log(2−3β)/(β(1−β)) dβ < 0.3631` (value `0.36308373`). The lab file
`ChenExplicit/BJSCbar.lean` has `BJS.cbar_lt : cbar < 0.363084` for the same integral, so this
is a port. BJS Lemma 52. Unit U-1527. -/
theorem cbar_lt' : (∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) < 0.3631 := by
  have hc := BJS.cbar_lt
  unfold BJS.cbar at hc
  linarith

/-- `log 3 − log 2 > 0.405`. -/
theorem log_three_halves_gt : 0.405 < log 3 - log 2 := by
  have := Real.log_three_gt_d9
  have := Real.log_two_lt_d9
  norm_num at *; linarith

/-! ### Assembly: Chen's lower bound, CONDITIONAL ON the level of distribution -/

/-- **Chen's lower bound, CONDITIONAL ON `LevelBV` and `LevelBVTriples`**: for every large even
`N`, `π₂(N) > M(N)/100 = 0.04 C_N N / log² N`, where `π₂(N) = chenCount N` counts primes
`p < N` with `N − p` a product of at most two primes. Assembled from the leaves `SA_lower`,
`sumSAq_upper`, `SB_upper`, `error_small`, `cbar_lt'` and the PROVED Chen inequality
`ChenExplicit.lemma37`; margin `log(3/2) − c̄ − 4η > 0.405 − 0.3631 − 0.02 > 0.01`. -/
theorem chen_lower_conditional (h1 : LevelBV) (h2 : LevelBVTriples) :
    ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → (1 / 100 : ℝ) * Mchen N < chenCount N := by
  obtain ⟨N1, hA⟩ := SA_lower h1 0.005 (by norm_num)
  obtain ⟨N2, hQ⟩ := sumSAq_upper h1 0.005 (by norm_num)
  obtain ⟨N3, hB⟩ := SB_upper h2 0.005 (by norm_num)
  obtain ⟨N4, hE⟩ := error_small 0.005 (by norm_num)
  refine ⟨max (max N1 N2) (max (max N3 N4) 256), fun N he hN => ?_⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN4 : N4 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN5 : 256 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have l37 := lemma37 N hN5
  have a := hA N he hN1
  have q := hQ N he hN2
  have b := hB N he hN3
  have e := hE N hN4
  have hc := cbar_lt'
  have hl := log_three_halves_gt
  have hM := Mchen_pos N (by omega)
  have h6 : log (6 : ℝ) = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h6] at q
  set M := Mchen N
  set cb := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))
  have hm : 0 ≤ (log 3 - log 2 - cb - 0.03) * M := mul_nonneg (by linarith) hM.le
  nlinarith

/-- **Chen's theorem, CONDITIONAL ON `LevelBV` and `LevelBVTriples`**: every large even `N` is
`p + m` with `p` prime and `m` a product of at most two primes. From `chen_lower_conditional`. -/
theorem chen_conditional (h1 : LevelBV) (h2 : LevelBVTriples) : ∃ T : ℝ, ChenAbove T := by
  obtain ⟨N₀, hN⟩ := chen_lower_conditional h1 h2
  refine ⟨max N₀ 2, fun N he hT => ?_⟩
  have hle : max N₀ 2 ≤ N := by exact_mod_cast hT.le
  have hM := Mchen_pos N (le_of_max_le_right hle)
  have hc := hN N he (le_of_max_le_left hle)
  have hpos' : 0 < chenCount N := by
    have : (0 : ℝ) < chenCount N := by linarith
    exact_mod_cast this
  unfold chenCount at hpos'
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos'
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, N - p, hp.2.1, by omega, hp.2.2⟩

/-- Vacuity of `card_bset_dvd` and `card_A_dvd`: at `N = 10`, `d = 3`, the primes `p < 10`,
`p ∤ 10`, `3 ∣ 10 − p` are `p = 7` only. -/
example : ((range 10).filter fun p => p.Prime ∧ ¬ p ∣ 10 ∧ 3 ∣ 10 - p) = {7} := by
  ext p; simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; interval_cases p <;> norm_num at *
  · rintro rfl; norm_num

end LeanLab.AlmostPrimeSums.Decomp1527c
