/-
Proposition 8.1 of P0029 Bhowmik, Grimmelt, The exceptional set of the Goldbach problem,
arXiv 2607.27282v2, Section 8, page 30, at `ϑ = 5/12`, with the minor arc input of
Maynard, Pandey, Radziwiłł, Exponential sums over primes, arXiv 2608.14777v1, Theorem 1.1,
as a named hypothesis. Unit U-1322, track T1. Proposition 8.1 belongs to P0029, NOT to
P0082 Brüdern-Perelli 1998, under which the unit was filed.

Section 8 of P0029 is not readable here: the arXiv PDF has no text layer, the v2 HTML stops in
Section 2, the v1 HTML stops inside Lemma 7.6. The statement `Prop81` below is the lab's
reconstruction of the exception form of Proposition 8.1, from Sections 4.3, 6 and 7 of the v1
HTML and from the page 30 to 32 reading of unit U-6726, BG2026Sigma.lean. NEED COPY for a
literal check.

The minor arc mechanism, read in Section 4.3 and Lemma 7.3 of the v1 HTML: on the minor arcs
`|S(α)| ≪ (X R^{-1/2} + X^{4/5}) log⁴ X` from Vinogradov, so `Σ |r_𝔪(N)|² ≪ (X²/R + X^{8/5}) X log⁵ X`,
Lemma 4.2, and Lemma 7.3 carries `(R^{-1} + X^{-2/5} + η⁴) X³ log⁵ X`. Chebyshev then gives
`X/R + X^{3/5}` exceptions. With MPR the `X^{4/5}` becomes `X^{19/24+o(1)}`, the `X^{-2/5}` becomes
`X^{-5/12+o(1)}`, and the exceptions `X^{1-ϑ} + X^{7/12}`, balanced at `ϑ = 5/12`.

Named hypotheses, CITED:
* `MPRTheorem11`: MPR Theorem 1.1, unrefereed.
* `MajorPart81 ϑ rMaj`: the major arc half of Proposition 8.1, from Theorem 6.3, Proposition 7.5
  and the Section 8 argument; no minor arc exponent enters it.
* `MinorL2 ϑ κ rMin`: Lemma 4.2 or the minor arc part of Lemma 7.3 with `X^{2κ}` in place of `X^{8/5}`.
  From `MinorArcSup κ` it follows by Parseval as in Lemma 4.2's proof, not done in Lean.

AI wrote this Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.BG2026Sigma

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-! ### The MPR minor arc input -/

/-- `S(α) = Σ_{n<N} Λ(n) e(nα)`. -/
def SΛ (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ range N, (Λ n : ℂ) * Complex.exp (2 * π * Complex.I * ((n : ℂ) * (α : ℂ)))

/-- MPR arXiv 2608.14777v1 Theorem 1.1, CITED: for `α = a/q + β`, `(a, q) = 1`, `q ≤ N^{1/2}`,
`|β| ≤ 1/(q N^{1/2})`, `B = max(q, qN|β|)`: `|S(α)| ≤ N^{o(1)} (N/B^{1/2} + N^{19/24})`. The `N^{o(1)}` is
written `C_ε N^ε` for every `ε > 0`. -/
def MPRTheorem11 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℤ) (q : ℕ) (β : ℝ), 1 ≤ N → 0 < q →
    a.natAbs.Coprime q → (q : ℝ) ≤ Real.sqrt N → |β| ≤ 1 / (q * Real.sqrt N) →
    ‖SΛ N (a / q + β)‖ ≤
      C * (N : ℝ) ^ ε * (N / Real.sqrt (max (q : ℝ) (q * N * |β|)) + (N : ℝ) ^ (19 / 24 : ℝ))

/-- `α` lies on the minor arcs `𝔪(R)`: off every arc `|α - a/q| ≤ R/(qN)`, `q ≤ R`. Taking every
`a`, not only `(a, q) = 1`, gives the same set, since a reduced fraction has a smaller `q` and a
wider arc. -/
def Minor (N : ℕ) (R α : ℝ) : Prop :=
  ∀ (q : ℕ) (a : ℤ), 0 < q → (q : ℝ) ≤ R → R / (q * N) < |α - a / q|

/-- The minor arc sup bound `|S(α)| ≤ C_ε N^ε (N R^{-1/2} + N^κ)` on `𝔪(R)`, Section 4.3 with `N^κ`
for Vinogradov's `N^{4/5}`. -/
def MinorArcSup (κ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (R α : ℝ), 1 ≤ N → 1 ≤ R → Minor N R α →
    ‖SΛ N α‖ ≤ C * (N : ℝ) ^ ε * (N / Real.sqrt R + (N : ℝ) ^ κ)

/-- Dirichlet's theorem with a reduced fraction: `q ≤ ⌊√N⌋`, `(a, q) = 1`, `|α - a/q| ≤ 1/(q√N)`. -/
theorem dirichlet_reduced (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ a.natAbs.Coprime q ∧ (q : ℝ) ≤ Real.sqrt N ∧
      |α - a / q| ≤ 1 / (q * Real.sqrt N) := by
  set Q := Nat.floor (Real.sqrt N) with hQ
  have hsqrt1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hQpos : 0 < Q := Nat.floor_pos.mpr hsqrt1
  obtain ⟨j, k, hk, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hQpos
  set x : ℚ := (j : ℚ) / (k : ℚ) with hx
  have hxden : (x.den : ℤ) ∣ k := by
    have := Rat.den_dvd j k
    rwa [Rat.divInt_eq_div] at this
  have hden_le : (x.den : ℤ) ≤ k := Int.le_of_dvd hk hxden
  have hdenR : (x.den : ℝ) ≤ (k : ℝ) := by exact_mod_cast hden_le
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hQle : (Q : ℝ) ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
  have hQlt : Real.sqrt N < Q + 1 := Nat.lt_floor_add_one _
  have hkQR : (k : ℝ) ≤ Q := by exact_mod_cast hkQ
  have hxR : ((x : ℚ) : ℝ) = (j : ℝ) / (k : ℝ) := by rw [hx]; push_cast; ring
  have hcast : ((x : ℚ) : ℝ) = (x.num : ℝ) / (x.den : ℝ) := Rat.cast_def x
  have hdpos : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  refine ⟨x.num, x.den, x.den_pos, x.reduced, by linarith, ?_⟩
  rw [← hcast, hxR]
  have h1 : |α - j / k| = |k * α - j| / k := by
    rw [show α - j / k = (k * α - j) / k by field_simp]
    rw [abs_div, abs_of_pos hkR]
  rw [h1, div_le_iff₀ hkR]
  have hsq : 0 < Real.sqrt N := by linarith
  calc |(k : ℝ) * α - j| ≤ 1 / (Q + 1) := hjk
    _ ≤ 1 / Real.sqrt N := one_div_le_one_div_of_le hsq hQlt.le
    _ ≤ 1 / (x.den * Real.sqrt N) * k := by
        have e : 1 / (x.den * Real.sqrt N) * k = (k / x.den) * (1 / Real.sqrt N) := by
          field_simp
        rw [e]
        have h1 : 1 ≤ (k : ℝ) / x.den := by rw [le_div_iff₀ hdpos]; linarith
        have h2 : 0 < 1 / Real.sqrt N := one_div_pos.mpr hsq
        nlinarith

/-- The MPR sup bound on the minor arcs, `κ = 19/24`. CONDITIONAL ON `MPRTheorem11`. -/
theorem minorArcSup_of_MPR (h : MPRTheorem11) : MinorArcSup (19 / 24) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, fun N R α hN hR hmin => ?_⟩
  obtain ⟨a, q, hq, hcop, hqN, hβ⟩ := dirichlet_reduced N hN α
  have hα : α = a / q + (α - a / q) := by ring
  have key := hb N a q (α - a / q) hN hq hcop hqN hβ
  rw [← hα] at key
  refine key.trans ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hRB : R ≤ max (q : ℝ) (q * N * |α - a / q|) := by
    by_cases hc : (q : ℝ) ≤ R
    · have := hmin q a hq hc
      rw [div_lt_iff₀ (by positivity)] at this
      exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by linarith)
  have hs : Real.sqrt R ≤ Real.sqrt (max (q : ℝ) (q * N * |α - a / q|)) := Real.sqrt_le_sqrt hRB
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  have hdiv : (N : ℝ) / Real.sqrt (max (q : ℝ) (q * N * |α - a / q|)) ≤ N / Real.sqrt R :=
    div_le_div_of_nonneg_left hNR.le hsR hs
  have hCN : 0 ≤ C * (N : ℝ) ^ ε := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hCN

/-- Vacuity test for `Minor`: `α = 1/2` is on `𝔪(1)` for `N = 4`. -/
theorem vacuity_minor : Minor 4 1 (1 / 2) := by
  intro q a hq hqR
  have hq1 : q = 1 := by
    have : (q : ℝ) ≤ 1 := hqR
    have : q ≤ 1 := by exact_mod_cast this
    omega
  subst hq1
  simp only [Nat.cast_one, div_one, one_mul]
  have : (1 / 2 : ℝ) ≤ |1 / 2 - (a : ℝ)| := by
    rcases le_or_gt a 0 with h | h
    · have : (a : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ a := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
  norm_num at this ⊢; linarith

/-! ### The Chebyshev step and the exception count -/

/-- Chebyshev: `#{i : |f i| > t} ≤ M / t²` when `Σ f² ≤ M`. -/
theorem card_large_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t M : ℝ} (ht : 0 < t)
    (hM : ∑ i ∈ s, f i ^ 2 ≤ M) : ((s.filter (fun i => t < |f i|)).card : ℝ) ≤ M / t ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : ((s.filter (fun i => t < |f i|)).card : ℝ) * t ^ 2 ≤
      ∑ i ∈ s.filter (fun i => t < |f i|), f i ^ 2 := by
    have := Finset.card_nsmul_le_sum (s.filter (fun i => t < |f i|)) (fun i => f i ^ 2) (t ^ 2)
      (fun i hi => by
        rw [mem_filter] at hi
        have := hi.2
        rw [← sq_abs (f i)]
        exact pow_le_pow_left₀ ht.le this.le 2)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ i ∈ s.filter (fun i => t < |f i|), f i ^ 2 ≤ ∑ i ∈ s, f i ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg _)
  linarith

/-- `𝔖(N) ≥ 2 C₀`. -/
theorem Sing_ge (N : ℕ) : 2 * C0 ≤ Sing N := by
  unfold Sing
  have hprod : (1 : ℝ) ≤ ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
    apply Finset.one_le_prod₀
    intro p hp
    rw [mem_filter] at hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have : 0 < (p : ℝ) - 2 := by linarith
    have : 0 ≤ 1 / ((p : ℝ) - 2) := by positivity
    linarith
  have := C0_pos
  nlinarith

/-- `K x^a ≤ x^b` for large `x` when `a < b`. -/
theorem eventually_le_rpow {a b K : ℝ} (hab : a < b) (hK : 0 < K) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x → K * x ^ a ≤ x ^ b := by
  refine ⟨max 1 (K ^ (b - a)⁻¹), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hba : 0 < b - a := by linarith
  have hK' : K ≤ x ^ (b - a) := by
    have h1 : K ^ (b - a)⁻¹ ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 hba.le
    rwa [Real.rpow_inv_rpow hK.le hba.ne'] at h2
  have : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hK' (by positivity)

/-! ### Proposition 8.1, exception form -/

/-- The major arc half of Proposition 8.1 at level `ϑ`, `R = X^ϑ`, CITED. At a primitive real
character `χ̃` mod `r̃`, `X = r̃^A`, `r̃ < R`, with a real zero `β > 1 - c/log X`, the major arc part
`rMaj X N` of `r₂(N)` is `(1 + χ̃(-1) b) 𝔖(N) N + E`, `|b - 1| < 3δ/4`, `|E| ≤ δ/8 𝔖(N) N`, for every even
multiple `N` of `r̃` in `[X/2, X]` outside a set of size at most `X^τ`, any `τ > 1 - ϑ`; those are the
residue classes with large conductor dropped in Section 6, at most `C₁(ε) X^{1-ϑ}`. -/
def MajorPart81 (ϑ : ℝ) (rMaj : ℝ → ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → 1 / A < ϑ →
    ∀ τ : ℝ, 1 - ϑ < τ → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0) →
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ τ ∧
      ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
        |E| ≤ δ / 8 * (Sing N * N) ∧ rMaj ((r : ℝ) ^ A) N = (1 + (χ (-1)).re * b) * (Sing N * N) + E

/-- The minor arc mean square at level `ϑ` with sup exponent `κ`, CITED:
`Σ_{X/2 ≤ N ≤ X} |r_𝔪(N)|² ≤ C_ε X^ε (X^{3-ϑ} + X^{2κ+1})`, Lemma 4.2 with `X^{2κ}` for `X^{8/5}`. -/
def MinorL2 (ϑ κ : ℝ) (rMin : ℝ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMin X N ^ 2 ≤ C * X ^ ε * (X ^ (3 - ϑ) + X ^ (2 * κ + 1))

/-- Proposition 8.1 at level `ϑ` with exception exponent `σ`, the lab's reconstruction of its
exception form: at a Siegel zero of conductor `r̃ < X^ϑ`, all but `X^τ` even multiples `N` of `r̃`
in `[X/2, X]`, any `τ > σ`, have `r₂(N) = (1 + χ̃(-1) b) 𝔖(N) N + E`, `|b - 1| < 3δ/4`, `|E| ≤ δ/4 𝔖(N) N`. -/
def Prop81 (ϑ σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → 1 / A < ϑ →
    ∀ τ : ℝ, σ < τ → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0) →
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ τ ∧
      ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
        |E| ≤ δ / 4 * (Sing N * N) ∧ r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E

/-- Exception count of the minor arcs: at most `K X^{max(1-ϑ, 2κ-1)+ε}` even `N ∈ [X/2, X]` with
`|r_𝔪(N)| > δ/8 𝔖(N) N`. -/
theorem minor_exceptions {ϑ κ : ℝ} {rMin : ℝ → ℕ → ℝ} (hm : MinorL2 ϑ κ rMin) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ) (r : ℕ), 1 ≤ X →
      (((evenMult r X).filter (fun N => δ / 8 * (Sing N * N) < |rMin X N|)).card : ℝ) ≤
        K * X ^ (max (1 - ϑ) (2 * κ - 1) + ε) := by
  obtain ⟨C, hC, hL2⟩ := hm ε hε
  have hC0 := C0_pos
  refine ⟨2 * C / (δ * C0 / 8) ^ 2, by positivity, fun X r hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set t := δ * C0 / 8 * X with ht
  have htpos : 0 < t := by positivity
  have hsub : (evenMult r X).filter (fun N => δ / 8 * (Sing N * N) < |rMin X N|) ⊆
      (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => t < |rMin X N|) := by
    intro N hN
    simp only [evenMult, mem_filter, mem_Icc] at hN ⊢
    refine ⟨hN.1.1, lt_of_le_of_lt ?_ hN.2⟩
    have hNX : X / 2 ≤ N := (Nat.ceil_le).mp hN.1.1.1
    have hS := Sing_ge N
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have : C0 * X ≤ Sing N * N := by nlinarith
    rw [ht]; nlinarith
  have hcard := card_large_le (Icc ⌈X / 2⌉₊ ⌊X⌋₊) (rMin X) htpos (hL2 X hX)
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)
  refine h1.trans (hcard.trans ?_)
  set m := max (1 - ϑ) (2 * κ - 1)
  have hX2 : X ^ (2 : ℝ) = X ^ 2 := by norm_cast
  have e1 : X ^ ε * X ^ (3 - ϑ) ≤ X ^ (m + ε) * X ^ (2 : ℝ) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX (by have := le_max_left (1 - ϑ) (2 * κ - 1); linarith)
  have e2 : X ^ ε * X ^ (2 * κ + 1) ≤ X ^ (m + ε) * X ^ (2 : ℝ) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX (by have := le_max_right (1 - ϑ) (2 * κ - 1); linarith)
  rw [hX2] at e1 e2
  rw [div_le_iff₀ (by positivity), ht]
  have hpos : 0 < X ^ (m + ε) := by positivity
  calc C * X ^ ε * (X ^ (3 - ϑ) + X ^ (2 * κ + 1))
      = C * (X ^ ε * X ^ (3 - ϑ) + X ^ ε * X ^ (2 * κ + 1)) := by ring
    _ ≤ C * (2 * (X ^ (m + ε) * X ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le; linarith
    _ = 2 * C / (δ * C0 / 8) ^ 2 * X ^ (m + ε) * (δ * C0 / 8 * X) ^ 2 := by
        field_simp

/-- Proposition 8.1 from its two halves. CONDITIONAL ON `MajorPart81 ϑ rMaj` and `MinorL2 ϑ κ rMin`,
for any split `r₂ = rMaj + rMin`. Exception exponent `max(1 - ϑ, 2κ - 1)`. -/
theorem prop81_of_parts {ϑ κ : ℝ} {rMaj rMin : ℝ → ℕ → ℝ}
    (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N)
    (hM : MajorPart81 ϑ rMaj) (hm : MinorL2 ϑ κ rMin) : Prop81 ϑ (max (1 - ϑ) (2 * κ - 1)) := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hMA⟩ := hM δ hδ hδ1
  refine ⟨c, hc, fun A hA hAϑ τ hτ => ?_⟩
  set m := max (1 - ϑ) (2 * κ - 1)
  set ε := (τ - m) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hτ' : 1 - ϑ < m + ε := by have := le_max_left (1 - ϑ) (2 * κ - 1); linarith
  obtain ⟨r0, hr0⟩ := hMA A hA hAϑ (m + ε) hτ'
  obtain ⟨K, hK, hKb⟩ := minor_exceptions hm (δ := δ) (ε := ε) hδ hεpos
  obtain ⟨x0, hx01, hx0⟩ := eventually_le_rpow (a := m + ε) (b := τ) (K := 2 * (K + 1))
    (by linarith) (by positivity)
  refine ⟨max r0 ⌈x0 ^ A⁻¹⌉₊, fun r _ hr χ hprim hreal hzero => ?_⟩
  obtain ⟨Bmaj, hBmaj, hmaj⟩ := hr0 r (le_of_max_le_left hr) χ hprim hreal hzero
  set X := (r : ℝ) ^ A with hXdef
  have hrx : x0 ^ A⁻¹ ≤ r := (Nat.ceil_le).mp (le_of_max_le_right hr)
  have hXx : x0 ≤ X := by
    have h := Real.rpow_le_rpow (by positivity) hrx hA.le
    rwa [Real.rpow_inv_rpow (by linarith) hA.ne'] at h
  have hX1 : 1 ≤ X := le_trans hx01 hXx
  have hX0 : 0 < X := by linarith
  set Bmin := (evenMult r X).filter (fun N => δ / 8 * (Sing N * N) < |rMin X N|)
  refine ⟨Bmaj ∪ Bmin, ?_, fun N hN hNB => ?_⟩
  · have h1 := (Nat.cast_le (α := ℝ)).mpr (card_union_le Bmaj Bmin)
    have h2 := hKb X r hX1
    have h3 := hx0 X hXx
    have hp : 0 ≤ X ^ (m + ε) := by positivity
    push_cast at h1
    nlinarith
  · rw [mem_union, not_or] at hNB
    obtain ⟨b, E, hb, hE, hrM⟩ := hmaj N hN hNB.1
    have hmin : |rMin X N| ≤ δ / 8 * (Sing N * N) := by
      by_contra h; push Not at h
      exact hNB.2 (mem_filter.mpr ⟨hN, h⟩)
    refine ⟨b, E + rMin X N, hb, ?_, ?_⟩
    · calc |E + rMin X N| ≤ |E| + |rMin X N| := abs_add_le _ _
        _ ≤ δ / 4 * (Sing N * N) := by linarith
    · rw [hsplit X N, hrM]; ring

/-! ### Where `ϑ` enters: exponent arithmetic -/

/-- With Vinogradov's `κ = 4/5` the exception exponent `max(1 - ϑ, 3/5)` is `3/5` exactly when `ϑ ≥ 2/5`. -/
theorem vinogradov_balance (ϑ : ℝ) : max (1 - ϑ) (2 * (4 / 5) - 1) = 3 / 5 ↔ 2 / 5 ≤ ϑ := by
  constructor
  · intro h; have := le_max_left (1 - ϑ) (2 * (4 / 5 : ℝ) - 1); linarith
  · intro h; rw [max_eq_right (by linarith)]; norm_num

/-- With MPR's `κ = 19/24` the exception exponent `max(1 - ϑ, 7/12)` is `7/12` exactly when `ϑ ≥ 5/12`. -/
theorem mpr_balance (ϑ : ℝ) : max (1 - ϑ) (2 * (19 / 24) - 1) = 7 / 12 ↔ 5 / 12 ≤ ϑ := by
  constructor
  · intro h; have := le_max_left (1 - ϑ) (2 * (19 / 24 : ℝ) - 1); linarith
  · intro h; rw [max_eq_right (by linarith)]; norm_num

/-- `ϑ = 5/12` is inside Theorem 6.3's range `ε < ϑ < 4/9 - ε`, at `ε = 1/72`; it needs `ε < 1/36`. -/
theorem five_twelfths_admissible :
    (0 : ℝ) < 1 / 72 ∧ (1 / 72 : ℝ) < 5 / 12 ∧ (5 / 12 : ℝ) < 4 / 9 - 1 / 72 ∧
      (4 / 9 : ℝ) - 1 / 36 = 5 / 12 := by norm_num

/-- Lemma 7.3 at `ϑ = 5/12`, `η = R^{-1/4}`: the `X^{3-ϑ}` term and the MPR form `X^{2κ+1}` of the
`X^{13/5}` term have the same exponent `31/12`; with Vinogradov they are `X^{3-ϑ}` and `X^{13/5}`. -/
theorem lemma73_exponents : (3 : ℝ) - 5 / 12 = 31 / 12 ∧ 2 * (19 / 24 : ℝ) + 1 = 31 / 12 ∧
    (3 : ℝ) + (-(2 / 5)) = 2 * (4 / 5) + 1 := by norm_num

/-- Section 7's condition `10 R² ≤ η N` with `η = R^{-1/4}` is `10 R^{9/4} ≤ N`, the source of `4/9`. -/
theorem eta_condition {R N : ℝ} (hR : 0 < R) :
    10 * R ^ (2 : ℝ) ≤ R ^ (-(1 / 4) : ℝ) * N ↔ 10 * R ^ (9 / 4 : ℝ) ≤ N := by
  have hu : 0 < R ^ (1 / 4 : ℝ) := by positivity
  have e1 : R ^ (9 / 4 : ℝ) = R ^ (2 : ℝ) * R ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hR]; norm_num
  rw [Real.rpow_neg hR.le, le_inv_mul_iff₀ hu, e1]
  constructor <;> intro h <;> linarith

/-! ### Proposition 8.1 at `ϑ = 5/12` and the chain to Theorem 8.2 -/

/-- Proposition 8.1 at `ϑ = 5/12` with exceptions `X^{7/12+ε}`. CONDITIONAL ON `MajorPart81 (5/12)`
and `MinorL2 (5/12) (19/24)`, the latter being the MPR input in mean square form. -/
theorem prop81_five_twelfths {rMaj rMin : ℝ → ℕ → ℝ}
    (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N)
    (hM : MajorPart81 (5 / 12) rMaj) (hm : MinorL2 (5 / 12) (19 / 24) rMin) :
    Prop81 (5 / 12) (7 / 12) := by
  have h := prop81_of_parts hsplit hM hm
  have e : max (1 - (5 / 12 : ℝ)) (2 * (19 / 24) - 1) = 7 / 12 := by norm_num
  rwa [e] at h

/-- Even multiples of `r` in `[X/2, X]`: at least `X/(4r) - 1`. -/
theorem evenMult_card_ge (r : ℕ) [NeZero r] {X : ℝ} (hX : 0 ≤ X) :
    X / (4 * r) - 1 ≤ ((evenMult r X).card : ℝ) := by
  have hrN : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr : (0 : ℝ) < r := by exact_mod_cast hrN
  set k1 := ⌈X / (4 * r)⌉₊ with hk1d
  set k2 := ⌊X / (2 * r)⌋₊ with hk2d
  have hsub : (Icc k1 k2).image (fun k => 2 * r * k) ⊆ evenMult r X := by
    intro N hN
    simp only [mem_image, mem_Icc] at hN
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hN
    simp only [evenMult, mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨r * k, by ring⟩, ⟨2 * k, by ring⟩⟩
    · rw [Nat.ceil_le]
      have h := (Nat.ceil_le).mp hk1
      rw [div_le_iff₀ (by positivity)] at h
      push_cast; nlinarith
    · apply Nat.le_floor
      have h := (Nat.le_floor_iff (by positivity)).mp hk2
      rw [le_div_iff₀ (by positivity)] at h
      push_cast; linarith
  have hinj : Set.InjOn (fun k : ℕ => 2 * r * k) (Icc k1 k2 : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj, Nat.card_Icc] at hc
  have h1 : (k1 : ℝ) < X / (4 * r) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : X / (2 * r) < k2 + 1 := Nat.lt_floor_add_one _
  have h3 : (k2 : ℝ) + 1 - k1 ≤ ((k2 + 1 - k1 : ℕ) : ℝ) := by
    rcases le_total k1 (k2 + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; rfl
    · rw [Nat.sub_eq_zero_of_le h]
      have : ((k2 + 1 : ℕ) : ℝ) ≤ k1 := by exact_mod_cast h
      push_cast at this ⊢; linarith
  have h4 : X / (2 * r) = 2 * (X / (4 * r)) := by field_simp; ring
  have h5 : ((k2 + 1 - k1 : ℕ) : ℝ) ≤ (evenMult r X).card := by exact_mod_cast hc
  linarith

/-- The page 32 consequence of Proposition 8.1: `Prop81 ϑ σ` gives `Prop81AtMultiplesσ σ` when
`ϑ ≥ 1 - σ`, so that every `A` with `σ < 1 - 1/A` has `r̃ = X^{1/A} < X^ϑ`. PROVED from `Prop81`. -/
theorem prop81AtMultiplesσ_of_prop81 {ϑ σ : ℝ} (hσ0 : 0 ≤ σ) (hϑ : 1 - σ ≤ ϑ)
    (h : Prop81 ϑ σ) : Prop81AtMultiplesσ σ := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hA⟩ := h δ hδ hδ1
  refine ⟨c, hc, fun A hA0 hAσ => ?_⟩
  set τ := (σ + (1 - 1 / A)) / 2 with hτ
  have hAϑ : 1 / A < ϑ := by linarith
  obtain ⟨r0, hr0⟩ := hA A hA0 hAϑ τ (by rw [hτ]; linarith)
  have hAA : A * (1 - 1 / A) = A - 1 := by field_simp
  have hAs : A * σ < A - 1 := by
    have := mul_lt_mul_of_pos_left hAσ hA0; linarith
  have hA1 : 0 < A - 1 := by nlinarith
  have hAt : A * τ < A - 1 := by
    have : A * τ = (A * σ + (A - 1)) / 2 := by rw [hτ, mul_div_assoc', mul_add, hAA]
    rw [this]; linarith
  obtain ⟨x1, hx11, hx1⟩ := eventually_le_rpow (K := 16) hAt (by norm_num)
  obtain ⟨x2, -, hx2⟩ := eventually_le_rpow (K := 16) hAs (by norm_num)
  obtain ⟨x3, -, hx3⟩ := eventually_le_rpow (a := 0) (K := 16) hA1 (by norm_num)
  refine ⟨max r0 ⌈max x1 (max x2 x3)⌉₊, fun r _ hr χ hp hre hz => ?_⟩
  obtain ⟨B, hB, hBN⟩ := hr0 r (le_of_max_le_left hr) χ hp hre hz
  refine ⟨B, ?_, fun N hN hNB => hBN N hN hNB⟩
  have hrx : max x1 (max x2 x3) ≤ r := (Nat.ceil_le).mp (le_of_max_le_right hr)
  have hrx1 : x1 ≤ r := le_trans (le_max_left _ _) hrx
  have hrx2 : x2 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrx
  have hrx3 : x3 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hrx
  have hr1 : (1 : ℝ) ≤ r := le_trans hx11 hrx1
  have hrpos : (0 : ℝ) < r := by linarith
  have e1 : ((r : ℝ) ^ A) ^ τ = (r : ℝ) ^ (A * τ) := (Real.rpow_mul hrpos.le A τ).symm
  have e2 : ((r : ℝ) ^ A) ^ σ = (r : ℝ) ^ (A * σ) := (Real.rpow_mul hrpos.le A σ).symm
  have e3 : (r : ℝ) ^ A / (4 * r) = (r : ℝ) ^ (A - 1) / 4 := by
    rw [Real.rpow_sub_one hrpos.ne']; field_simp
  have hcnt := evenMult_card_ge r (X := (r : ℝ) ^ A) (by positivity)
  rw [e3] at hcnt
  rw [e1] at hB
  rw [e2]
  have i1 := hx1 r hrx1
  have i2 := hx2 r hrx2
  have i3 := hx3 r hrx3
  rw [Real.rpow_zero] at i3
  have : 0 < (r : ℝ) ^ (A - 1) := by positivity
  linarith

/-- Theorem 8.2 with `X^{7/12}` exceptions, `A > 12/5`, from the two halves of Proposition 8.1 at
`ϑ = 5/12`. CONDITIONAL ON `MajorPart81 (5/12) rMaj` and `MinorL2 (5/12) (19/24) rMin`. -/
theorem theorem82σ_seven_twelfths_of_parts {rMaj rMin : ℝ → ℕ → ℝ}
    (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N)
    (hM : MajorPart81 (5 / 12) rMaj) (hm : MinorL2 (5 / 12) (19 / 24) rMin) :
    Theorem82σ (7 / 12) :=
  theorem82σ_of_prop81σ _ (prop81AtMultiplesσ_of_prop81 (by norm_num) (by norm_num)
    (prop81_five_twelfths hsplit hM hm))

/-- Vacuity test for `MinorL2`: the split `rMaj = r₂`, `rMin = 0` satisfies it at every `ϑ`, `κ`. -/
theorem vacuity_minorL2 (ϑ κ : ℝ) : MinorL2 ϑ κ (fun _ _ => 0) := by
  intro ε hε
  refine ⟨1, one_pos, fun X hX => ?_⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
  have : 0 < X := by linarith
  positivity

/-- Vacuity test for the range: `A = 2.45` has `1/A < 5/12`. -/
theorem vacuity_A : (0 : ℝ) < 2.45 ∧ 1 / (2.45 : ℝ) < 5 / 12 := by norm_num

end

end LeanLab.ExceptionalSet.BG2026
