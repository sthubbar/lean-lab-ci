/-
P0069 Baker Harman Pintz 1997, Section 5, pages 43 to 53. A split of the OPEN leaf
`upper_normalized_raw_conditions_slack` of UpperShortC165Leaves that follows the paper's own route
for b1 on page 53: Lemma 34 for g, h, j and Lemma 33 for the kept part of k give 5.1 and 5.2,
Lemma 29 turns them into 5.18, and the prime number theorem gives the local density behind 5.17 and
the constant v1. The rescaling `lam` is no longer left free: it is built here as
`lam = (v1 + delta) / D` from the local density profile `D` of the raw weight, which is the only
choice that makes the main term constant on J, and every later leaf is stated for that shape.
The principal half of 1.8 is PROVED in Prep1121UpslackPrincipal from the density leaf, and the
non-principal half of 1.9 is split along Lemmas 33, 34 and 29 in Prep1121UpslackLemma29.
This replaces the main split SPLIT_upper_normalized_raw_conditions_slack, whose two leaves are
QUESTIONS: `upper_slack_split_slack_distribution` is asked for every bounded `lam >= 1`, which
looks false already at a constant `lam = 2`, unproved here, and
`upper_slack_split_mean_square_transfer` asks for 1.9 at moduli up to Q from 1.8 at moduli up
to a power of log x, which the paper never does.
New file, no new definition, the sealed statement is untouched.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1121UpslackPrincipal
import LeanLab.BHP1997.Prep1121UpslackLemma29

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 page 53, the display for v1 "from the prime number theorem", with 5.17 on page 51
read for b1. The raw page 53 weight has a local density profile `D x m` over `log Y`: `D` is
bounded below by a positive constant, varies by at most `K / Y` per unit step on J, tends to
v1 = w(1/c4)/c4 plus the integral over E uniformly on J, and the prefix sums of the raw weight
minus `D / log Y` over J are `O(Y L^-A)` for every `A`. This is the prime number theorem with error
term `Y exp(-eps L^(1/2))` applied to the products of primes in g, h, j and the kept part of k,
together with the Buchstab integrals; a citation wall in the paper. HARD. -/
theorem upslack_raw_local_density
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (D : ℝ → ℕ → ℝ) (c K : ℝ), 0 < c ∧ (∀ x m, c ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  sorry

/-- LEAF: P0069 page 3 display 1.8 for a non-principal character modulo `q <= L^A`, for the
coefficient `(v / D) b1`. The density term carries `delta chi = 0`. By partial summation against
the bounded slowly varying factor `v / D` it reduces to the twisted prefix sums of b1, which are
`O(Y L^-A)` by the Siegel Walfisz theorem applied to g, h, j and the kept part of k, each a sum
over products of primes at least `Y^c1` of a rough indicator. The paper leaves this implicit in
"from the prime number theorem". HARD. -/
theorem upslack_nonprincipal_prefix
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 52, 5.17 to 5.23, the principal character in 1.9 for the coefficient
`(v / D) b1`. Lemma 29 at the smaller `T2` gives 5.19, combined with 5.17 it gives 5.20, the proof
of 4.4 gives 5.21, and 5.22 and 5.23 follow; here the main term `v / log Y` per integer is matched
because the factor `v / D` cancels the local density `D / log Y` of b1 from the density leaf.
HARD. -/
theorem upslack_principal_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) *
                (1 : DirichletCharacter ℂ q) (m : ZMod q) -
              Thm2.delta (1 : DirichletCharacter ℂ q) * (v : ℂ) /
                Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
          C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 53 with U-1624: once `D <= v` the rescaling `v / D` is at least one. PROVED. -/
theorem upslack_lam_ge_one {v c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hdv : d ≤ v) :
    1 ≤ v / d := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  rw [le_div_iff₀ hd]; linarith

/-- Page 3 display 1.8 for `(v / D) b1`, by cases on the character: the principal case is the
PROVED `upslack_principal_prefix_split` of Prep1121UpslackPrincipal, the non-principal case is the
leaf. PROVED from the leaf. -/
theorem upslack_short_distribution
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    Task308.ShortDistribution ε v (upperNormCoeff ε (fun x m => v / D x m)) := by
  intro A hA
  obtain ⟨C1, h1⟩ := upslack_principal_prefix_split hε hε8 v hc hDc hDLip hDpre hA
  obtain ⟨C2, h2⟩ := upslack_nonprincipal_prefix hε hε8 v hc hDc hDLip hA
  refine ⟨max (max C1 C2) 1, ?_⟩
  intro x hx q hq hqx χ t ht
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1' : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2' : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hR : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hmono : ∀ {c' : ℝ}, c' ≤ max (max C1 C2) 1 →
      c' * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    intro c' hc'
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hc' hR
  by_cases hχ : χ = 1
  · exact le_trans (h1 x hx1' q hq hqx χ hχ t ht)
      (hmono (le_trans (le_max_left _ _) (le_max_left _ _)))
  · have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
    have h := le_trans (h2 x hx2' q hq hqx χ hχ t ht)
      (hmono (le_trans (le_max_right _ _) (le_max_left _ _)))
    simpa only [hd, zero_mul, zero_div, sub_zero] using h

/-- Page 3 display 1.9 for `(v / D) b1`, assembled from the non-principal mean square, proved
in Prep1121UpslackLemma29 from its leaves, and the principal mean square leaf: the sum over the characters outside `E_q` is the sum over those other than the
principal one, plus the principal term when it is outside `E_q`. PROVED from the two leaves. -/
theorem upslack_short_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    Task308.ShortMeanSquare ε v (upperNormCoeff ε (fun x m => v / D x m)) := by
  obtain ⟨E, hE⟩ := upslack_nonprincipal_mean_square_split h4 h9 hε hε8 v hc hDc hDLip
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C1, h1⟩ := hE A hA
  obtain ⟨C2, h2⟩ := upslack_principal_mean_square h4 h9 hε hε8 v hc hDc hDLip hDpre hA
  set M := max (max C1 C2) 1 with hM
  have hC1 : C1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM1 : 1 ≤ M := le_max_right _ _
  refine ⟨2 * M, fun x hx q hq hqQ => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hxM : M ≤ x := by linarith
  obtain ⟨hcard, hms⟩ := h1 x (le_trans hC1 hxM) q hq hqQ
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hq0 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hL _)
  have hR : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg hL _)
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · calc ((E A x q).card : ℝ) ≤ C1 * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := hcard
      _ ≤ 2 * M * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
        rw [mul_assoc, mul_assoc (2 * M)]
        exact mul_le_mul_of_nonneg_right (by linarith) hq0
  have hb1 := hms z hz1 hz2
  have hb2 := h2 x (le_trans hC2 hxM) q hq hqQ z hz1 hz2
  have e : ∀ c' : ℝ, c' * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) =
      c' * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := fun c' => by
    ring
  rw [e] at hb1 hb2 ⊢
  have k1 := mul_le_mul_of_nonneg_right hC1 hR
  have k2 := mul_le_mul_of_nonneg_right hC2 hR
  by_cases hmem : (1 : DirichletCharacter ℂ q) ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q
  · rw [← Finset.add_sum_erase _ _ hmem]
    linarith
  · rw [Finset.erase_eq_of_notMem hmem] at hb1
    nlinarith

/-- The target `upper_normalized_raw_conditions_slack` of UpperShortC165Leaves, verbatim, from the
leaves above. Take the local density profile `D` of b1 from the density leaf, set
`lam = (v1 + delta) / D`, which is bounded by `|v1 + delta| / c` and at least one on J once
`D <= v1 + delta`, and get 1.8 and 1.9 at the slack density `v1 + delta` from the two assemblies.
The target declaration is not used. -/
theorem upslack_route
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  obtain ⟨D, c, K, hc, hDc, hDLip, hDconv, hDpre⟩ :=
    upslack_raw_local_density h4 h9 hω hz hε hε8
  set v := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
    upperDeletedIntegral ω ε + δ with hv
  obtain ⟨X, hX⟩ := hDconv δ hδ
  refine ⟨fun x m => v / D x m, |v| / c, fun x m => upslack_lam_bound hc hDc x m,
    ⟨X, fun x hx m hm => upslack_lam_ge_one hc (hDc x m) (hX x hx m hm)⟩,
    upslack_short_distribution hε hε8 v hc hDc hDLip hDpre,
    upslack_short_mean_square h4 h9 hε hε8 v hc hDc hDLip hDpre⟩

end LeanLab.BHP1997.DecompC165d
