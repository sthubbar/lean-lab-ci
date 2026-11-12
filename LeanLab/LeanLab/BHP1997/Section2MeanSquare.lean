/-
P0069 Baker, Harman, Pintz 1997, Section 2, page 6: the reduction of Theorem 2 to a mean
square bound. ROUTE BURST session 2, step `section2_circle_method`, branch
claude/BHP1997-section2_circle_method.

The paper, page 6: "To prove Theorem 2 it suffices to show that"
  Σ_{2n ∈ K} |∫_{1/Q}^{1+1/Q} S₁(α)S₂(α)e(-2nα) dα - uvY/(ℒℒ') 𝔖(2n)|² ≪ H Y² ℒ^{-A-7},
and the rest of Section 2 proves this display in two stages, 2.2 on the major arcs and
2.3 on the minor arcs. The integral equals the convolution Σ_{k+m=2n} a(k)b(m) by
orthogonality, so the display is stated here with the convolution.

Contents.
* `card_filter_mul_sq_le`, PROVED: the Chebyshev counting step behind "it suffices".
* `two_C2_le_sing`, PROVED: 𝔖(2n) ≥ 2C₂, the lower bound the counting step needs.
* `MeanSquare`, `Conclusion`, `Theorem2With`: the page 6 display, the conclusion of
  Theorem 2, and the hypotheses i to iv of Theorem 2 copied verbatim from
  `Thm2.Theorem2`; `theorem2_iff_with` checks by `Iff.rfl` that they match exactly.
* `conclusion_of_meanSquare`, PROVED: the page 6 reduction, for u v ≠ 0.
* `section2_mean_square`, LEAF, OPEN: the page 6 display from hypotheses i to iv, which is
  2.2 plus 2.3, the whole analytic content of pages 6 to 11.
* `theorem2_paper_nondegenerate`, PROVED from the leaf: Theorem 2 in the form
  `Thm2.Theorem2Paper` for every pair with u v ≠ 0.

Why the step `DecompC165b.section2_circle_method` is not wired here. QUESTION, not a
FINDING: `Thm2.Theorem2` allows u = v = 0. Then the threshold in (1.6) is 0 and the
conclusion asks that the convolution vanish for all but few even N, while hypotheses i
to iv with u = v = 0 only say the sums are small. A candidate counterexample: b the
indicator of one prime m₀ in J and a the indicator of the integers k in
[x - m₀, x - m₀ + H] free of prime factors below exp(√log x); i to iv hold trivially
since the supports have at most H + 1 points, while sieve lower bounds give far more
than H/ℒ² even N with a nonzero convolution. The paper's u, v are positive constants,
page 2 display 1.5. No Lean proof of the counterexample exists, so the step's statement
is left untouched and the u v ≠ 0 case is the one proved from the leaf.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Sing

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2

/-- P0069 Baker Harman Pintz 1997, Section 2, page 6, the step "it suffices to show":
the Chebyshev count. If every threshold `t N` on `S` is at least `t₀ ≥ 0`, the number of
`N ∈ S` with `t N < f N` times `t₀²` is at most `Σ_{N ∈ S} f N²`. PROVED. -/
theorem card_filter_mul_sq_le (S : Finset ℕ) (f t : ℕ → ℝ) {t0 : ℝ} (ht0 : 0 ≤ t0)
    (ht : ∀ N ∈ S, t0 ≤ t N) :
    ((S.filter (fun N => t N < f N)).card : ℝ) * t0 ^ 2 ≤ ∑ N ∈ S, f N ^ 2 := by
  calc ((S.filter (fun N => t N < f N)).card : ℝ) * t0 ^ 2
      = ∑ N ∈ S.filter (fun N => t N < f N), t0 ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ N ∈ S.filter (fun N => t N < f N), f N ^ 2 := by
        apply Finset.sum_le_sum
        intro N hN
        rw [Finset.mem_filter] at hN
        have h1 : t0 < f N := lt_of_le_of_lt (ht N hN.1) hN.2
        exact pow_le_pow_left₀ ht0 h1.le 2
    _ ≤ ∑ N ∈ S, f N ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun N _ _ => sq_nonneg _)

/-- P0069 Baker Harman Pintz 1997, page 6 definition of 𝔖(2n), read with the product over
p > 2 as in `Thm2.sing`: every factor (p-1)/(p-2) is at least 1, so 𝔖(2n) ≥ 2C₂. This is the
uniform lower bound for the threshold in (1.6) used by the page 6 reduction. PROVED. -/
theorem two_C2_le_sing (n : ℕ) : 2 * C2 ≤ sing n := by
  unfold sing
  have h1 := ChenExplicit.one_le_oddFactor n
  have := C2_pos
  nlinarith

/-- P0069 Baker Harman Pintz 1997, Section 2, page 6, the display after 2.1:
Σ_{2n ∈ K} |∫_{1/Q}^{1+1/Q} S₁S₂e(-2nα)dα - uvY/(ℒℒ') 𝔖(2n)|² ≪ H Y² ℒ^{-A-7}, for every
A > 0, with K = [x, x + H] and H = x^{θ₁θ₂} = Y^{θ₂}. The integral is written as the
convolution it equals by orthogonality. -/
def MeanSquare (ε : ℝ) (a b : ℝ → ℕ → ℂ) (u v : ℝ) : Prop :=
  let θ₁ : ℝ := 11 / 20 + ε
  let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
  let Y : ℝ → ℝ := fun x => x ^ θ₁
  let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
  let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N),
      ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
          u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖ ^ 2 ≤
      C * x ^ (θ₁ * θ₂) * Y x ^ 2 * Real.log x ^ (-A - 7)

set_option maxHeartbeats 1000000 in
/-- P0069 Baker Harman Pintz 1997, Section 2, page 6: "To prove Theorem 2 it suffices to
show" the mean square display. For u v ≠ 0 the threshold of (1.6) is at least
|uv| 2C₂ Y/(θ₁ ℒ³), so by Chebyshev the exceptional set has at most a constant times
H ℒ^{-A-2} elements once the display is used with A + 1, fewer than H/ℒ^A for large x.
The case u v = 0 is excluded: the paper's u, v are positive, page 2 display 1.5. PROVED. -/
theorem conclusion_of_meanSquare (ε : ℝ) (hε : 0 < ε) (a b : ℝ → ℕ → ℂ) (u v : ℝ)
    (huv : u * v ≠ 0) (hms : MeanSquare ε a b u v) :
    let θ₁ : ℝ := 11 / 20 + ε
    let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let Y : ℝ → ℝ := fun x => x ^ θ₁
    let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
    let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
    ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
      (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N ∧
          K * |u * v| * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2) / Real.log x <
          ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
            u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖)).card : ℝ) <
        x ^ (θ₁ * θ₂) / Real.log x ^ A := by
  intro θ₁ θ₂ Y I J A hA
  obtain ⟨C1, hC1⟩ := hms (A + 1) (by linarith)
  have hθ : 0 < θ₁ := by simp only [θ₁]; linarith
  have hC2 := C2_pos
  set D : ℝ := (u * v) ^ 2 * (2 * C2) ^ 2 with hD
  have hDpos : 0 < D := by
    have : 0 < (u * v) ^ 2 := by positivity
    positivity
  set c : ℝ := max 1 (|C1| * θ₁ ^ 2 / D) + 1 with hc
  refine ⟨1, max (max C1 3) (Real.exp c), fun x hx => ?_⟩
  have hxC1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp c ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hLc : c ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hxe
  have hc1 : 2 ≤ c := by
    have := le_max_left 1 (|C1| * θ₁ ^ 2 / D); simp only [hc]; linarith
  have hL : 0 < L := by linarith
  have hL' : Real.log (Y x) = θ₁ * L := by
    simp only [Y]; rw [Real.log_rpow hx0]
  set H := x ^ (θ₁ * θ₂) with hH
  have hHpos : 0 < H := Real.rpow_pos_of_pos hx0 _
  have hYpos : 0 < Y x := Real.rpow_pos_of_pos hx0 _
  set P := L ^ A with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hL _
  have hpow : L ^ (-(A + 1) - 7) = 1 / (P * L ^ 8) := by
    rw [show -(A + 1) - 7 = -(A + (8 : ℕ)) by push_cast; ring, Real.rpow_neg hL.le,
      Real.rpow_add hL, Real.rpow_natCast]
    simp [hP]
  -- the Chebyshev step
  set S := (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N : ℕ => Even N) with hS
  set f : ℕ → ℝ := fun N => ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
            u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖ with hf
  set t : ℕ → ℝ := fun N => 1 * |u * v| * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2) /
    Real.log x with ht
  set t0 : ℝ := |u * v| * (2 * C2) * Y x / (θ₁ * L ^ 3) with ht0
  have ht0nn : 0 ≤ t0 := by positivity
  have htt : ∀ N ∈ S, t0 ≤ t N := by
    intro N _
    have hs := two_C2_le_sing (N / 2)
    simp only [ht, ht0, hL', ← hLdef]
    rw [show 1 * |u * v| * Y x / (L * (θ₁ * L)) * sing (N / 2) / L =
      |u * v| * sing (N / 2) * Y x / (θ₁ * L ^ 3) by field_simp]
    gcongr
  have hcheb := card_filter_mul_sq_le S f t ht0nn htt
  have hms' := hC1 x hxC1
  have hfilt : (Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N ∧
          1 * |u * v| * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2) / Real.log x <
          ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
            u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖) =
      S.filter (fun N => t N < f N) := by
    rw [hS, Finset.filter_filter]
  rw [hfilt]
  have hkey : ((S.filter (fun N => t N < f N)).card : ℝ) * t0 ^ 2 ≤
      C1 * H * Y x ^ 2 * (1 / (P * L ^ 8)) := by
    rw [← hpow]; exact le_trans hcheb hms'
  have hn0 : 0 ≤ ((S.filter (fun N => t N < f N)).card : ℝ) := Nat.cast_nonneg _
  generalize ((S.filter (fun N => t N < f N)).card : ℝ) = n at hkey hn0 ⊢
  -- clear denominators
  have ht0sq : t0 ^ 2 = D * Y x ^ 2 / (θ₁ ^ 2 * L ^ 6) := by
    rw [ht0, hD, div_pow, mul_pow, mul_pow, sq_abs]; ring
  rw [ht0sq] at hkey
  have h2 : n * D * L ^ 2 * P ≤ C1 * θ₁ ^ 2 * H := by
    have hY2 : 0 < Y x ^ 2 := by positivity
    have e1 : n * (D * Y x ^ 2 / (θ₁ ^ 2 * L ^ 6)) * (θ₁ ^ 2 * L ^ 8 * P / Y x ^ 2) =
        n * D * L ^ 2 * P := by field_simp
    have e2 : C1 * H * Y x ^ 2 * (1 / (P * L ^ 8)) * (θ₁ ^ 2 * L ^ 8 * P / Y x ^ 2) =
        C1 * θ₁ ^ 2 * H := by field_simp
    rw [← e1, ← e2]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  have hbig : |C1| * θ₁ ^ 2 < D * L ^ 2 := by
    have h3 : |C1| * θ₁ ^ 2 / D < L ^ 2 := by
      have := le_max_right 1 (|C1| * θ₁ ^ 2 / D)
      nlinarith
    rw [div_lt_iff₀ hDpos] at h3; linarith
  rw [lt_div_iff₀ hPpos]
  have h4 : C1 * θ₁ ^ 2 * H ≤ |C1| * θ₁ ^ 2 * H := by
    have := le_abs_self C1
    gcongr
  by_contra hcon'
  have hcon := not_lt.mp hcon'
  have : D * L ^ 2 * H ≤ n * D * L ^ 2 * P := by
    have := mul_le_mul_of_nonneg_left hcon (by positivity : 0 ≤ D * L ^ 2)
    nlinarith
  nlinarith [mul_lt_mul_of_pos_right hbig hHpos]

/-- P0069 Baker Harman Pintz 1997, page 3, the conclusion of Theorem 2: 1.6 for almost all
even N in [x, x + x^{θ₁θ₂}], copied verbatim from `Thm2.Theorem2`. -/
def Conclusion (ε : ℝ) (a b : ℝ → ℕ → ℂ) (u v : ℝ) : Prop :=
  let θ₁ : ℝ := 11 / 20 + ε
  let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
  let Y : ℝ → ℝ := fun x => x ^ θ₁
  let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
  let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
  ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
    (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N ∧
        K * |u * v| * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2) / Real.log x <
        ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
          u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖)).card : ℝ) <
      x ^ (θ₁ * θ₂) / Real.log x ^ A

/-- P0069 Baker Harman Pintz 1997, page 3, Theorem 2 with an arbitrary conclusion `P`:
the hypotheses i to iv copied verbatim from `Thm2.Theorem2`. With `P = Conclusion` it is
`Thm2.Theorem2` itself, see `theorem2_iff_with`. -/
def Theorem2With (ε B : ℝ)
    (P : (ℝ → ℕ → ℂ) → (ℝ → ℕ → ℂ) → ℝ → ℝ →
      (ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)) → Prop) : Prop :=
  ∀ (a b : ℝ → ℕ → ℂ) (u v : ℝ) (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)),
    let θ₁ : ℝ := 11 / 20 + ε
    let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let Y : ℝ → ℝ := fun x => x ^ θ₁
    let Q : ℝ → ℕ := fun x => ⌊(Y x ^ θ₂) ^ (1 / 2 : ℝ) / 2⌋₊
    let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
    let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
    (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
        ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
            C * Y x * Real.log x ^ (-A)) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ Q x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * Q x : ℝ) / (6 * Y x) ≤ z → z ≤ 6 * q * Q x / Y x →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (Y x / 2)..(3 * Y x),
            ‖∑ m ∈ (J x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ^ 2 ≤
          C * ((q : ℝ) * Q x) ^ 2 * Y x * Real.log x ^ (-A)) →
    P a b u v E

/-- The hypotheses of `Theorem2With` are exactly those of `Thm2.Theorem2`. PROVED by `Iff.rfl`. -/
theorem theorem2_iff_with (ε B : ℝ) :
    Theorem2 ε B ↔ Theorem2With ε B (fun a b u v _ => Conclusion ε a b u v) := Iff.rfl

/-- LEAF. P0069 Baker Harman Pintz 1997, Section 2, pages 6 to 11: the page 6 mean square
display from hypotheses i to iv of Theorem 2, with ε in the paper's window where Bε is
small, page 3. The paper proves it as 2.2, the major arcs, pages 6 to 8 with 2.4 to 2.9,
plus 2.3, the minor arcs, pages 8 to 11 with 2.10 to 2.16 and Gallagher's lemma. No
hypothesis u v ≠ 0 is needed here. OPEN. -/
theorem section2_mean_square :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ => MeanSquare ε a b u v) := by
  sorry

/-- P0069 Baker Harman Pintz 1997, Theorem 2 in the form of `Thm2.Theorem2Paper`, for
every pair of densities with u v ≠ 0: the page 6 reduction `conclusion_of_meanSquare`
applied to the leaf `section2_mean_square`. PROVED from the leaf; CONDITIONAL on it. -/
theorem theorem2_paper_nondegenerate :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Theorem2With ε B (fun a b u v _ => u * v ≠ 0 → Conclusion ε a b u v) := by
  intro B
  obtain ⟨ε₀, hε₀, h⟩ := section2_mean_square B
  refine ⟨ε₀, hε₀, fun ε hε hεε a b u v E h1 h2 h3 h4 h5 huv => ?_⟩
  exact conclusion_of_meanSquare ε hε a b u v huv (h ε hε hεε a b u v E h1 h2 h3 h4 h5)

end LeanLab.BHP1997.Section2MS
