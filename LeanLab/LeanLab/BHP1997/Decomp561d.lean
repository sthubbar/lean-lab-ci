/-
P0069 pages 9 and 10, displays 2.11 to 2.16.
Independent split of the local minor arc energy estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Sing

namespace LeanLab.BHP1997.Decomp561d
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- P0069 page 1: the long interval length Y. -/
noncomputable def length512 (ε x : ℝ) : ℝ := x ^ (11 / 20 + ε)


/-- P0069 page 3: the Farey order Q. -/
noncomputable def order512 (ε x : ℝ) : ℕ :=
  ⌊(length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2⌋₊


/-- P0069 page 5: a complete period starting at 1/Q. -/
noncomputable def period512 (ε x : ℝ) : Set ℝ :=
  Ioc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ))


/-- P0069 page 5: the major arcs with half width log x to power 4D divided by qY.
Clipping to the complete period is harmless for sufficiently large x. -/
noncomputable def major512 (ε D x : ℝ) : Set ℝ :=
  period512 ε x ∩ ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
    ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
          ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x))


/-- P0069 page 5: the minor arcs are the complement inside the complete period. -/
noncomputable def minor512 (ε D x : ℝ) : Set ℝ := period512 ε x \ major512 ε D x


/-- P0069 page 5: S with its finite support displayed. -/
noncomputable def polynomial512 (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ S, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))


/-- P0069 page 9 display 2.11: the local energy of S2 on a minor arc neighborhood
of radius 1/H. -/
noncomputable def localMinorEnergy512 (ε D x : ℝ) (b : ℕ → ℂ) (ζ : ℝ) : ℝ :=
  ∫ t in Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
      (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2


/-- P0069 page 5, the support J of the short polynomial. -/
noncomputable def support561 (Y : ℝ) : Finset ℕ := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊

/-- P0069 page 9 following 2.13, the centered character coefficient. -/
noncomputable def centered561 (Y : ℝ) (b : ℕ → ℂ) (v : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  b m * χ (m : ZMod q) - delta χ * v / Real.log Y

/-- P0069 pages 9 and 10 displays 2.13 and 2.15, complementary character energy.
The factor q times character count over phi squared stays in the rational arc leaf. -/
noncomputable def characterEnergy561 (Y T : ℝ) (b : ℕ → ℂ) (v : ℝ)
    (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) : ℝ :=
  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
    ∫ t in (-1 / T)..(1 / T),
      ‖polynomial512 (support561 Y) (centered561 Y b v χ) t‖ ^ 2

/-- P0069 page 10 display 2.16, a normalized fixed additive window moment.
The window length is T over 2, so the Gallagher frequency product is one half. -/
noncomputable def fixedWindowMoment561 (Y T : ℝ) (b : ℕ → ℂ) (v : ℝ)
    (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) : ℝ :=
  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
    ∫ y in (Y / 2)..(3 * Y),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
        centered561 Y b v χ m‖ ^ 2

/-- P0069 page 10 after 2.16 and page 3 hypothesis iv, the multiplicative window. -/
noncomputable def multiplicativeWindowMoment561 (Y z : ℝ) (b : ℕ → ℂ) (v : ℝ)
    (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) : ℝ :=
  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
    ∫ y in (Y / 2)..(3 * Y),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        centered561 Y b v χ m‖ ^ 2

/-- LEAF. P0069 page 10 display 2.16, Gallagher Lemma 1.9 in reference 21.
Use window length T over 2 with frequency radius 1 over T. This is a
sufficient normalized Gallagher input, not the literal printed window of length T.
The short polynomial is supported in J. A positive T at most Y keeps every
nonzero fixed window inside the stated y integral. Sum the inequality over the
complementary characters. The constant is uniform in every displayed parameter. OPEN. -/
theorem leaf_gallagher561 :
    ∃ G : ℝ, 0 < G ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        characterEnergy561 Y T b v q E ≤ G / T ^ 2 * fixedWindowMoment561 Y T b v q E := by
  sorry

/-- LEAF. P0069 page 10 after 2.16, Saffari Vaughan reference 29 proof of 6.21.
Uniform control of the multiplicative windows controls the fixed additive window.
The z range is exactly T over 6Y through 6T over Y. The constant is uniform and
M is a nonnegative bound on the whole character sum, so no character dependent
choice of z is assumed. OPEN. -/
theorem leaf_saffari_vaughan561 :
    ∃ V : ℝ, 0 < V ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        fixedWindowMoment561 Y T b v q E ≤ V * M := by
  sorry

/-- P0069 page 3 and page 9 before 2.12, the Farey order is short enough for
Gallagher windows. This is only the elementary square bound. -/
theorem order_square_le_length561 (ε x : ℝ) (hY : 1 ≤ length512 ε x) :
    (order512 ε x : ℝ) ^ 2 ≤ length512 ε x := by
  let H : ℝ := length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)
  have hH0 : 0 ≤ H := Real.rpow_nonneg (by linarith) _
  have hHY : H ≤ length512 ε x :=
    Real.rpow_le_self_of_one_le hY (by norm_num)
  have hfloor : (order512 ε x : ℝ) ≤ Real.sqrt H / 2 := by
    unfold order512
    rw [← Real.sqrt_eq_rpow]
    exact Nat.floor_le (by positivity)
  have hs : Real.sqrt H ^ 2 = H := Real.sq_sqrt hH0
  have hn : (0 : ℝ) ≤ order512 ε x := Nat.cast_nonneg _
  nlinarith [Real.sqrt_nonneg H]

/-- LEAF. P0069 page 9 displays 2.11 to 2.14 and page 10 display 2.15.
The rational arc covering, principal part and exceptional characters reduce
local minor energy to the actual complementary character energy. This leaf
retains that character energy as an explicit input and contains neither the
Gallagher step nor the Saffari Vaughan window comparison. The all modulus
principal and nonunit residue bookkeeping remain in this rational arc leaf.
QUESTION. The nonunit family in PROGRESS.md must be resolved before repointing
the old local energy leaf. OPEN. -/
theorem leaf_local_energy_from_characters561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
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
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ q : ℕ, 1 ≤ q → q ≤ order512 ε x →
        characterEnergy561 (length512 ε x) ((q : ℝ) * order512 ε x) (b x) v q (E A x q) ≤
          C * length512 ε x * Real.log x ^ (-A)) →
    (∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
        localMinorEnergy512 ε D x (b x) ζ ≤
          C * length512 ε x * Real.log x ^ (-L)) := by
  sorry

/-- P0069 pages 9 and 10 displays 2.11 to 2.16, the exact expanded local
minor arc leaf. CONDITIONAL ON the rational arc, Gallagher and Saffari Vaughan
leaves. No direct admission occurs in this assembly. -/
theorem local_minor_energy561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
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
    (∀ L : ℝ, 0 < L → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ ζ : ℝ,
        localMinorEnergy512 ε D x (b x) ζ ≤
          C * length512 ε x * Real.log x ^ (-L)) := by
  intro B
  obtain ⟨ε₀, hε₀, hlocal⟩ := leaf_local_energy_from_characters561 B
  obtain ⟨G, hG, hGall⟩ := leaf_gallagher561
  obtain ⟨V, hV, hSV⟩ := leaf_saffari_vaughan561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he a b u v E
  dsimp only
  intro h1 h2 h3 h4 h5
  apply hlocal ε hε he a b u v E h1 h2 h3 h4 h5
  intro A hA
  obtain ⟨C₀, hC₀⟩ := h5 A hA
  let C : ℝ := max (max C₀ 3) (G * V * |C₀|)
  refine ⟨C, fun x hx q hq hqQ => ?_⟩
  have hxC : C₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : 3 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hY : 1 ≤ length512 ε x :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hQ : 1 ≤ order512 ε x := hq.trans hqQ
  let Y := length512 ε x
  let T : ℝ := (q : ℝ) * order512 ε x
  have hY0 : 0 ≤ Y := by dsimp [Y]; linarith
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ))
  have hTY : T ≤ Y := by
    calc
      T ≤ (order512 ε x : ℝ) ^ 2 := by
        dsimp [T]
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ) (Nat.cast_nonneg _)
      _ ≤ Y := order_square_le_length561 ε x hY
  let M : ℝ := |C₀| * T ^ 2 * Y * Real.log x ^ (-A)
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmulti (z : ℝ) (hz0 : T / (6 * Y) ≤ z) (hz1 : z ≤ 6 * T / Y) :
      multiplicativeWindowMoment561 Y z (b x) v q (E A x q) ≤ M := by
    have hh := (hC₀ x hxC q hq hqQ).2 z hz0 (by simpa [T, Y, length512, order512, mul_assoc] using hz1)
    change multiplicativeWindowMoment561 Y z (b x) v q (E A x q) ≤
      C₀ * T ^ 2 * Y * Real.log x ^ (-A) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₀) (sq_nonneg T)) hY0)
      (Real.rpow_nonneg hlog0.le _))
  have hfixed := hSV Y T hY hT hTY (b x) v q (E A x q) M hM hmulti
  have henergy := hGall Y T hY hT hTY (b x) v q (E A x q)
  calc
    characterEnergy561 Y T (b x) v q (E A x q) ≤ G / T ^ 2 * fixedWindowMoment561 Y T (b x) v q (E A x q) := henergy
    _ ≤ G / T ^ 2 * (V * M) := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = (G * V * |C₀|) * Y * Real.log x ^ (-A) := by
      dsimp [M]
      field_simp [ne_of_gt hT]
    _ ≤ C * Y * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hY0)
        (Real.rpow_nonneg hlog0.le _)

end LeanLab.BHP1997.Decomp561d
