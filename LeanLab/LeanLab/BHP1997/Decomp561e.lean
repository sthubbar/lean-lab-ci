/-
P0069 pages 8 and 9, displays 2.10 and 2.11.
Independent split of the periodic kernel reduction.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561c
import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- P0069 page 5: S1 S2 e at frequency minus N. -/
noncomputable def integrand512 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t *
    polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t *
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))


/-- P0069 page 6: the even frequencies in K. -/
noncomputable def frequencies512 (ε x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
    (fun N => Even N)


/-- P0069 page 6 display 2.3: the minor arc mean square as a real quantity. -/
noncomputable def minorError512 (ε D x : ℝ) (a b : ℕ → ℂ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖∫ t in minor512 ε D x, integrand512 ε x a b N t‖ ^ 2


/-- P0069 page 6: H Y squared times the requested logarithmic saving. -/
noncomputable def scale512 (ε A x : ℝ) : ℝ :=
  x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
    length512 ε x ^ 2 * Real.log x ^ (-A - 7)


/-- P0069 page 9 before 2.11, the complete long polynomial energy. -/
noncomputable def longEnergy561 (ε x : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∫ t in period512 ε x,
    ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2

/-- P0069 page 9 before 2.11, the complete short polynomial energy. -/
noncomputable def shortEnergy561 (ε x : ℝ) (b : ℕ → ℂ) : ℝ :=
  ∫ t in period512 ε x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2

/-- P0069 page 8 display 2.10, the periodic kernel majorant with both poles.
At resonance use H rather than the totalized reciprocal of zero. -/
noncomputable def kernelWeight561 (H t : ℝ) : ℝ :=
  if ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖ = 0 then H
  else min H (1 / ‖((2 * t : ℝ) : AddCircle (1 : ℝ))‖)

/-- P0069 page 8 display 2.10, the weighted short polynomial energy. -/
noncomputable def weightedEnergy561 (ε D x : ℝ) (b : ℕ → ℂ) (ζ : ℝ) : ℝ :=
  ∫ t in minor512 ε D x,
    ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 *
      kernelWeight561
        (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - ζ) ^ 2

/-- LEAF. P0069 page 8 display 2.10, the finite Fourier and Cauchy reduction.
The norm bound for the even frequency geometric kernel is proved in Decomp561c.
Only the integral rearrangement and the two Cauchy inequalities remain here.
There are no coefficient distribution or logarithmic saving premises. OPEN. -/
theorem leaf_kernel_schur561 :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W → (∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤ W) →
        minorError512 ε D x a b ≤
          K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
  sorry

/-- LEAF. P0069 page 9, reduction of 2.10 to 2.11.
Dyadic neighborhoods of the two periodic poles turn the uniform local energy
bound U into a weighted energy bound C H squared U. This finite integral
inequality has no arithmetic or logarithmic saving premise. OPEN. -/
theorem leaf_kernel_localization561 :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ U : ℝ, 0 ≤ U →
      (∀ ζ : ℝ, localMinorEnergy512 ε D x b ζ ≤ U) →
      ∀ ζ : ℝ, weightedEnergy561 ε D x b ζ ≤
        K * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ^ 2 * U := by
  sorry

/-- LEAF. P0069 page 9 before 2.11, the coefficient energy bounds from Parseval
and hypothesis ii. The needed short interval divisor moment for the long
polynomial is kept explicit. A full summatory divisor bound is not substituted.
This input has no minor arc or local energy hypothesis. OPEN. -/
theorem leaf_coefficient_energies561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ a b : ℝ → ℕ → ℂ,
        (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
          ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∃ M C : ℝ, 0 ≤ M ∧ 1 ≤ C ∧ ∀ x : ℝ, C ≤ x →
          longEnergy561 ε x (a x) ≤ C * length512 ε x * Real.log x ^ M ∧
          shortEnergy561 ε x (b x) ≤ C * length512 ε x * Real.log x ^ M := by
  sorry

/-- P0069 pages 8 and 9 displays 2.10 and 2.11, explicit logarithmic budget.
Local exponent twice A plus three M plus 14 absorbs the three half powers of
coefficient energy and leaves the required exponent minus A minus 7. -/
theorem kernel_log_absorption561 {H Y l C₀ C₁ K M A : ℝ}
    (hH : 0 ≤ H) (hY : 0 ≤ Y) (hl : 0 < l)
    (hC₀ : 1 ≤ C₀) (hC₁ : 1 ≤ C₁) (hK : 1 ≤ K) :
    (C₀ * Y * l ^ M) * Real.sqrt (C₀ * Y * l ^ M) *
        Real.sqrt (K * H ^ 2 * (C₁ * Y * l ^ (-(2 * A + 3 * M + 14)))) ≤
      C₀ ^ 2 * K * C₁ * H * Y ^ 2 * l ^ (-A - 7) := by
  let J : ℝ := C₀ * K * C₁
  have hJ : 1 ≤ J := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC₀ hK) hC₁
  have hU : 0 ≤ C₀ * Y * l ^ M := by positivity
  have hZ : 0 ≤ J * H * Y * l ^ (-A - M - 7) := by positivity
  have hsq :
      (C₀ * Y * l ^ M) * (K * H ^ 2 * (C₁ * Y * l ^ (-(2 * A + 3 * M + 14)))) ≤
        (J * H * Y * l ^ (-A - M - 7)) ^ 2 := by
    have hp : l ^ M * l ^ (-(2 * A + 3 * M + 14)) = (l ^ (-A - M - 7)) ^ 2 := by
      rw [← Real.rpow_add hl, ← Real.rpow_mul_natCast hl.le]
      congr 1
      ring
    calc
      _ = J * H ^ 2 * Y ^ 2 * (l ^ M * l ^ (-(2 * A + 3 * M + 14))) := by dsimp [J]; ring
      _ = J * H ^ 2 * Y ^ 2 * (l ^ (-A - M - 7)) ^ 2 := by rw [hp]
      _ ≤ J ^ 2 * H ^ 2 * Y ^ 2 * (l ^ (-A - M - 7)) ^ 2 := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hroot := (Real.sqrt_le_iff).mpr ⟨hZ, hsq⟩
  calc
    _ = (C₀ * Y * l ^ M) * Real.sqrt
        ((C₀ * Y * l ^ M) * (K * H ^ 2 * (C₁ * Y * l ^ (-(2 * A + 3 * M + 14))))) := by
      rw [Real.sqrt_mul hU]
      ring
    _ ≤ (C₀ * Y * l ^ M) * (J * H * Y * l ^ (-A - M - 7)) :=
      mul_le_mul_of_nonneg_left hroot hU
    _ = _ := by
      have hp : l ^ M * l ^ (-A - M - 7) = l ^ (-A - 7) := by
        rw [← Real.rpow_add hl]
        congr 1
        ring
      calc
        _ = C₀ ^ 2 * K * C₁ * H * Y ^ 2 * (l ^ M * l ^ (-A - M - 7)) := by dsimp [J]; ring
        _ = _ := by rw [hp]

/-- P0069 pages 8 and 9 displays 2.10 and 2.11, the exact expanded kernel
reduction leaf. CONDITIONAL ON the finite Schur, dyadic localization and
coefficient energy leaves. No direct admission occurs in this assembly. -/
theorem minor_kernel_reduction561 :
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
          C * length512 ε x * Real.log x ^ (-L)) →
    ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        minorError512 ε D x (a x) (b x) ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨ε₀, hε₀, hcoeff⟩ := leaf_coefficient_energies561 B
  obtain ⟨K, hK, hSchur⟩ := leaf_kernel_schur561
  obtain ⟨G, hG, hLoc⟩ := leaf_kernel_localization561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he a b u v E
  dsimp only
  intro _h1 h2 _h3 _h4 _h5 hlocal A hA
  obtain ⟨M, C₀, hM, hC₀, henergy⟩ := hcoeff ε hε he a b h2
  have hθ : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) :=
    mul_pos (by linarith) (by norm_num)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hθ).eventually (Filter.eventually_ge_atTop (2 : ℝ)))
  let L : ℝ := 2 * A + 3 * M + 14
  have hL : 0 < L := by dsimp [L]; linarith
  obtain ⟨D₀, hD₀⟩ := hlocal L hL
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₀ D hD
  let C₂ : ℝ := max C₁ 1
  let P : ℝ := K * C₀ ^ 2 * G * C₂
  let C : ℝ := max (max (max C₀ C₁) (max X 3)) P
  refine ⟨C, fun x hx => ?_⟩
  have hxC₀ : C₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hxC₁ : C₁ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx3 : 3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  let H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
  let Y : ℝ := length512 ε x
  let U : ℝ := C₂ * Y * Real.log x ^ (-L)
  let W : ℝ := G * H ^ 2 * U
  have hH : 2 ≤ H := hX x hxX
  have hY : 0 ≤ Y := Real.rpow_nonneg hx0 _
  have hC₂ : 1 ≤ C₂ := le_max_right _ _
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hlocalU (ζ : ℝ) : localMinorEnergy512 ε D x (b x) ζ ≤ U := by
    calc
      _ ≤ C₁ * Y * Real.log x ^ (-L) := hC₁ x hxC₁ ζ
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hY) (Real.rpow_nonneg hlog.le _)
  have hweighted := hLoc ε D x (b x) hH U hU hlocalU
  have hbound := hSchur ε D x (a x) (b x) hH W hW hweighted
  have hE₁ : 0 ≤ longEnergy561 ε x (a x) := integral_nonneg fun _ => sq_nonneg _
  have hce : 0 ≤ C₀ * Y * Real.log x ^ M := by positivity
  calc
    minorError512 ε D x (a x) (b x) ≤
        K * longEnergy561 ε x (a x) * Real.sqrt (shortEnergy561 ε x (b x)) * Real.sqrt W := hbound
    _ ≤ K * (C₀ * Y * Real.log x ^ M) * Real.sqrt (C₀ * Y * Real.log x ^ M) * Real.sqrt W := by
      gcongr
      · exact (henergy x hxC₀).1
      · exact (henergy x hxC₀).2
    _ = K * ((C₀ * Y * Real.log x ^ M) * Real.sqrt (C₀ * Y * Real.log x ^ M) * Real.sqrt W) := by ring
    _ ≤ K * (C₀ ^ 2 * G * C₂ * H * Y ^ 2 * Real.log x ^ (-A - 7)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ K)
      exact kernel_log_absorption561 (by linarith) hY hlog hC₀ hC₂ hG
    _ = P * scale512 ε A x := by dsimp [P, scale512, H, Y]; ring
    _ ≤ C * scale512 ε A x := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      unfold scale512
      positivity

end LeanLab.BHP1997.Decomp561e
