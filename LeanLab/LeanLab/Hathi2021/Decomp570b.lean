/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, pages 194 to 196.
Independent supply for the exceptional arc leaf.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp577b
import LeanLab.Hathi2021.Decomp577d
import LeanLab.Hathi2021.Decomp577e

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a

namespace LeanLab.Hathi2021.Decomp570b

/-- Hu page 195, Rieger reference 17. Supplied by Decomp577d,
CONDITIONAL ON its Rieger collision count leaf.
This input involves only the fourth moment of the prime square sum. -/
theorem rieger_fourth_moment_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSquareFourthMoment n₁ n ≤ K * (n : ℝ) * Real.log n ^ 2 :=
  LeanLab.Hathi2021.Decomp577d.rieger_fourth_moment_bound

/-- Hu page 194 Lemma 2.3, Platt and Trudgian reference 16. Supplied by
Decomp577e, CONDITIONAL ON its unshifted exceptional measure leaf.
The translated slice form is the periodic version used on page 195.
This input contains no prime exponential sum. -/
theorem platt_trudgian_slice_bound :
    ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ → ∀ t : ℝ,
        volume.real (exceptionalSlice n₁ t) ≤ K * (n₁ : ℝ) ^ (-E) :=
  LeanLab.Hathi2021.Decomp577e.platt_trudgian_slice_bound

/-- Helper for Hu pages 195 and 196. Swap the two coordinates in the
second strip so that its minor coordinate comes first. -/
private theorem stripMass_false_swap (n₁ n₂ : ℕ) :
    stripMass n₁ n₂ false =
      ∫ z in ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ exceptional n₁) ∩
        {z | z.1 ∉ majorOne n₁ n₂},
        ‖S n₁ n₂ z.1‖ * ‖T n₁ n₂ z.1‖ ^ 2 *
          ‖S n₁ n₁ z.2‖ * ‖T n₁ n₁ z.2‖ ^ 2 := by
  have hp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    simpa only [← Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  have heq := hp.setIntegral_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding
    (baseNorm n₁ n₂) (minorStrip n₁ n₂ false)
  have hset : Prod.swap ⁻¹' minorStrip n₁ n₂ false =
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ exceptional n₁) ∩
        {z | z.1 ∉ majorOne n₁ n₂} := by
    ext z
    simp [minorStrip, exceptional, and_assoc, and_left_comm, and_comm, add_comm]
  rw [hset] at heq
  rw [stripMass, ← heq]
  apply integral_congr_ae
  filter_upwards with z
  dsimp [baseNorm]
  ring

/-- Helper for Hu page 195 and the symmetric estimate on page 196.
Uniform pointwise and moment bounds control the sum of the two strips.
This theorem states every analytic hypothesis explicitly. -/
private theorem stripMass_uniform_le (n₁ n₂ : ℕ) {M A m : ℝ}
    (hM : 0 ≤ M)
    (hminor₁ : ∀ x, x ∉ majorOne n₁ n₁ → ‖T n₁ n₁ x‖ ≤ M)
    (hminor₂ : ∀ x, x ∉ majorOne n₁ n₂ → ‖T n₁ n₂ x‖ ≤ M)
    (hS₁ : primeSecondMoment n₁ n₁ ≤ A)
    (hS₂ : primeSecondMoment n₁ n₂ ≤ A)
    (hT₁ : primeSquareFourthMoment n₁ n₁ ≤ A)
    (hT₂ : primeSquareFourthMoment n₁ n₂ ≤ A)
    (hslice : ∀ t, volume.real (exceptionalSlice n₁ t) ≤ m) :
    stripMass n₁ n₂ true + stripMass n₁ n₂ false ≤
      2 * M ^ 2 * Real.sqrt A ^ 3 * Real.sqrt m := by
  have hgen (a b : ℕ)
      (hma : ∀ x, x ∉ majorOne n₁ a → ‖T n₁ a x‖ ≤ M)
      (hsa : primeSecondMoment n₁ a ≤ A)
      (hsb : primeSecondMoment n₁ b ≤ A)
      (htb : primeSquareFourthMoment n₁ b ≤ A) :
      (∫ z in ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩ exceptional n₁) ∩
        {z | z.1 ∉ majorOne n₁ a},
        ‖S n₁ a z.1‖ * ‖T n₁ a z.1‖ ^ 2 *
          ‖S n₁ b z.2‖ * ‖T n₁ b z.2‖ ^ 2) ≤
        M ^ 2 * Real.sqrt A ^ 3 * Real.sqrt m := by
    have hcS (n : ℕ) : Continuous (fun x => ‖S n₁ n x‖) := by unfold S e; fun_prop
    have hcT (n : ℕ) : Continuous (fun x => ‖T n₁ n x‖ ^ 2) := by unfold T e; fun_prop
    have hb := LeanLab.Hathi2021.Decomp577a.sectional_cauchy_bound
      (fun x => ‖S n₁ a x‖) (fun x => ‖T n₁ a x‖ ^ 2)
      (fun x => ‖S n₁ b x‖) (fun x => ‖T n₁ b x‖ ^ 2)
      (hcS a) (hcT a) (hcS b) (hcT b)
      (fun x => norm_nonneg _) (fun x => sq_nonneg _)
      (fun x => norm_nonneg _) (fun x => sq_nonneg _)
      (measurableSet_majorOne n₁ a).compl (measurableSet_exceptional n₁)
      (sq_nonneg M)
      (fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hma x hx.2) 2)
      (fun y hy => hslice y)
    have hfour : (∫ y in Set.Icc (0 : ℝ) 1, (‖T n₁ b y‖ ^ 2) ^ 2) =
        primeSquareFourthMoment n₁ b := by simp only [← pow_mul]; rfl
    rw [hfour] at hb
    calc
      _ ≤ M ^ 2 * Real.sqrt (primeSecondMoment n₁ a) * Real.sqrt m *
          Real.sqrt (primeSecondMoment n₁ b) * Real.sqrt (primeSquareFourthMoment n₁ b) := hb
      _ ≤ M ^ 2 * Real.sqrt A * Real.sqrt m * Real.sqrt A * Real.sqrt A := by gcongr
      _ = _ := by ring
  have h₁ := hgen n₁ n₂ hminor₁ hS₁ hS₂ hT₂
  have h₂ := hgen n₂ n₁ hminor₂ hS₂ hS₁ hT₁
  change stripMass n₁ n₂ true ≤ _ at h₁
  rw [← stripMass_false_swap n₁ n₂] at h₂
  calc
    _ ≤ (M ^ 2 * Real.sqrt A ^ 3 * Real.sqrt m) +
      (M ^ 2 * Real.sqrt A ^ 3 * Real.sqrt m) := add_le_add h₁ h₂
    _ = _ := by ring

/-- Helper for Hu pages 195 and 196. Every fixed natural power of
logarithm is eventually bounded by any fixed positive power. -/
private theorem log_pow_le_rpow (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (Real.log n) ^ k ≤ (n : ℝ) ^ η := by
  have hz : Tendsto (fun x : ℝ => (Real.log x) ^ k / x ^ η) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hη).tendsto_div_nhds_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hz.comp tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsmall := (hN n ((le_max_right _ _).trans hn)).le
  exact (div_le_one (Real.rpow_pos_of_pos hnpos η)).1 hsmall

/-- Pages 195 and 196. CONDITIONAL ON the minor T bound, the fourth moment
bound and the strict exceptional slice estimate. Every analytic input is an
explicit hypothesis; the proof has no sorry. -/
private theorem strip_power_saving_of_inputs (C : ℝ) (hC : 1 < C)
    (hMinor : ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
        N₀ ≤ n → n ≤ n₁ → (n₁ : ℝ) ≤ C * n → ∀ x : ℝ,
        x ∉ majorOne n₁ n → ‖T n₁ n x‖ ≤ K * (n : ℝ) ^ (7 / 16 + ε : ℝ))
    (hFourth : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSquareFourthMoment n₁ n ≤ K * (n : ℝ) * Real.log n ^ 2)
    (hSlice : ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ → ∀ t : ℝ,
        volume.real (exceptionalSlice n₁ t) ≤ K * (n₁ : ℝ) ^ (-E)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      stripMass n₁ n₂ true + stripMass n₁ n₂ false ≤
        K * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε) := by
  obtain ⟨E, hE, Ke, hKe, Ne, hNe⟩ := hSlice
  let η : ℝ := (E - 3 / 4) / 16
  let ε : ℝ := (E - 3 / 4) / 8
  have hη : 0 < η := by dsimp [η]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨Kt, hKt, Nt, hNt⟩ := hMinor η hη
  obtain ⟨Ks, hKs, Ns, hNs⟩ := prime_second_moment_bound
  obtain ⟨Kr, hKr, Nr, hNr⟩ := hFourth
  obtain ⟨Nl₁, hNl₁⟩ := log_pow_le_rpow 1 η hη
  obtain ⟨Nl₂, hNl₂⟩ := log_pow_le_rpow 2 η hη
  let Km : ℝ := max Ks Kr
  have hKm : 0 ≤ Km := hKs.trans (le_max_left _ _)
  let Kraw : ℝ := 2 * Kt ^ 2 * Real.sqrt Km ^ 3 * Real.sqrt Ke
  have hKraw : 0 ≤ Kraw := by dsimp [Kraw]; positivity
  let N : ℕ := max 2 (max Ne (max Nt (max Ns (max Nr (max Nl₁ Nl₂)))))
  refine ⟨ε, hε, Kraw * C, mul_nonneg hKraw (by linarith), N, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have hN₂ : 2 ≤ n₂ := (le_max_left _ _).trans hn
  have hN₁ : N ≤ n₁ := hn.trans hlt.le
  have hn₁pos : (0 : ℝ) < n₁ := by exact_mod_cast (show 0 < n₁ by omega)
  have hn₁one : (1 : ℝ) ≤ n₁ := by exact_mod_cast (show 1 ≤ n₁ by omega)
  have hne : Ne ≤ n₁ := by dsimp [N] at hN₁; omega
  have hnt : Nt ≤ n₂ := by dsimp [N] at hn; omega
  have hns : Ns ≤ n₂ := by dsimp [N] at hn; omega
  have hnr : Nr ≤ n₂ := by dsimp [N] at hn; omega
  have hnl₁ : Nl₁ ≤ n₁ := by dsimp [N] at hN₁; omega
  have hnl₂ : Nl₂ ≤ n₁ := by dsimp [N] at hN₁; omega
  have hlog₁ : Real.log n₁ ≤ (n₁ : ℝ) ^ η := by simpa using hNl₁ n₁ hnl₁
  have hlog₂ : (Real.log n₁) ^ 2 ≤ (n₁ : ℝ) ^ η := hNl₂ n₁ hnl₂
  have hmoment (n : ℕ) (hnlo : n₂ ≤ n) (hnhi : n ≤ n₁) :
      primeSecondMoment n₁ n ≤ Km * (n₁ : ℝ) ^ (1 + η) ∧
      primeSquareFourthMoment n₁ n ≤ Km * (n₁ : ℝ) ^ (1 + η) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hlogle : Real.log n ≤ Real.log n₁ :=
      Real.log_le_log hnpos (by exact_mod_cast hnhi)
    have hnle : (n : ℝ) ≤ n₁ := by exact_mod_cast hnhi
    have hsp : Ks ≤ Km := le_max_left _ _
    have hrp : Kr ≤ Km := le_max_right _ _
    constructor
    · calc
        primeSecondMoment n₁ n ≤ Ks * (n : ℝ) * Real.log n :=
          hNs n₁ n (hns.trans hnlo) hnhi
        _ ≤ Km * (n₁ : ℝ) * Real.log n₁ := by gcongr
        _ ≤ Km * (n₁ : ℝ) * (n₁ : ℝ) ^ η := by gcongr
        _ = Km * (n₁ : ℝ) ^ (1 + η) := by rw [Real.rpow_add hn₁pos, Real.rpow_one]; ring
    · calc
        primeSquareFourthMoment n₁ n ≤ Kr * (n : ℝ) * Real.log n ^ 2 :=
          hNr n₁ n (hnr.trans hnlo) hnhi
        _ ≤ Km * (n₁ : ℝ) * Real.log n₁ ^ 2 := by gcongr
        _ ≤ Km * (n₁ : ℝ) * (n₁ : ℝ) ^ η := by gcongr
        _ = Km * (n₁ : ℝ) ^ (1 + η) := by rw [Real.rpow_add hn₁pos, Real.rpow_one]; ring
  have hminor (n : ℕ) (hnlo : n₂ ≤ n) (hnhi : n ≤ n₁)
      (hr : (n₁ : ℝ) ≤ C * n) (x : ℝ) (hx : x ∉ majorOne n₁ n) :
      ‖T n₁ n x‖ ≤ Kt * (n₁ : ℝ) ^ (7 / 16 + η : ℝ) := by
    calc
      ‖T n₁ n x‖ ≤ Kt * (n : ℝ) ^ (7 / 16 + η : ℝ) :=
        hNt n₁ n (hnt.trans hnlo) hnhi hr x hx
      _ ≤ Kt * (n₁ : ℝ) ^ (7 / 16 + η : ℝ) := by gcongr
  have hrself : (n₁ : ℝ) ≤ C * n₁ := by nlinarith
  have hraw := stripMass_uniform_le n₁ n₂
    (M := Kt * (n₁ : ℝ) ^ (7 / 16 + η : ℝ))
    (A := Km * (n₁ : ℝ) ^ (1 + η)) (m := Ke * (n₁ : ℝ) ^ (-E))
    (by positivity) (hminor n₁ hlt.le le_rfl hrself)
    (hminor n₂ le_rfl hlt.le hratio)
    (hmoment n₁ hlt.le le_rfl).1 (hmoment n₂ le_rfl hlt.le).1
    (hmoment n₁ hlt.le le_rfl).2 (hmoment n₂ le_rfl hlt.le).2
    (hNe n₁ hne)
  have hsroot : Real.sqrt (Km * (n₁ : ℝ) ^ (1 + η)) =
      Real.sqrt Km * (n₁ : ℝ) ^ ((1 + η) / 2) := by
    rw [Real.sqrt_mul hKm, Real.sqrt_eq_rpow ((n₁ : ℝ) ^ (1 + η)), ← Real.rpow_mul hn₁pos.le]
    congr 2
    ring
  have heroot : Real.sqrt (Ke * (n₁ : ℝ) ^ (-E)) =
      Real.sqrt Ke * (n₁ : ℝ) ^ (-E / 2) := by
    rw [Real.sqrt_mul hKe, Real.sqrt_eq_rpow ((n₁ : ℝ) ^ (-E)), ← Real.rpow_mul hn₁pos.le]
    congr 2
    ring
  let r : ℝ := (7 / 16 + η) * 2 + ((1 + η) / 2) * 3 + (-E / 2)
  have hexp : r ≤ 2 - ε := by dsimp [r, η, ε]; linarith
  have hrawpow : stripMass n₁ n₂ true + stripMass n₁ n₂ false ≤ Kraw * (n₁ : ℝ) ^ r := by
    calc
      _ ≤ 2 * (Kt * (n₁ : ℝ) ^ (7 / 16 + η : ℝ)) ^ 2 *
          Real.sqrt (Km * (n₁ : ℝ) ^ (1 + η)) ^ 3 *
          Real.sqrt (Ke * (n₁ : ℝ) ^ (-E)) := hraw
      _ = Kraw * (((n₁ : ℝ) ^ ((7 / 16 + η) * 2) *
          (n₁ : ℝ) ^ (((1 + η) / 2) * 3)) * (n₁ : ℝ) ^ (-E / 2)) := by
        rw [hsroot, heroot, mul_pow, mul_pow,
          ← Real.rpow_mul_natCast hn₁pos.le, ← Real.rpow_mul_natCast hn₁pos.le]
        dsimp [Kraw]
        ring
      _ = _ := by rw [← Real.rpow_add hn₁pos, ← Real.rpow_add hn₁pos]
  calc
    _ ≤ Kraw * (n₁ : ℝ) ^ r := hrawpow
    _ ≤ Kraw * (n₁ : ℝ) ^ (2 - ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn₁one hexp) hKraw
    _ = Kraw * ((n₁ : ℝ) * n₁) * (n₁ : ℝ) ^ (-ε) := by
      rw [show (2 : ℝ) - ε = 2 + -ε by ring, Real.rpow_add hn₁pos, Real.rpow_two]
      ring
    _ ≤ Kraw * ((n₁ : ℝ) * (C * n₂)) * (n₁ : ℝ) ^ (-ε) := by gcongr
    _ = (Kraw * C) * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε) := by ring

/-- LEAF. Hu pages 195 and 196, the two I bounds before multiplying by G.
This smaller analytic task contains no G to power 82 and no arc integral.
It needs the sectional Cauchy estimate, the four inputs above, and
absorption of the logarithms into the strict exponent reserve. -/
theorem strip_power_saving (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      stripMass n₁ n₂ true + stripMass n₁ n₂ false ≤
        K * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε) :=
  strip_power_saving_of_inputs C hC
    (fun ε hε => minor_prime_square_sup C ε hC hε)
    rieger_fourth_moment_bound
    platt_trudgian_slice_bound

/-- Page 194. The complement of the product major region is exactly the
union of the two minor coordinate strips after restricting to E. -/
theorem exceptional_minor_partition (n₁ n₂ : ℕ) :
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∩
      ((major n₁ n₂)ᶜ ∩ exceptional n₁) =
        minorStrip n₁ n₂ true ∪ minorStrip n₁ n₂ false := by
  ext α
  simp only [minorStrip, Bool.true_eq, ↓reduceIte, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, major, Set.mem_prod]
  tauto

/-- Pages 194 and 195. The base norm is continuous and nonnegative. -/
theorem continuous_baseNorm (n₁ n₂ : ℕ) : Continuous (baseNorm n₁ n₂) := by
  unfold baseNorm S T e
  fun_prop

/-- Pages 194 and 195. The strips are measurable. -/
theorem measurableSet_minorStrip (n₁ n₂ : ℕ) (first : Bool) :
    MeasurableSet (minorStrip n₁ n₂ first) := by
  cases first <;> exact
    ((measurableSet_Icc.prod measurableSet_Icc).inter (measurableSet_exceptional n₁)).inter
      (by simp only [Bool.false_eq_true, ↓reduceIte, minorStrip];
          first | exact (measurableSet_majorOne n₁ n₂).compl.preimage measurable_snd |
                  exact (measurableSet_majorOne n₁ n₁).compl.preimage measurable_fst)

/-- Page 194. The union estimate does not require disjoint strips. -/
theorem integral_union_le {s t : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfi : IntegrableOn f (s ∪ t)) (h0 : ∀ x, 0 ≤ f x) :
    (∫ x in s ∪ t, f x) ≤ (∫ x in s, f x) + ∫ x in t, f x := by
  have hid : s ∪ t = s ∪ (t \ s) := by ext x; simp
  rw [hid, setIntegral_union Set.disjoint_sdiff_right (ht.diff hs)
    (hfi.mono_set Set.subset_union_left)
    (hfi.mono_set (Set.Subset.trans Set.sdiff_subset Set.subset_union_right))]
  apply add_le_add le_rfl
  exact setIntegral_mono_set (hfi.mono_set Set.subset_union_right)
    (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall Set.sdiff_subset)

/-- Page 194. Taking out G to power 82 leaves the two strip masses. -/
theorem exceptional_arc_strip_bound (n₁ n₂ : ℕ) (hn₁ : 16 ≤ n₁) :
    |R2 n₁ n₂| ≤ L n₁ ^ 82 * (stripMass n₁ n₂ true + stripMass n₁ n₂ false) := by
  let U := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let A := U ∩ ((major n₁ n₂)ᶜ ∩ exceptional n₁)
  have hAU : A ⊆ U := Set.inter_subset_left
  have hA : MeasurableSet A :=
    (measurableSet_Icc.prod measurableSet_Icc).inter
      ((measurableSet_major n₁ n₂).compl.inter (measurableSet_exceptional n₁))
  have h0 : ∀ α, 0 ≤ baseNorm n₁ n₂ α := by intro α; unfold baseNorm; positivity
  have hfi : IntegrableOn (baseNorm n₁ n₂) U :=
    (continuous_baseNorm n₁ n₂).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hcf : IntegrableOn (fun α => L n₁ ^ 82 * baseNorm n₁ n₂ α) A :=
    (show IntegrableOn (fun α => L n₁ ^ 82 * baseNorm n₁ n₂ α) U volume from
      hfi.const_mul _).mono_set hAU
  have hpoint (α : ℝ × ℝ) : ‖integrand n₁ n₂ α‖ ≤ L n₁ ^ 82 * baseNorm n₁ n₂ α := by
    have hG := pow_le_pow_left₀ (norm_nonneg (G n₁ (α.1 + α.2)))
      (norm_G_le n₁ hn₁ (α.1 + α.2)) 82
    calc
      ‖integrand n₁ n₂ α‖ = ‖G n₁ (α.1 + α.2)‖ ^ 82 * baseNorm n₁ n₂ α := by
        simp only [integrand, norm_mul, norm_pow, norm_e, mul_one, baseNorm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hG (h0 α)
  calc
    |R2 n₁ n₂| ≤ ‖∫ α in A, integrand n₁ n₂ α‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ α in A, ‖integrand n₁ n₂ α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in A, L n₁ ^ 82 * baseNorm n₁ n₂ α :=
      setIntegral_mono_on ((integrableOn_integrand n₁ n₂).mono_set hAU).norm hcf hA
        (fun α _ => hpoint α)
    _ = L n₁ ^ 82 * ∫ α in A, baseNorm n₁ n₂ α := integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change (∫ α in A, baseNorm n₁ n₂ α) ≤ _
      rw [show A = minorStrip n₁ n₂ true ∪ minorStrip n₁ n₂ false from
        exceptional_minor_partition n₁ n₂]
      exact integral_union_le (measurableSet_minorStrip n₁ n₂ true)
        (measurableSet_minorStrip n₁ n₂ false)
        (hfi.mono_set (by
          intro α hα; rcases hα with hα | hα <;> exact hα.1.1)) h0


/-- Page 196. A positive power saving absorbs the one additional factor L. -/
theorem L_mul_rpow_neg_le_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → L n * (n : ℝ) ^ (-ε) ≤ 1 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hz.comp tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds htwo))
  refine ⟨max 16 N, ?_⟩
  intro n hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog1 : 1 ≤ Real.log n := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (show (16 : ℝ) ≤ n by exact_mod_cast hn16)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [h16] at hm
    linarith [Real.log_two_gt_d9]
  have hratio : (n : ℝ) / Real.log n ≤ n :=
    (div_le_iff₀ hlogpos).2 (by nlinarith)
  have hL : L n ≤ Real.log n / Real.log 2 := by
    unfold L Decomp115.logScale
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (div_pos hnpos hlogpos) hratio) htwo.le
  have hdecay : Real.log n / (n : ℝ) ^ ε ≤ Real.log 2 :=
    (hN n ((le_max_right _ _).trans hn)).le
  rw [Real.rpow_neg hnpos.le]
  calc
    L n * ((n : ℝ) ^ ε)⁻¹ ≤ (Real.log n / Real.log 2) * ((n : ℝ) ^ ε)⁻¹ :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = (Real.log n / (n : ℝ) ^ ε) / Real.log 2 := by ring
    _ ≤ 1 := (div_le_one htwo).2 hdecay

/-- Page 196. CONDITIONAL ON the smaller two strip power saving estimate.
This has the exact statement of the sealed exceptional arc leaf. -/
theorem exceptional_arc_order_bound (C : ℝ) (hC : 1 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      |R2 n₁ n₂| ≤ K * ((n₁ : ℝ) * n₂ * L n₁ ^ 81) := by
  obtain ⟨ε, hε, K, hK, N, hN⟩ := strip_power_saving C hC
  obtain ⟨N', hN'⟩ := L_mul_rpow_neg_le_one ε hε
  refine ⟨K, hK, max 16 (max N N'), ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have hn16 : 16 ≤ n₁ := ((le_max_left _ _).trans hn).trans hlt.le
  have hnN : N ≤ n₂ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnN' : N' ≤ n₁ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hn).trans hlt.le
  have hm := hN n₁ n₂ ho₁ ho₂ hnN hlt hratio
  have hdecay := hN' n₁ hnN'
  have hL : 0 ≤ L n₁ := (Decomp115.logScale_pos n₁ hn16).le
  calc
    |R2 n₁ n₂| ≤ L n₁ ^ 82 * (stripMass n₁ n₂ true + stripMass n₁ n₂ false) :=
      exceptional_arc_strip_bound n₁ n₂ hn16
    _ ≤ L n₁ ^ 82 * (K * ((n₁ : ℝ) * n₂) * (n₁ : ℝ) ^ (-ε)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (K * ((n₁ : ℝ) * n₂) * L n₁ ^ 81) * (L n₁ * (n₁ : ℝ) ^ (-ε)) := by ring
    _ ≤ (K * ((n₁ : ℝ) * n₂) * L n₁ ^ 81) * 1 :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

end LeanLab.Hathi2021.Decomp570b
