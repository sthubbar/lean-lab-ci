/-
P0093 pages 155 through 160 and page 166 equation 9.1.
Upstream ports of the finite character and principal mass proofs.
The source proofs are in SPLIT_doubled_system_characters1622 and Principal442.
Those files import Lemma6Split111 through Decomp111, so this port breaks that cycle.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.CircleSplit111
import LeanLab.Linnik1951.GaussBound376
import LeanLab.PNTPort.ZetaZeros.GammaBounds
import LeanLab.Perelli1996.TotientRatio320
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- P0093 page 159 before equation 5.1. The damped character prime series. -/
noncomputable def characterPrime519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ (p : ℕ) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- P0093 page 166 equation 9.1. The doubled rational system. -/
def arcSystem519 (q : ℕ) (τ : ℝ) : Set ℝ :=
  {x | ∃ r : ℚ, r.den = q ∧ |x - r| ≤ 2 / ((q : ℝ) * τ)}

/-- P0093 page 159 before equation 5.1. Character weighting preserves the
uniform geometric majorant of the damped prime series. -/
theorem continuous_character_prime519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) : Continuous (characterPrime519 χ N) := by
  unfold characterPrime519
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)


open MeasureTheory

/-- P0093 page 159 trivial full period bound before equation 5.3.
Parseval for an absolutely summable negative natural Fourier series. -/
theorem series_square_integral519 (a : ℕ → ℂ) (ha : Summable a) :
    (∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) =
        ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hf : Continuous (fun α : ℝ => ∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) := by
    apply continuous_tsum (u := fun n => ‖a n‖)
    · intro n
      fun_prop
    · exact ha.norm
    · intro n α
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hs : IntervalIntegrable (fun α : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) volume 0 1 :=
    (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => ∑' n : ℕ, a n *
          Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) i‖ ^ 2 := by
      simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm
    _ = _ := negative_modes_sum111_up111 _ _ (negative_series_coefficient_proved357_up111 a ha)

/-- P0093 page 159 before equation 5.3. Natural coefficient zero
extension of the character prime series, with absolute summability. -/
theorem character_coefficients_summable519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun n : ℕ => if n.Prime then
      χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (damping_summable111_up111 N hN)
  intro n
  by_cases hn : n.Prime
  · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)
  · simp [hn, (Real.exp_pos _).le]

/-- P0093 page 159 before equation 5.3. The subtype prime series
equals its zero extension over the natural frequencies. -/
theorem character_series_nat519 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (α : ℝ) :
    characterPrime519 χ N α = ∑' n : ℕ,
      (if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) *
        Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) := by
  classical
  let f : ℕ → ℂ := fun n => if n.Prime then χ n *
    (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) else 0
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact absurd (by simp [f, hp] : f n = 0) hn
  calc
    _ = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold characterPrime519
      apply tsum_congr
      intro p
      simp only [f, if_pos p.property]
    _ = ∑' n : ℕ, f n := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hn : n.Prime <;> simp [f, hn]

/-- P0093 page 159 before equation 5.3. Every character has full
period square mass at most two N. The estimate discards primality and
uses the geometric damping sum. No prime number theorem is needed. -/
theorem character_full_mass519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖characterPrime519 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  classical
  simp_rw [character_series_nat519]
  rw [series_square_integral519 _ (character_coefficients_summable519 χ N hN)]
  have he : ∀ n : ℕ,
      ‖if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0‖ ^ 2 ≤
        Real.exp (-2 * (n : ℝ) / N) := by
    intro n
    by_cases hn : n.Prime
    · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc := pow_le_pow_left₀ (norm_nonneg (χ n)) (χ.norm_le_one n) 2
      have heq : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-2 * (n : ℝ) / N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc
        _ = ‖χ n‖ ^ 2 * Real.exp (-(n : ℝ) / N) ^ 2 := by ring
        _ ≤ 1 * Real.exp (-(n : ℝ) / N) ^ 2 :=
          mul_le_mul_of_nonneg_right (by simpa using hc) (by positivity)
        _ = _ := by rw [one_mul, heq]
    · simp [hn, (Real.exp_pos _).le]
  have hh := laplace_bound111_up111 (fun _ => (1 : ℝ)) 1 N hN (by norm_num)
    (fun _ => by norm_num) (by intro M; simp)
  have hg : Summable (fun n : ℕ => Real.exp (-2 * (n : ℝ) / N)) := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr : ‖Real.exp (-2 / (N : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hNp)
    have hs := summable_geometric_of_norm_lt_one hr
    convert hs using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N) :=
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _) he hg).tsum_le_tsum he hg
    _ ≤ _ := by simpa using hh

/-- P0093 page 159 before equation 5.3. Integer frequency character
sums have period one in the additive phase. -/
theorem character_periodic519 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Function.Periodic (characterPrime519 χ N) 1 := by
  intro α
  unfold characterPrime519
  apply tsum_congr
  intro p
  congr 1
  have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
        ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
  rw [hp, mul_one]

/-- P0093 page 159 before equation 5.3. The local square mass on a
symmetric interval of radius at most one half is at most the full
period square mass. -/
theorem character_local_mass519 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    (∫ α in -r..r, ‖characterPrime519 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  have hc := (continuous_character_prime519 χ N hN).norm.pow 2
  have hp : Function.Periodic (fun α => ‖characterPrime519 χ N α‖ ^ 2) 1 :=
    (character_periodic519 χ N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖characterPrime519 χ N α‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact hi.trans (he.trans_le (character_full_mass519 χ N hN))


open MeasureTheory Filter Finset

/-- The reduced residues below q number the totient of q, in the form the assembly
uses for the counting of the doubled intervals. -/
private theorem card_reduced1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

/-- LEAF. The covering step of the geometry. For q at least two and tau at least four,
every point of the arc system of denominator q that lies in the unit interval lies in
one of the doubled rational intervals of radius two over q tau about a reduced residue
below q. Only rational arithmetic and the positivity of q and tau are used; no
integration, no character and no bound on the prime system occurs. -/
theorem rational_cover519 (q : ℕ) [NeZero q] (τ : ℝ) (hq : 2 ≤ q) (hτ : 4 ≤ τ) :
    arcSystem519 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
  rintro x ⟨⟨r, hrden, hrδ⟩, hx0, hx1⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hRle : 2 / ((q : ℝ) * τ) ≤ 1 / (2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le] at hrδ
  obtain ⟨hrlo, hrhi⟩ := hrδ
  have hrcq : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hrden]
  have hcop : r.num.natAbs.Coprime q := by
    have h := r.reduced
    rwa [hrden] at h
  have hnum_nonneg : 0 ≤ r.num := by
    by_contra hneg
    push_neg at hneg
    have hle : (r.num : ℝ) ≤ -1 := by
      have : r.num ≤ -1 := by omega
      exact_mod_cast this
    have hrle : (r : ℝ) ≤ -1 / (q : ℝ) := by
      rw [hrcq, div_le_div_iff₀ hqpos hqpos]
      nlinarith
    have hxle : x ≤ -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) := by linarith
    have hneg' : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) < 0 := by
      have hsplit : -1 / (q : ℝ) + 1 / (2 * (q : ℝ)) = -(1 / (2 * (q : ℝ))) := by
        field_simp
        ring
      rw [hsplit]
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  have hnum_lt : r.num < (q : ℤ) := by
    by_contra hge
    push_neg at hge
    have hne : r.num ≠ (q : ℤ) := by
      intro he
      have hnat : r.num.natAbs = q := by
        rw [he]
        exact Int.natAbs_natCast q
      rw [hnat] at hcop
      have hq1 : q = 1 := Nat.coprime_self q |>.mp hcop
      omega
    have hge' : (q : ℤ) + 1 ≤ r.num := by omega
    have hcastZ : ((q : ℤ) : ℝ) + 1 ≤ (r.num : ℝ) := by exact_mod_cast hge'
    have hcast : (q : ℝ) + 1 ≤ (r.num : ℝ) := by
      have hqZ : ((q : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      linarith
    have hrbig : 1 + 1 / (q : ℝ) ≤ (r : ℝ) := by
      rw [hrcq, le_div_iff₀ hqpos]
      have hmul : (1 + 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) + 1 := by
        field_simp
      rw [hmul]
      exact hcast
    have hxge : 1 + 1 / (2 * (q : ℝ)) ≤ x := by
      have hsplit : (1 : ℝ) + 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 + 1 / (2 * (q : ℝ)) := by
        field_simp
        ring
      linarith
    have : (1 : ℝ) < 1 + 1 / (2 * (q : ℝ)) := by
      have : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    linarith
  set a := r.num.toNat with hadef
  have hanum : (a : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
  have halt : a < q := by
    have h' : (a : ℤ) < (q : ℤ) := by rw [hanum]; exact hnum_lt
    exact_mod_cast h'
  have hcopa : Nat.Coprime a q := by
    have hna : r.num.natAbs = a := by
      rw [hadef]
      have h1 : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum_nonneg
      have h2 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum_nonneg
      exact_mod_cast h1.trans h2.symm
    rwa [hna] at hcop
  have hcasta : (a : ℝ) = (r.num : ℝ) := by
    have : (a : ℝ) = ((a : ℤ) : ℝ) := by push_cast; ring
    rw [this, hanum]
  have hmem : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨halt, hcopa⟩
  have hxI : x ∈ Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
      ((a : ℝ) / q + 2 / ((q : ℝ) * τ)) := by
    have e1 : (a : ℝ) / q - 2 / ((q : ℝ) * τ) = (r : ℝ) - 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    have e2 : (a : ℝ) / q + 2 / ((q : ℝ) * τ) = (r : ℝ) + 2 / ((q : ℝ) * τ) := by
      rw [hcasta, hrcq]
    rw [Set.mem_Icc, e1, e2]
    constructor <;> linarith
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨a, hmem, hxI⟩


/-- LEAF. The integral step of the geometry. For a nonnegative continuous function and a
cover of the clipped arc system by the doubled intervals of the reduced residues, the
integral over the clipped system is at most the integral over the radius interval of the
sum of the shifted values at the reduced residues. This is subadditivity of the integral
over a finite union together with translation of the interval, so it uses no property of
the function beyond nonnegativity and continuity, and none of the characters. -/
theorem rational_cover_integral519 (q : ℕ) [NeZero q] (τ : ℝ) (hτ : 0 < τ) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ x : ℝ, 0 ≤ f x)
    (hcover : arcSystem519 q τ ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ)) ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) :
    (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1, f α) ≤
      ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f ((a : ℝ) / q + z) := by
  classical
  let r : ℝ := 2 / ((q : ℝ) * τ)
  let S := (Finset.range q).filter (fun a => Nat.Coprime a q)
  let t : ℕ → Set ℝ := fun a => Set.Icc ((a : ℝ) / q - r) ((a : ℝ) / q + r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hi (a : ℕ) : IntegrableOn f (t a) := hf.integrableOn_Icc
  have hU : (∫ x in ⋃ a ∈ S, t a, f x) ≤ ∑ a ∈ S, ∫ x in t a, f x := by
    clear hcover
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      have hiU : IntegrableOn f (⋃ i ∈ S, t i) :=
        integrableOn_finset_iUnion.mpr (fun i _ => hi i)
      have hle := integral_mono_measure
        (Measure.restrict_union_le (μ := volume) (t a) (⋃ i ∈ S, t i))
        (ae_of_all _ hn) (integrable_add_measure.mpr ⟨hi a, hiU⟩)
      rw [integral_add_measure (hi a) hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert ha]
      exact hle.trans (add_le_add le_rfl ih)
  have hiU : IntegrableOn f (⋃ a ∈ S, t a) :=
    integrableOn_finset_iUnion.mpr (fun a _ => hi a)
  calc
    _ ≤ ∫ x in ⋃ a ∈ S, t a, f x :=
      setIntegral_mono_set hiU (ae_of_all _ hn) (ae_of_all _ hcover)
    _ ≤ ∑ a ∈ S, ∫ x in t a, f x := hU
    _ = ∑ a ∈ S, ∫ z in -r..r, f ((a : ℝ) / q + z) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [t]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (a : ℝ) / q - r ≤ (a : ℝ) / q + r),
        intervalIntegral.integral_comp_add_left]
      simp only [sub_eq_add_neg]
    _ = _ := by
      change (∑ a ∈ S, ∫ z in -r..r, f ((a : ℝ) / q + z)) =
        ∫ z in -r..r, ∑ a ∈ S, f ((a : ℝ) / q + z)
      exact (intervalIntegral.integral_finsetSum
        (fun a _ => (hf.comp (continuous_const.add continuous_id)).intervalIntegrable (-r) r)).symm




open MeasureTheory Finset

/-- The phase of the residue `m` modulo `q`, as an `n`-th power. -/
private theorem exp_phase_nat (q m a : ℕ) (hq : 0 < q) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ a := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- Complete residue sums vanish off the divisibility condition. -/
private theorem full_sum_nat (q m : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q ∣ m then (q : ℂ) else 0 := by
  classical
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) ^ q = 1 := by
    rw [← exp_phase_nat q m q hq]
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (q : ℂ) / (q : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / ((1 : ℕ) : ℂ) := by
      field_simp
      ring
    rw [harg, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by norm_num : (1 : ℕ) ≠ 0)]
    exact one_dvd m
  simp_rw [exp_phase_nat q m _ hq]
  by_cases hdiv : q ∣ m
  · rw [if_pos hdiv]
    have hone : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) = 1 := by
      rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne']
      exact hdiv
    rw [hone]
    simp
  · rw [if_neg hdiv]
    have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ)) - 1 ≠ 0 := by
      intro h0
      apply hdiv
      rw [sub_eq_zero] at h0
      have := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := m) (N := q) hq.ne').mp h0
      exact this
    have hmul := geom_sum_mul (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ))) q
    rw [hpower, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hne

/-- The sum over the multiples of a divisor reduces to the quotient modulus. -/
private theorem multiples_sum_nat (q d m : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (a : ℂ) / (q : ℂ))) =
      if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hq
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  have hqeq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hfilter : (Finset.range q).filter (fun a => d ∣ a) =
      (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      rw [hqeq] at ha
      exact ⟨b, (Nat.mul_lt_mul_left hd0).mp ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by rw [hqeq]; exact (Nat.mul_lt_mul_left hd0).mpr hb, ⟨b, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · have heq (b : ℕ) :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((d * b : ℕ) : ℂ) / (q : ℂ))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) *
              (b : ℂ) / ((q / d : ℕ) : ℂ)) := by
      congr 1
      conv_lhs => rw [hqeq]
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hqdC : ((q / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hqd.ne'
      push_cast
      field_simp
    simp_rw [heq]
    exact full_sum_nat (q / d) m hqd
  · intro b _ c _ heq
    exact Nat.eq_of_mul_eq_mul_left hd0 heq

/-- Möbius inversion gives the coprimality indicator at every positive modulus. -/
private theorem coprime_indicator_nat (q a : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  classical
  have hset : q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd a q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
    simp [hg, hq.ne', and_comm]
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd a q))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one] using h

/-- The Ramanujan sum at argument one is the Möbius function of the modulus. -/
private theorem ramanujan_sum_one_nat (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  have heq (a : ℕ) :
      (if Nat.Coprime a q then
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) =
        (∑ d ∈ q.divisors,
            if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [coprime_indicator_nat q a hq]
    split_ifs <;> simp
  rw [Finset.sum_filter]
  simp_rw [heq, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hstep : ∀ d ∈ q.divisors,
      (∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ))) =
        (ArithmeticFunction.moebius d : ℂ) *
          (if q / d ∣ 1 then ((q / d : ℕ) : ℂ) else 0) := by
    intro d hd
    have hdd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hone : ∀ a ∈ Finset.range q,
        (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) =
          (ArithmeticFunction.moebius d : ℂ) *
            (if d ∣ a then
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) else 0) := by
      intro a _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hone, ← Finset.mul_sum, ← Finset.sum_filter,
      multiples_sum_nat q d 1 hq hdd]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_eq_single q]
  · rw [Nat.div_self hq]
    simp
  · intro d hd hdne
    have hnot : ¬ q / d ∣ 1 := by
      intro h1
      have hqd1 : q / d = 1 := Nat.dvd_one.mp h1
      have h := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rw [hqd1, mul_one] at h
      exact hdne h
    rw [if_neg hnot, mul_zero]
  · intro hnot
    exact absurd (Nat.mem_divisors_self q hq.ne') hnot



/-! ### The principal Gauss vector of the unit group

The unit sum of the additive character is the Ramanujan sum at argument one, so its
modulus is at most one, and the same holds for the conjugate sum that the Gauss vector of
the principal character is. -/

/-- The unit sum of the additive character has modulus at most one. -/
private theorem unit_sum_addChar_le_one (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c‖ ≤ 1 := by
  classical
  have hq : 0 < q := NeZero.pos q
  have hfil : (Finset.range q).filter (fun a => IsUnit ((a : ℕ) : ZMod q))
      = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    refine Finset.filter_congr ?_
    intro a _
    exact ZMod.isUnit_iff_coprime a q
  have hconv :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c)
        = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℕ) : ℂ) * (a : ℂ) / (q : ℂ)) := by
    rw [Finset.sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, ← Finset.sum_filter,
      hfil]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Int.cast_natCast a, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hconv, ramanujan_sum_one_nat q hq, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- The Gauss vector of the principal character at the unit shift one has modulus at most
one: it is the conjugate of the unit sum of the additive character. -/
private theorem unit_gauss_principal_le (q : ℕ) [NeZero q] :
    ‖∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(1 * c))‖ ≤ 1 := by
  have hconj :
      (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-(1 * c)))
        = (starRingEnd ℂ)
            (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [LeanLab.PNTPort.LargeSieve.conj_stdAddChar]
    simp
  rw [hconj, Complex.norm_conj]
  exact unit_sum_addChar_le_one q

/-! ### Counting the primes that divide the modulus

At most `log_2 q` primes divide `q`, since their product is at most `q`; the correction
terms of the prime series are supported on exactly those primes. -/

/-- The number of distinct prime divisors of a positive integer obeys `2 ^ ω ≤ q`. -/
private theorem two_pow_primeFactors_card_le (q : ℕ) (hq : 0 < q) :
    2 ^ q.primeFactors.card ≤ q := by
  have h2 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact h2.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))

/-- The count of distinct prime divisors is at most twice the logarithm. -/
private theorem primeFactors_card_le_log (q : ℕ) (hq : 2 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have hq0 : 0 < q := by omega
  have hle : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le q hq0
  have hpos : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card := by positivity
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq : (1 : ℝ) < q)
  nlinarith

/-- The tail of the prime series at a unit residue is supported on the primes dividing `q`,
and each of its terms has modulus at most one. -/
private theorem corr_bound (N q : ℕ) [NeZero q] (hq : 2 ≤ q) (z : ℝ) (a : ZMod q) :
    ‖∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 2 * Real.log q := by
  classical
  let emb : Function.Embedding {d // d ∈ q.primeFactors} Nat.Primes :=
    ⟨fun d => (⟨d.1, (Nat.mem_primeFactors.mp d.2).1⟩ : Nat.Primes),
      fun x y hxy => Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hxy)⟩
  set sf : Finset Nat.Primes := q.primeFactors.attach.map emb with hsf
  have hmem : ∀ p : Nat.Primes, p ∉ sf → IsUnit (((p : ℕ)) : ZMod q) := by
    intro p hp
    by_contra hnu
    apply hp
    have hpnot : ¬ Nat.Coprime (p : ℕ) q :=
      fun h => hnu ((ZMod.isUnit_iff_coprime (p : ℕ) q).mpr h)
    have hdvd : (p : ℕ) ∣ q := by
      have hg : Nat.gcd (p : ℕ) q ∣ (p : ℕ) := Nat.gcd_dvd_left _ _
      have hg1 : Nat.gcd (p : ℕ) q ≠ 1 := fun h => hpnot (Nat.coprime_iff_gcd_eq_one.mpr h)
      rcases Nat.Prime.eq_one_or_self_of_dvd p.2 (Nat.gcd (p : ℕ) q) hg with h1 | h1
      · exact absurd h1 hg1
      · exact h1 ▸ Nat.gcd_dvd_right _ _
    have hmem' : (p : ℕ) ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨p.2, hdvd, by omega⟩
    rw [hsf, Finset.mem_map]
    exact ⟨⟨(p : ℕ), hmem'⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hcard : sf.card = q.primeFactors.card := by
    rw [hsf]
    simp
  have hterm : ∀ p : Nat.Primes,
      ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ ≤ 1 := by
    intro p
    by_cases hp : IsUnit (((p : ℕ)) : ZMod q)
    · rw [if_pos hp, norm_zero]; norm_num
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.mpr ?_
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have hzero : ∀ p : Nat.Primes, p ∉ sf →
      (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) = 0 := by
    intro p hp
    rw [if_pos (hmem p hp)]
  rw [tsum_eq_sum hzero]
  calc ‖∑ p ∈ sf, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖
      ≤ ∑ p ∈ sf, ‖(if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ sf, (1 : ℝ) := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (sf.card : ℝ) := by simp
    _ = (q.primeFactors.card : ℝ) := by rw [hcard]
    _ ≤ 2 * Real.log q := primeFactors_card_le_log q hq




open MeasureTheory Filter Finset

/-! ### Finite character expansion

The character table expands the additive character on the units.
The unit Gauss vector is written out as an explicit finite sum at every use site.
-/

open MeasureTheory Filter Finset Complex
open LeanLab.PNTPort.LargeSieve
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Character-table expansion of the additive character on the units. -/
private theorem sum_Gunit_mul_char (a b : ZMod q) (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b
      = (q.totient : ℂ) * ZMod.stdAddChar (-(a * b)) := by
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ b = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
        ZMod.stdAddChar (-(a * c)) * χ (c⁻¹ * b) := by
    intro χ
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, hcu⟩ := hc
    rw [conj_char_of_isUnit χ hcu, mul_assoc, ← map_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq,
      if_pos (ZMod.inv_mul_of_unit b hb)]
    ring
  · intro c hc hcb
    rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq, if_neg ?_]
    · simp
    · intro h
      apply hcb
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hcu⟩ := hc
      have h2 : c * (c⁻¹ * b) = c * 1 := by rw [h]
      rw [← mul_assoc, ZMod.mul_inv_of_unit c hcu, one_mul, mul_one] at h2
      exact h2.symm
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩) hnot

/-- `G` is multiplicative in the additive shift: on units it is `χ a` times `G χ 1`. -/
private theorem Gunit_eq_mul (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) = χ a * (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) := by
  classical
  have hainv : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  have hbinv : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have hau : IsUnit a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    exact ⟨u⁻¹, by simp⟩
  have hinv2 : a⁻¹⁻¹ = a := by
    calc a⁻¹⁻¹ = a⁻¹⁻¹ * 1 := (mul_one _).symm
      _ = a⁻¹⁻¹ * (a⁻¹ * a) := by rw [hainv]
      _ = a⁻¹⁻¹ * a⁻¹ * a := by rw [mul_assoc]
      _ = 1 * a := by rw [ZMod.inv_mul_of_unit a⁻¹ hau]
      _ = a := one_mul a
  have hconj : (starRingEnd ℂ) (χ a⁻¹) = χ a := by
    rw [conj_char_of_isUnit χ hau, hinv2]
  have hstep : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ d ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar (-d) * (starRingEnd ℂ) (χ (a⁻¹ * d)) := by
    skip
    refine Finset.sum_nbij' (fun c => a * c) (fun c => a⁻¹ * c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, ha.mul hc.2⟩
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, hau.mul hc.2⟩
    · intro c hc
      show a⁻¹ * (a * c) = c
      rw [← mul_assoc, hainv, one_mul]
    · intro c hc
      show a * (a⁻¹ * c) = c
      rw [← mul_assoc, hbinv, one_mul]
    · intro c hc
      show ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ c)
        = ZMod.stdAddChar (-(a * c)) * (starRingEnd ℂ) (χ (a⁻¹ * (a * c)))
      rw [← mul_assoc, hainv, one_mul]
  rw [hstep]
  skip
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_filter] at hd
  simp only [map_mul, hconj, one_mul]
  ring



/-- A nontrivial Dirichlet character has vanishing sum over the units. -/
private theorem sum_unit_char_of_ne_one {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a = 0 := by
  classical
  have hex : ∃ u : (ZMod q)ˣ, ψ ((u : ZMod q)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (MulChar.ext_iff.mpr (fun u => by rw [h u]; simp))
  obtain ⟨u, hu⟩ := hex
  have huo : IsUnit ((u : ZMod q)) := u.isUnit
  have hji : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, (u⁻¹).isUnit.mul ha.2⟩
  have hbi : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a) := by
    refine Finset.sum_nbij' (fun a => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) (fun a => (u : ZMod q) * a)
      hji ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, huo.mul ha.2⟩
    · intro a ha
      show (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) = a
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * a) = a
      have h1 : (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * (u : ZMod q) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
    · intro a ha
      show ψ a = ψ ((u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a))
      have h1 : (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← mul_assoc, h1, one_mul]
  have hfac : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ ((u : ZMod q) * a)
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_mul]
  have hS : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a
      = ψ (u : ZMod q) * ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a :=
    hbi.trans hfac
  have hz : (1 - ψ (u : ZMod q)) *
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), ψ a) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  refine (mul_eq_zero.1 hz).resolve_left ?_
  intro hc
  exact hu (sub_eq_zero.1 hc).symm

/-- `χ·conj χ'` summed over the units: the totient at `χ = χ'`, zero otherwise. -/
private theorem sum_unit_char_mul_inv (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), χ a * χ' a⁻¹
      = if χ = χ' then (q.totient : ℂ) else 0 := by
  classical
  set ψ : DirichletCharacter ℂ q := χ * χ'⁻¹ with hpsi
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      χ a * χ' a⁻¹ = ψ a := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [hpsi, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    congr 1
    have hmul : χ' a⁻¹ * χ' a = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit a hau, map_one]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [Finset.sum_congr rfl hpt]
  by_cases hχ : χ = χ'
  · subst hχ
    rw [if_pos rfl]
    have hψ1 : ψ = 1 := by rw [hpsi]; simp
    rw [hψ1]
    have hconst : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (1 : DirichletCharacter ℂ q) a = (1 : ℂ) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨v, rfl⟩ := ha.2
      simp
    rw [Finset.sum_congr rfl hconst, Finset.sum_filter]
    have hC : ∑ x : ZMod q, (if IsUnit x then (1 : ℂ) else 0) = (q.totient : ℂ) := by
      have hR := sum_isUnit_eq_totient (q := q)
      have h2 : ((∑ x : ZMod q, (if IsUnit x then (1 : ℝ) else 0) : ℝ) : ℂ) = (q.totient : ℂ) := by
        rw [hR]
        push_cast
        ring
      rw [← h2]
      push_cast
      ring_nf
      congr 1
      funext x
      by_cases hx : IsUnit x <;> simp [hx]
    exact hC
  · rw [if_neg hχ]
    refine sum_unit_char_of_ne_one ?_
    intro h
    apply hχ
    rw [hpsi] at h
    have h2 := congrArg (fun t => t * χ') h
    simp only [one_mul] at h2
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h2

/-- The Gauss vectors of two characters are orthogonal over the units. -/
private theorem sum_Gunit_orth (χ χ' : DirichletCharacter ℂ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
      = if χ = χ' then (q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))) else 0 := by
  classical
  have hpt : ∀ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
      (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))
        = (χ a * χ' a⁻¹) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hau⟩ := ha
    rw [Gunit_eq_mul χ hau, Gunit_eq_mul χ' hau, map_mul, conj_char_of_isUnit χ' hau]
    ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, sum_unit_char_mul_inv]
  by_cases h : χ = χ'
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The principal Gauss vector: the additive character of the units is the conjugate of
the Ramanujan sum, so its norm is `|μ(q)|`. -/
private theorem Gunit_one_principal_le (hq : 0 < q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ≤ 1 := by
  classical
  have hU : ∀ c : ZMod q, (1 : DirichletCharacter ℂ q) c = if IsUnit c then (1 : ℂ) else 0 := by
    intro c
    by_cases hc : IsUnit c
    · rw [if_pos hc]
      obtain ⟨v, rfl⟩ := hc
      simp
    · rw [if_neg hc, MulChar.map_nonunit _ hc]
  have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
      = ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c) := by
    skip
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [hU c, if_pos hc.2]
    simp
  have hconj : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar (-c)
      = (starRingEnd ℂ) (∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c),
          ZMod.stdAddChar c) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    exact (LeanLab.PNTPort.LargeSieve.conj_stdAddChar c).symm
  have hram : ∑ c ∈ (Finset.univ : Finset (ZMod q)).filter (fun c => IsUnit c), ZMod.stdAddChar c
      = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1 := by
    rw [Finset.sum_filter, sum_zmod_eq_sum_range]
    unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rw [Finset.mem_range] at hc
    by_cases hcop : Nat.Coprime c q
    · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 hcop), if_pos hcop]
      have hone : ((c : ZMod q)) = ((1 : ℤ) : ZMod q) * (c : ZMod q) := by simp
      rw [hone, stdAddChar_mul_natCast (q := q) 1 c]
      congr 1
      push_cast
      ring
    · rw [if_neg (fun h => hcop ((ZMod.isUnit_iff_coprime c q).1 h)), if_neg hcop]
  have hmu : LeanLab.Perelli1996.Ramanujan103.ramanujanSum q 1
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 hq (Nat.coprime_one_right q)
  rw [hG, hconj, norm_conj, hram, hmu, Complex.norm_intCast]
  have h1 : |(ArithmeticFunction.moebius q : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast h1

/-- `G χ 1` is the Gauss sum of `χ⁻¹`, so its square norm is at most the modulus. -/
private theorem Gunit_one_norm_sq_le (χ : DirichletCharacter ℂ q) : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 ≤ (q : ℝ) := by
  have hcongr : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))
      = ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a := by
    skip
    rw [Finset.sum_filter (s := Finset.univ)]
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.inv_apply_eq_inv']
      have h1 : (χ a)⁻¹ = (starRingEnd ℂ) (χ a) := by
        have hnorm : ‖χ a‖ = 1 := by
          rw [show a = ((ha.unit : (ZMod q)ˣ) : ZMod q) from ha.unit_spec.symm]
          exact DirichletCharacter.unit_norm_eq_one χ ha.unit
        rw [Complex.inv_eq_conj hnorm]
      rw [h1]
      have h2 : ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a = ZMod.stdAddChar (-(1 * a)) := by
        rw [AddChar.mulShift_apply]
        simp
      rw [h2]
      ring
    · rw [if_neg ha, MulChar.map_nonunit _ ha, zero_mul]
  rw [hcongr]
  have hgs : (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q) a)
      = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (((-1 : (ZMod q)ˣ)) : ZMod q)) := rfl
  rw [hgs, gaussSum_mulShift_eq, norm_mul, mul_pow]
  rw [show χ⁻¹⁻¹ = χ from inv_inv χ]
  have hχ1 : ‖χ (((-1 : (ZMod q)ˣ)) : ZMod q)‖ ^ 2 = 1 := by
    rw [normSq_char (χ := χ) (((-1 : (ZMod q)ˣ)) : ZMod q), if_pos ((-1 : (ZMod q)ˣ).isUnit)]
  rw [hχ1, one_mul]
  have hb := LeanLab.Linnik1951.gauss_norm_le376 (χ⁻¹)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsq : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 ≤ (Real.sqrt (q : ℝ)) ^ 2 := by
    nlinarith [hb, norm_nonneg (gaussSum χ⁻¹ ZMod.stdAddChar)]
  rwa [Real.sq_sqrt hq0] at hsq

/-- Per-prime character expansion: on a prime whose residue is a unit, the additive character
of the shifted fraction is `1/φ` times the Gauss-weighted character sum. -/
private theorem char_expansion_pointwise (q : ℕ) [NeZero q] (a : ZMod q) (p : Nat.Primes)
    (hp : IsUnit ((p : ℕ) : ZMod q)) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q)))
      = (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q) := by
  rw [sum_Gunit_mul_char a ((p : ℕ) : ZMod q) hp]
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  field_simp

/-- Splitting the exponential of the shifted fraction into the residue phase and the shift. -/
private theorem exp_split_phase (q : ℕ) [NeZero q] (z : ℝ) (a : ZMod q) (p : Nat.Primes) :
    ZMod.stdAddChar (-(a * ((p : ℕ) : ZMod q))) *
        Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = Complex.exp
          ((-(2 * Real.pi * (((a.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have h1 : ((a.val : ℕ) : ZMod q) = a := ZMod.natCast_zmod_val a
  have h2 : ((((p : ℕ) : ℤ)) : ZMod q) = ((p : ℕ) : ZMod q) := Int.cast_natCast _
  have hpos : a * ((p : ℕ) : ZMod q) = ((↑((a.val : ℤ) * ((p : ℕ) : ℤ))) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, h1]
  rw [(LeanLab.PNTPort.LargeSieve.conj_stdAddChar (a * ((p : ℕ) : ZMod q))).symm, hpos,
    ZMod.stdAddChar_coe, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast,
    map_ofNat]
  ring


/-- Pointwise expansion of the prime series at a shifted unit fraction. -/
private theorem prime_fourier_expansion (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (a : ZMod q) :
    primeFourier111_up111 N ((a.val : ℝ) / q + z) =
      (1 / (q.totient : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z +
        ∑' p : Nat.Primes, (if IsUnit ((p : ℕ) : ZMod q) then 0
          else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
  classical
  have hφ : ((q.totient : ℂ)) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  set F : Nat.Primes → DirichletCharacter ℂ q → ℂ := fun p χ =>
    (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (χ ((p : ℕ) : ZMod q) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) with hF
  have hsumF : ∀ χ : DirichletCharacter ℂ q, Summable (fun p : Nat.Primes => F p χ) := by
    intro χ
    have hb : Summable (fun p : Nat.Primes => ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N)) :=
      ((damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective).mul_left _
    refine Summable.of_norm_bounded hb (fun p => ?_)
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul]
    have he : ‖Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    have hce : ‖(Real.exp (-((p : ℕ) : ℝ) / N) : ℂ)‖ = Real.exp (-((p : ℕ) : ℝ) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hχ : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := by
      have h2 : ‖χ ((p : ℕ) : ZMod q)‖ ^ 2 ≤ 1 := by
        rw [normSq_char]
        split_ifs <;> norm_num
      nlinarith [norm_nonneg (χ ((p : ℕ) : ZMod q))]
    rw [he, hce, mul_one]
    have hc0 : 0 ≤ Real.exp (-((p : ℕ) : ℝ) / N) := (Real.exp_pos _).le
    have hstep : ‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N)
        ≤ 1 * Real.exp (-((p : ℕ) : ℝ) / N) :=
      mul_le_mul_of_nonneg_right hχ hc0
    calc ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (‖χ ((p : ℕ) : ZMod q)‖ * Real.exp (-((p : ℕ) : ℝ) / N))
        ≤ ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * (1 * Real.exp (-((p : ℕ) : ℝ) / N)) :=
          mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
      _ = ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG))‖ * Real.exp (-((p : ℕ) : ℝ) / N) := by ring
  have hp_id : ∀ p : Nat.Primes,
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)
      = (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q, F p χ)
          + (if IsUnit ((p : ℕ) : ZMod q) then 0
              else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
                Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
    intro p
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, add_zero, ← exp_split_phase (q := q) z a p]
      rw [char_expansion_pointwise (q := q) a p hp]
      have hL : (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          ((1 / (q.totient : ℂ)) *
            (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
          = ∑ χ : DirichletCharacter ℂ q, (1 / (q.totient : ℂ)) * F p χ := by
        rw [show (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            ((1 / (q.totient : ℂ)) *
              (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))
            = (1 / (q.totient : ℂ)) *
              ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * χ ((p : ℕ) : ZMod q)) *
              ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) by ring]
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        simp only [hF]
        ring
      rw [hL, Finset.mul_sum]
    · have hS : (∑ χ : DirichletCharacter ℂ q, F p χ) = 0 := by
        refine Finset.sum_eq_zero (fun χ _ => ?_)
        simp only [hF]
        rw [MulChar.map_nonunit _ hp]
        ring
      rw [if_neg hp, hS, mul_zero, zero_add]
  have hsA : Summable (fun p : Nat.Primes => (1 / (q.totient : ℂ)) *
      (∑ χ : DirichletCharacter ℂ q, F p χ)) := by
    have h : Summable (fun p : Nat.Primes => ∑ χ : DirichletCharacter ℂ q, F p χ) :=
      summable_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (f := fun (χ : DirichletCharacter ℂ q) (p : Nat.Primes) => F p χ)
        (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) => hsumF χ)
    exact h.mul_left _
  have hsB : Summable (fun p : Nat.Primes => (if IsUnit ((p : ℕ) : ZMod q) then 0
      else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a.val : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I))) := by
    have hb := (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
    refine Summable.of_norm_bounded hb (fun p => ?_)
    by_cases hp : IsUnit ((p : ℕ) : ZMod q)
    · rw [if_pos hp, norm_zero]
      exact (Real.exp_pos _).le
    · rw [if_neg hp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_rfl
  rw [primeFourier111_up111, tsum_congr hp_id, Summable.tsum_add hsA hsB]
  congr 1
  rw [tsum_mul_left]
  congr 1
  have hswap : (∑' (p : Nat.Primes), ∑ χ : DirichletCharacter ℂ q, F p χ)
      = ∑ χ : DirichletCharacter ℂ q, ∑' (p : Nat.Primes), F p χ :=
    Summable.tsum_finsetSum (fun χ (_ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) =>
      hsumF χ)
  rw [hswap]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [characterPrime519, ← tsum_mul_left]

/-- The squared character combination summed over the reduced residues. The Gauss vectors of
distinct characters are orthogonal, so only the diagonal survives: the sum is the totient times
the character squares weighted by the squared Gauss norms at `1`. -/
private theorem sum_normSq_chi_combo (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2
      = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
  classical
  have hreal : ∀ w : ℂ, ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hresumA : ∀ f : ZMod q → ℂ,
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), (f a).re)
        = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a), f a).re := by
    intro f
    have h := map_sum Complex.reCLM f
      ((Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a))
    simpa only [Complex.reCLM_apply] using h.symm
  have hresumC : ∀ f : DirichletCharacter ℂ q → ℂ,
      (∑ χ : DirichletCharacter ℂ q, (f χ).re) = (∑ χ : DirichletCharacter ℂ q, f χ).re := by
    intro f
    have h := map_sum Complex.reCLM f (Finset.univ : Finset (DirichletCharacter ℂ q))
    simpa only [Complex.reCLM_apply] using h.symm
  have hre : ∀ χ : DirichletCharacter ℂ q,
      ((characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
          ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re
        = (q.totient : ℝ) * (‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
    intro χ
    rw [Complex.mul_conj, Complex.mul_conj]
    rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) by simp]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  have hcomplex :
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = ∑ χ : DirichletCharacter ℂ q,
            (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
              ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))))) := by
    have hexp : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ∑ χ : DirichletCharacter ℂ q, ∑ χ' : DirichletCharacter ℂ q,
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
                (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum, Finset.sum_mul_sum]
    rw [hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.sum_comm]
    have hfac : ∀ a : ZMod q,
        ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
        = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
      intro a
      rw [map_mul]
      ring
    rw [Finset.sum_eq_single χ]
    · have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac a)
      rw [hstep, sum_Gunit_orth χ χ, if_pos rfl]
    · intro χ' _ hne
      have hfac' : ∀ a : ZMod q,
          ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ' N z)) *
              ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        intro a
        rw [map_mul]
        ring
      have hstep : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
            ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
              (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)) * characterPrime519 χ' N z)
          = (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ' N z)) *
              ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
                ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ' cG)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => hfac' a)
      rw [hstep, sum_Gunit_orth χ χ', if_neg (fun h => hne h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ χ) h
  calc ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
        ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2
      = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          ((∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)).re := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact hreal _
    _ = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => IsUnit a),
          (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) *
            (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(a * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)).re := by
        exact hresumA _
    _ = (∑ χ : DirichletCharacter ℂ q,
          (characterPrime519 χ N z * (starRingEnd ℂ) (characterPrime519 χ N z)) *
            ((q.totient : ℂ) * ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)) * (starRingEnd ℂ) ((∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG)))))).re := by
        rw [hcomplex]
    _ = ∑ χ : DirichletCharacter ℂ q,
          (q.totient : ℝ) * (‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
        rw [← hresumC]
        exact Finset.sum_congr rfl (fun χ _ => hre χ)
    _ = (q.totient : ℝ) *
          ∑ χ : DirichletCharacter ℂ q, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
        rw [Finset.mul_sum]

end





open MeasureTheory Filter Finset

private theorem card_reduced_aux1622 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))

set_option maxHeartbeats 2000000 in
private theorem pointwise_assembly (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      (8 / (q.totient : ℝ)) *
        (‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime519 χ N z‖ ^ 2) +
        8 * (q.totient : ℝ) * Real.log q ^ 2 := by
  classical
  have hq0 : 0 < q := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr hq0
    exact_mod_cast this
  set S := Finset.univ.filter (fun c : ZMod q => IsUnit c) with hS
  set FF := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hFF
  set X : ℝ := ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
      (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 with hX
  -- membership characterisations
  have hSmem : ∀ c : ZMod q, c ∈ S ↔ IsUnit c := by
    intro c
    rw [hS]
    simp
  have hRmem : ∀ a : ℕ, a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ↔
      a < q ∧ Nat.Coprime a q := by
    intro a
    simp
  have hX0 : 0 ≤ X := by
    rw [hX]
    have h1 : (0 : ℝ) ≤ ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
      positivity
    have h2 : (0 : ℝ) ≤ ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 :=
      Finset.sum_nonneg (fun χ _ => by positivity)
    have h3 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith
  -- step 1: the reduced residues of `range q` are the units of `ZMod q`
  have hbij : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2)
      = ∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2 := by
    refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) (fun c : ZMod q => c.val)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
    · intro c hc
      have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
        exact (hSmem c).mp hc
      exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
    · intro a ha
      exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    · intro c _
      exact ZMod.natCast_zmod_val c
    · intro a ha
      rw [ZMod.val_natCast_of_lt ((hRmem a).mp ha).1]
  have hcardS : S.card = q.totient := by
    have hb : S.card = ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := by
      refine Finset.card_nbij' (fun c : ZMod q => c.val) (fun a : ℕ => (a : ZMod q))
        ?_ ?_ ?_ ?_
      · intro c hc
        have hunit : IsUnit (((c.val : ℕ)) : ZMod q) := by
          rw [ZMod.natCast_zmod_val]
          exact (hSmem c).mp hc
        exact (hRmem c.val).mpr ⟨ZMod.val_lt c, (ZMod.isUnit_iff_coprime c.val q).mp hunit⟩
      · intro a ha
        exact (hSmem _).mpr ((ZMod.isUnit_iff_coprime a q).mpr ((hRmem a).mp ha).2)
      · intro c _
        exact ZMod.natCast_zmod_val c
      · intro a ha
        exact ZMod.val_natCast_of_lt ((hRmem a).mp ha).1
    rw [hb, card_reduced_aux1622]
  -- the principal Gauss vector has norm at most one
  have hG1 : ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2 ≤ 1 := by
    have hG : (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))
        = ∑ c ∈ S, ZMod.stdAddChar (-(1 * c)) := by
      rw [hS]
      skip
      refine Finset.sum_congr rfl (fun c hc => ?_)
      have h1 : (1 : DirichletCharacter ℂ q) c = 1 := by
        obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hc).2
        simp
      rw [h1, map_one, mul_one]
    rw [hG]
    nlinarith [unit_gauss_principal_le q,
      norm_nonneg (∑ c ∈ S, ZMod.stdAddChar (-(1 * c)))]
  -- the character sum is bounded by the bracket of the statement
  have hGbound : (∑ χ : DirichletCharacter ℂ q,
        ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) ≤ X := by
    have hsplit_chi : (∑ χ : DirichletCharacter ℂ q,
          ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
            ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
          + ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2 := by
      have h := Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (p := fun χ : DirichletCharacter ℂ q => χ = 1)
        (f := fun χ => ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
      rw [← h]
      have hsingle : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ = 1) = {1} := by
        ext χ
        simp
      have hrest : (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => ¬ (χ = 1)) = FF := by
        rw [hFF]
      rw [hsingle, hrest, Finset.sum_singleton]
    rw [hsplit_chi, hX]
    have hb1 : ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 *
          ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) cG))‖ ^ 2
        ≤ ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hG1 (by positivity)
    have hb2 : (∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        ≤ ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * (q : ℝ) :=
      Finset.sum_le_sum (fun χ _ =>
        mul_le_mul_of_nonneg_left (Gunit_one_norm_sq_le χ) (by positivity))
    have hb2' : (∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 * (q : ℝ))
        = (q : ℝ) * ∑ χ ∈ FF, ‖characterPrime519 χ N z‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun χ _ => by ring)
    linarith [hb1, hb2, hb2'.le]
  -- the squared phi-normalised character sums
  have hfac : ∀ c : ZMod q,
      ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2
        = (1 / (q.totient : ℝ)) ^ 2 *
            ‖∑ χ : DirichletCharacter ℂ q, (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z‖ ^ 2 := by
    intro c
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_one, one_div, mul_pow]
  have hA : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
      ≤ (1 / (q.totient : ℝ)) * X := by
    have horth := sum_normSq_chi_combo N q hN z
    have hsum : (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
        = (1 / (q.totient : ℝ)) ^ 2 *
            ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
              ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun c _ => hfac c), ← Finset.mul_sum]
      rw [hS, horth]
    rw [hsum]
    have heq : (1 / (q.totient : ℝ)) ^ 2 *
          ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2)
        = (1 / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖characterPrime519 χ N z‖ ^ 2 * ‖(∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-((1 : ZMod q) * cG)) * (starRingEnd ℂ) (χ cG))‖ ^ 2) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hGbound (by positivity)
  -- the bound at each residue
  have hpoint : ∀ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2 ≤
      2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
    intro c _
    have hexp := prime_fourier_expansion N q hN z c
    set A : ℂ := (1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
        (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z) with hAdef
    set Tt : ℂ := ∑' p : Nat.Primes, (if IsUnit (((p : ℕ)) : ZMod q) then 0
        else (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * (((c.val : ℝ) / q + z)) * ((p : ℕ) : ℝ)) : ℝ) *
            Complex.I)) with hTdef
    have hT : ‖Tt‖ ≤ 2 * Real.log q := by
      rw [hTdef]
      exact corr_bound N q hq z c
    have hlog : 0 ≤ Real.log q :=
      Real.log_nonneg (by linarith [show (1 : ℝ) ≤ 2 by norm_num,
        show (2 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq])
    have h3 : ‖A + Tt‖ ^ 2 ≤ (‖A‖ + 2 * Real.log q) ^ 2 := by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      linarith [norm_add_le A Tt]
    have h4 : (‖A‖ + 2 * Real.log q) ^ 2 ≤
        2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      nlinarith [sq_nonneg (‖A‖ - 2 * Real.log q)]
    have hgoal : ‖A + Tt‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * (2 * Real.log q) ^ 2 := by
      linarith [h3, h4]
    rw [hexp, hAdef, hTdef]
    exact hgoal
  -- the correction terms
  have hcorr : (∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
          (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
        + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    have h1 := Finset.sum_le_sum hpoint
    have h2 : (∑ c ∈ S, (2 * ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2 + 2 * (2 * Real.log q) ^ 2))
        = 2 * (∑ c ∈ S, ‖(1 / (q.totient : ℂ)) * (∑ χ : DirichletCharacter ℂ q,
            (∑ cG ∈ (Finset.univ : Finset (ZMod q)).filter (fun cG => IsUnit cG), ZMod.stdAddChar (-(c * cG)) * (starRingEnd ℂ) (χ cG)) * characterPrime519 χ N z)‖ ^ 2)
          + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    linarith [h1, h2.le, h2.ge]
  -- the final comparison
  have hmain : (∑ c ∈ S, ‖primeFourier111_up111 N ((c.val : ℝ) / q + z)‖ ^ 2) ≤
      2 * ((1 / (q.totient : ℝ)) * X) + 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 := by
    linarith [hcorr, hA]
  have hlast : 2 * (S.card : ℝ) * (2 * Real.log q) ^ 2 =
      8 * (q.totient : ℝ) * Real.log q ^ 2 := by
    rw [hcardS]
    ring
  have hfirst : 2 * ((1 / (q.totient : ℝ)) * X) ≤ (8 / (q.totient : ℝ)) * X := by
    have h1 : 2 * ((1 / (q.totient : ℝ)) * X) = (2 / (q.totient : ℝ)) * X := by ring
    have h2 : (2 / (q.totient : ℝ)) * X ≤ (8 / (q.totient : ℝ)) * X := by
      apply mul_le_mul_of_nonneg_right _ hX0
      apply div_le_div_of_nonneg_right _ hφpos.le
      norm_num
    linarith
  rw [hbij]
  linarith [hmain, hlast.le, hlast.ge, hfirst]


/-- LEAF. The finite unit character step, pointwise in z. At any z the sum of the squares
of the prime system shifted to the reduced residues below q is at most a constant over the
totient of q times the principal square plus q times the sum of the nonprincipal squares,
plus a constant times the totient of q times the square of the logarithm of q. The
orthogonality of the unit group gives the coefficient one over the totient, the Gauss
squares are bounded by q, and the primes dividing q are absorbed in the logarithmic term.
No tau, no integration and no growth hypothesis occurs. -/
theorem rational_pointwise_characters519 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q], 1 ≤ N → 2 ≤ q → ∀ z : ℝ,
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      B / (q.totient : ℝ) *
        (‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
          (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖characterPrime519 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * Real.log q ^ 2 := by
  refine ⟨8, by norm_num, ?_⟩
  intro N q _ hN hq z
  exact pointwise_assembly N q hN hq z

/-- The doubled system mass, from the two geometry steps and the pointwise finite
character bound. The target statement is unchanged. -/
theorem doubled_system_characters1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1, ‖primeFourier111_up111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime519 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters519
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime519 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime519 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun z : ℝ => ‖characterPrime519 χ N z‖ ^ 2) :=
    (continuous_character_prime519 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111_up111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_cover_integral519 q τ hτp (fun α => ‖primeFourier111_up111 N α‖ ^ 2)
    ((continuous_prime_fourier111_up111 N hN).norm.pow 2) (fun α => sq_nonneg _)
    (rational_cover519 q τ hq hτ)
  have hmono : (∫ z in -r..r, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111_up111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime519 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh


/-- P0093 page 156 Lemma 2. The vertical Mellin line. -/
noncomputable def mellinLine519 (N : ℕ) (t : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- P0093 page 156 display after equation 4.1 with ds equal to i dt. -/
noncomputable def mellinU519 (N : ℕ) (M : ℝ → ℂ) (α : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
      (-(mellinLine519 N t)) * Complex.Gamma (mellinLine519 N t) * M t

/-- P0093 page 156 Lemma 2. The line bound has a nonzero instance:
the constant coefficient one works with the displayed fixed positive constant. -/
theorem line_coefficient_one519 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (fun _ : ℝ => (1 : ℂ)) ∧ ∀ t : ℝ,
      ‖(1 : ℂ)‖ ≤ (1 / Real.log 2 ^ 3) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  refine ⟨continuous_const, fun t => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg : (2 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hl : Real.log 2 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by norm_num) harg
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [norm_one, one_div_mul_eq_div]
  apply (le_div_iff₀ (pow_pos hl0 3)).mpr
  simpa only [one_mul] using pow_le_pow_left₀ hl0.le hl 3


/-! Upstream central kernel ports from Repair493KernelData, Gamma442,
SPLIT_central_kernel_mass442 and Repair493ContourData. -/

open MeasureTheory

/-- P0093 page 156 equation 4.1. The Mellin kernel before its coefficient M.
The factor one over two pi remains outside this kernel. -/
noncomputable def mellinKernel519 (N : ℕ) (α t : ℝ) : ℂ :=
  (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
    (-(mellinLine519 N t)) * Complex.Gamma (mellinLine519 N t)

/-- LEAF. P0093 page 156 equation 4.1. A line bound on M bounds the
Mellin integral by B0 over two pi times its absolute weighted kernel
mass. This is the norm integral inequality alone. -/
theorem mellin_kernel_domination519 (N : ℕ) (α B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : (Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3))
    (hI : Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖mellinU519 N M α‖ ≤ (1 / (2 * Real.pi)) * B0 *
      (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hb (t : ℝ) : ‖mellinKernel519 N α t * M t‖ ≤
      B0 * (‖mellinKernel519 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg (mellinKernel519 N α t))
    nlinarith
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0) (Filter.Eventually.of_forall hb)
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, mellinKernel519 N α t * M t)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ, B0 * (‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- LEAF. P0093 page 158 before equation 4.8. Square root N is at
most N over square root R when one is at most R at most N. -/
theorem sqrt_scale519 (N R : ℝ) (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) :
    Real.sqrt N ≤ N / Real.sqrt R := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    Real.sqrt N * Real.sqrt R ≤ Real.sqrt N * Real.sqrt N := by
      gcongr
    _ = N := Real.mul_self_sqrt hN.le


/-- P0093 page 157 Gamma asymptotic used before equation 4.4.
The existing PNTPort strip bound gives exponential decay in the
absolute imaginary part by conjugation. -/
theorem gamma_absolute_decay519 (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * ‖s + 1‖ *
      Real.exp (-(Real.pi * |s.im| / 2)) := by
  by_cases hs : 0 ≤ s.im
  · simpa only [abs_of_nonneg hs] using
      LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL hlo hhi
  · have hh := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL
      (s := star s) (by simpa using hlo) (by simpa using hhi)
    have hn : ‖star s + 1‖ = ‖s + 1‖ := by
      simpa using norm_star (s + 1)
    have hgamma : ‖Complex.Gamma (star s)‖ = ‖Complex.Gamma s‖ := by
      simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
    have him : (star s).im = -s.im := by simp
    rw [hgamma, hn, him] at hh
    simpa only [abs_of_neg (lt_of_not_ge hs)] using hh

/-- P0093 page 157 shifted Mellin line. For N at least three the
Gamma factor is bounded by square root of two pi times three plus
absolute t times exp of negative pi absolute t over two. -/
theorem gamma_mellin_line519 (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hNr)
  have hlog : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N ≤ 1 := (div_le_one hlog).mpr hl
  have hre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hg := gamma_absolute_decay519 (mellinLine519 N t)
    (by rw [hre]; exact le_add_of_nonneg_right (by positivity))
    (by rw [hre]; linarith)
  have hn : ‖mellinLine519 N t + 1‖ ≤ 3 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t + 1)
    have hr : (mellinLine519 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by simp [hre]
    have hi : (mellinLine519 N t + 1).im = t := by simp [him]
    rw [hr, hi, abs_of_pos (by positivity : 0 < 1 / 2 + 1 / Real.log N + 1)] at hh
    linarith
  rw [him] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (by positivity)) (Real.exp_pos _).le)


open MeasureTheory

/-- The gap in the principal argument: `pi / 2 - 1 / (16 * pi)` is strictly positive. -/
private lemma pi_gap519 : (0 : ℝ) < Real.pi / 2 - 1 / (16 * Real.pi) := by
  have h16 : (0 : ℝ) < 16 * Real.pi := by positivity
  have h : (1 : ℝ) < Real.pi / 2 * (16 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have h2 : 1 / (16 * Real.pi) < Real.pi / 2 := (div_lt_iff₀ h16).mpr h
  linarith

/-- The principal argument of the base `1 / N + 2 pi alpha i` of the Mellin power factor
stays `1 / (16 * pi)` away from `pi / 2` when `|alpha| ≤ 4 / N`: the modulus of the base is at
most `(1 / N) sqrt (1 + (8 pi) ^ 2)`, so its cosine is at least `1 / sqrt (1 + (8 pi) ^ 2)`,
which is at least `1 / (16 pi)`, which is at least `sin (1 / (16 pi))`. -/
private lemma arg_base_bound519 (N : ℕ) (α : ℝ) (hN : 2 ≤ N) (hα : |α| ≤ 4 / (N : ℝ)) :
    |Complex.arg ((((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I))| ≤
      Real.pi / 2 - 1 / (16 * Real.pi) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have him : |z.im| ≤ 8 * Real.pi / (N : ℝ) := by
    rw [hzim, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    calc 2 * Real.pi * |α| ≤ 2 * Real.pi * (4 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 8 * Real.pi / (N : ℝ) := by field_simp; ring
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm_le : ‖z‖ ≤ (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
    have hz2 : ‖z‖ ^ 2 ≤ (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) := by
      have hsqim : z.im ^ 2 ≤ (8 * Real.pi / (N : ℝ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg z.im) him 2
        rwa [sq_abs] at h
      have expand : (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) ^ 2 + (8 * Real.pi / (N : ℝ)) ^ 2 := by
        field_simp; ring
      rw [hsq, hzre, expand]
      linarith
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt ((1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2)) := Real.sqrt_le_sqrt hz2
      _ = (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hnorm_ge
  have hcos : Real.sin (1 / (16 * Real.pi)) ≤ z.re / ‖z‖ := by
    have h16 : (1 : ℝ) / (16 * Real.pi) ≤ 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h1 : 1 + 64 * Real.pi ^ 2 ≤ (16 * Real.pi) ^ 2 := by
        nlinarith [Real.pi_gt_three, Real.pi_pos]
      calc Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ Real.sqrt ((16 * Real.pi) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = 16 * Real.pi := Real.sqrt_sq (by positivity)
    have hsin : Real.sin (1 / (16 * Real.pi)) ≤ 1 / (16 * Real.pi) :=
      (Real.sin_lt (by positivity)).le
    have hstep : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ z.re / ‖z‖ := by
      rw [hzre]
      have heq : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) / ((1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2)) := by
        field_simp
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) hzpos hnorm_le
    exact hsin.trans (h16.trans hstep)
  have hθmem : Real.pi / 2 - 1 / (16 * Real.pi) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨(pi_gap519).le, by
      have h1 : (0 : ℝ) < 1 / (16 * Real.pi) := by positivity
      linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub (1 / (16 * Real.pi)), ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- LEAF. First step of the parent proof, the modulus of the power factor.
For N at least two and alpha at most four over N the base of the power has
real part one over N and imaginary part at most eight pi over N, so the
imaginary part of its logarithm is at most pi over two minus one over
sixteen pi; its modulus is at least one over N, and N to the power a half
plus one over log N is at most e times the square root of N. No Gamma
factor, no logarithm of N, no integral here. -/
theorem mellin_base_bound519 (N : ℕ) (α t : ℝ) (hN : 2 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - 1 / (16 * Real.pi) :=
    arg_base_bound519 N α hN hα
  have hsre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
    try ring
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    have hσ' : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := hσ
    nlinarith [h1, h2, hmul]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    have hlow : -(Real.pi / 2 - 1 / (16 * Real.pi)) ≤ Complex.arg z := (abs_le.mp harg).1
    have hhigh : Complex.arg z ≤ Real.pi / 2 - 1 / (16 * Real.pi) := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h : t * (Complex.arg z + (Real.pi / 2 - 1 / (16 * Real.pi))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht.le (by linarith)
      nlinarith [h]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hhigh ht
  have hkey : (Complex.log z * (-(mellinLine519 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  try ring

/-- LEAF. Second step of the parent proof, the split of the logarithm.
For N at least two the logarithm of N times the sum of absolute t and two
is the sum of two nonnegative logarithms, so its cube is at most eight
cubes of log N plus eight cubes of the logarithm of the sum. -/
theorem log_cube_split519 (N : ℕ) (t : ℝ) (hN : 2 ≤ N) :
    Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hu : (0 : ℝ) < |t| + 2 := by positivity
  have hu1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hsplit : Real.log ((N : ℝ) * (|t| + 2)) =
      Real.log N + Real.log (|t| + 2) := Real.log_mul hNr.ne' hu.ne'
  have hA : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hB : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg hu1
  rw [hsplit]
  set a := Real.log N with ha
  set b := Real.log (|t| + 2) with hb
  have hA' : 0 ≤ a := by rw [ha]; exact hA
  have hB' : 0 ≤ b := by rw [hb]; exact hB
  have h1 : 0 ≤ 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b := by
    rw [show 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b = (a - b) ^ 2 * (2 * a + b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 := by
    rw [show a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 = (a - b) ^ 2 * (a + 2 * b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ a ^ 3 := pow_nonneg hA' 3
  have h4 : 0 ≤ b ^ 3 := pow_nonneg hB' 3
  nlinarith [h1, h2, h3, h4]

/-- `exp (-b * |t|)` is integrable on the line for `b > 0`. -/
private lemma integrable_exp_neg_abs519 (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    show Real.exp (-b * t) = Real.exp (-b * |t|)
    rw [abs_of_pos ht]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro t ht
    show Real.exp (b * t) = Real.exp (-b * |t|)
    rw [abs_of_nonpos ht]
    ring_nf
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    integrableOn_union.mpr ⟨h1, h2⟩
  rw [Set.Ioi_union_Iic] at h3
  exact integrableOn_univ.mp h3

/-- A fifth power is dominated by a constant times `exp (e * |t|)` for every `e > 0`: this is
Taylor's inequality `v ^ 5 ≤ 5 ! exp v` at `v = e * (|t| + 4)`, together with
`e * (|t| + 4) = e * |t| + 4 * e`. -/
private lemma shift_pow_five_le_exp519 (e : ℝ) (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (|t| + 4) ^ 5 ≤ K * Real.exp (e * |t|) := by
  refine ⟨120 * (1 / e) ^ 5 * Real.exp (4 * e), by positivity, fun t => ?_⟩
  have hv : (0 : ℝ) ≤ e * (|t| + 4) := by positivity
  have h1 : (e * (|t| + 4)) ^ 5 ≤ 120 * Real.exp (e * (|t| + 4)) := by
    have h := Real.pow_div_factorial_le_exp (x := e * (|t| + 4)) hv 5
    norm_num at h
    calc (e * (|t| + 4)) ^ 5 = (e * (|t| + 4)) ^ 5 / 120 * 120 := by ring
      _ ≤ Real.exp (e * (|t| + 4)) * 120 := by
          exact mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 120 * Real.exp (e * (|t| + 4)) := by ring
  have h2 : (|t| + 4) ^ 5 = (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hExp : Real.exp (e * (|t| + 4)) = Real.exp (4 * e) * Real.exp (e * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  calc (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5
      ≤ (1 / e) ^ 5 * (120 * Real.exp (e * (|t| + 4))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 120 * (1 / e) ^ 5 * Real.exp (4 * e) * Real.exp (e * |t|) := by
        rw [hExp]; ring

/-- The majorant `(|t| + 4) ^ 5 exp (-|t| / (16 pi))` of the twisted Gamma mass is
integrable on the line. -/
private lemma integrable_majorant519 :
    Integrable (fun t : ℝ => (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  obtain ⟨K, hK, hKle⟩ := shift_pow_five_le_exp519 (1 / (16 * Real.pi) / 2) (by positivity)
  have hbase : Integrable (fun t : ℝ => Real.exp (-(1 / (16 * Real.pi) / 2) * |t|)) :=
    integrable_exp_neg_abs519 _ (by positivity)
  refine Integrable.mono' (hbase.const_mul K) (by fun_prop) ?_
  filter_upwards with t
  have h1 : (|t| + 4) ^ 5 ≤ K * Real.exp (1 / (16 * Real.pi) / 2 * |t|) := hKle t
  have h2 : (0 : ℝ) ≤ (|t| + 4) ^ 5 := by positivity
  have h3 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h3)]
  calc (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)
      ≤ (K * Real.exp (1 / (16 * Real.pi) / 2 * |t|)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = K * Real.exp (-(1 / (16 * Real.pi) / 2) * |t|) := by
        rw [mul_assoc, ← Real.exp_add,
          show 1 / (16 * Real.pi) / 2 * |t| + -(1 / (16 * Real.pi)) * |t| =
            -(1 / (16 * Real.pi) / 2) * |t| by ring]

/-- `mellinLine519 N` is continuous in `t`. -/
private lemma continuous_mellinLine519 (N : ℕ) :
    Continuous fun t : ℝ => mellinLine519 N t := by
  have h : (fun t : ℝ => mellinLine519 N t) =
      fun t : ℝ => (((1 / 2 + 1 / Real.log N : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    simp [mellinLine519]
  rw [h]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The Gamma factor on the shifted Mellin line decays exponentially in `|t|` for every
`N ≥ 2`. For a line with real part at most `3 / 2` this is `gamma_absolute_decay519`; otherwise
the real part is at most `5 / 2` and `Gamma s = (s - 1) Gamma (s - 1)` moves it into the strip. -/
private theorem gamma_line_uniform519 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hinv : 1 / Real.log N ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 hlogle
  have hlog2' : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hinvle : 1 / Real.log N ≤ 3 / 2 := by
    have h2 : 1 / Real.log 2 ≤ 3 / 2 := by
      rw [div_le_iff₀ hlog2]
      linarith
    linarith
  have hquad : ∀ x : ℝ, |x| + 4 ≤ (|x| + 4) ^ 2 := by
    intro x
    have h : (1 : ℝ) ≤ |x| + 4 := by linarith [abs_nonneg x]
    nlinarith [h, abs_nonneg x]
  have hsp : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by positivity
  by_cases hcase : (mellinLine519 N t).re ≤ 3 / 2
  · have hlo : (1 : ℝ) / 2 ≤ (mellinLine519 N t).re := by
      rw [hre]
      have hp : (0 : ℝ) < 1 / Real.log N := by positivity
      linarith
    have h := gamma_absolute_decay519 (mellinLine519 N t) hlo hcase
    rw [him] at h
    have hnorm : ‖mellinLine519 N t + 1‖ ≤ |t| + 4 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t + 1)
      have hr : (mellinLine519 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by
        rw [Complex.add_re, Complex.one_re, hre]
      have hi : (mellinLine519 N t + 1).im = t := by
        rw [Complex.add_im, Complex.one_im, him]; ring
      rw [hr, hi] at hb
      have hre2 : |1 / 2 + 1 / Real.log N + 1| ≤ 4 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hnorm2 : ‖mellinLine519 N t + 1‖ ≤ (|t| + 4) ^ 2 := le_trans hnorm (hquad t)
    have hstep : Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t + 1‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hnorm2 hsp
    exact h.trans hstep
  · push_neg at hcase
    have hσle : (mellinLine519 N t).re ≤ 5 / 2 := by rw [hre]; linarith
    have hre1 : (mellinLine519 N t - 1).re = 1 / 2 + 1 / Real.log N - 1 := by
      rw [Complex.sub_re, Complex.one_re, hre]
    have him1 : (mellinLine519 N t - 1).im = t := by
      rw [Complex.sub_im, Complex.one_im, him]; ring
    have hne : mellinLine519 N t - 1 ≠ 0 := by
      intro h
      have h' := congr_arg Complex.re h
      rw [hre1] at h'
      simp only [Complex.zero_re] at h'
      linarith [hlog]
    have hGam : Complex.Gamma (mellinLine519 N t) =
        (mellinLine519 N t - 1) * Complex.Gamma (mellinLine519 N t - 1) := by
      have h := Complex.Gamma_add_one (mellinLine519 N t - 1) hne
      rwa [sub_add_cancel] at h
    have hpos1 : (1 : ℝ) / 2 ≤ (mellinLine519 N t - 1).re := by rw [hre1]; linarith
    have hle1 : (mellinLine519 N t - 1).re ≤ 3 / 2 := by rw [hre1]; linarith
    have hbound := gamma_absolute_decay519 (mellinLine519 N t - 1) hpos1 hle1
    rw [him1] at hbound
    have hb2 : ‖Complex.Gamma (mellinLine519 N t - 1)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ * Real.exp (-(Real.pi * |t| / 2)) := by
      have h := hbound
      rwa [sub_add_cancel] at h
    have hn1 : ‖mellinLine519 N t - 1‖ ≤ |t| + 2 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t - 1)
      rw [hre1, him1] at hb
      have hre2 : |1 / 2 + 1 / Real.log N - 1| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith [abs_nonneg t]
    have hn0 : ‖mellinLine519 N t‖ ≤ |t| + 3 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine519 N t)
      rw [hre, him] at hb
      have hre2 : |1 / 2 + 1 / Real.log N| ≤ 3 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    rw [hGam, norm_mul]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hstep1 : ‖mellinLine519 N t - 1‖ *
        ‖Complex.Gamma (mellinLine519 N t - 1)‖ ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hn1 hb2 (norm_nonneg _) (by positivity)
    refine hstep1.trans ?_
    have hinner : Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hn0 hsp
    have hstep2 : (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine519 N t‖ *
        Real.exp (-(Real.pi * |t| / 2))) ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    refine hstep2.trans ?_
    have hq2 : (|t| + 2) * (|t| + 3) ≤ (|t| + 4) ^ 2 := by nlinarith [abs_nonneg t]
    calc (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)))
        = ((|t| + 2) * (|t| + 3)) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ ((|t| + 4) ^ 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) :=
          mul_le_mul_of_nonneg_right hq2 (by positivity)
      _ = Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by ring

/-- Pointwise domination of the twisted Gamma mass with a logarithm factor. -/
private lemma gamma_twist_pointwise519 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  have hg := gamma_line_uniform519 N hN t
  have hfac : (0 : ℝ) ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) :=
    (Real.exp_pos _).le
  have h1 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) :=
    mul_le_mul_of_nonneg_left hg hfac
  have hee : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      Real.exp (-(Real.pi * |t| / 2)) = Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmid : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) =
      Real.sqrt (2 * Real.pi) * ((|t| + 4) ^ 2 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          Real.exp (-(Real.pi * |t| / 2)))) := by ring
  have h2 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) *
        ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    rw [hmid, hee] at h1
    exact h1
  have hlogp0 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
    have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
    positivity
  have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by linarith
  have hlog3 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by
    have h1' : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2' : Real.log (|t| + 2) ≤ |t| + 2 := Real.log_le_self (by linarith)
    have h3' : Real.log (|t| + 2) ≤ |t| + 4 := by linarith
    have h4' : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1'
    have h5' : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ h4' h3' 3
    have h6' : (1 : ℝ) ≤ (|t| + 4) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg t])
    linarith
  have h4 : (0 : ℝ) ≤ (|t| + 4) ^ 2 := by positivity
  have h5 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  have h3 : (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤ 2 * (|t| + 4) ^ 5 := by
    have := mul_le_mul_of_nonneg_left hlog3 h4
    calc (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤
        (|t| + 4) ^ 2 * (2 * (|t| + 4) ^ 3) := this
      _ = 2 * (|t| + 4) ^ 5 := by ring
  calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
      = (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) * (1 + Real.log (|t| + 2) ^ 3) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) *
          (1 + Real.log (|t| + 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
    _ = Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (|t| + 4) ^ 5) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ h5
        apply mul_le_mul_of_nonneg_left h3
        exact Real.sqrt_nonneg _
    _ = Real.sqrt (2 * Real.pi) * 2 *
          ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by ring

/-- `Gamma` composed with the shifted Mellin line is continuous: the line has positive real
part, so it stays away from the poles of `Gamma`. -/
private lemma continuous_gamma_mellin519 (N : ℕ) (hN : 2 ≤ N) :
    Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hre : ∀ t : ℝ, (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hpos : (0 : ℝ) < 1 / 2 + 1 / Real.log N := by positivity
  have hne : ∀ t : ℝ, ∀ m : ℕ, mellinLine519 N t ≠ -(m : ℂ) := by
    intro t m h
    have h1 := congr_arg Complex.re h
    rw [hre t] at h1
    have h3 : (-(m : ℂ)).re = -(m : ℝ) := by push_cast; simp
    rw [h3] at h1
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hpos]
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact ((Complex.differentiableAt_Gamma _ (hne t)).continuousAt).comp
    (continuous_mellinLine519 N).continuousAt

/-- LEAF. Third step of the parent proof, the twisted Gamma mass. The
Gamma factor on the line, weighted by the exponential gap of the power
factor and by the cube of the logarithm of the sum of absolute t and two,
is integrable for every N at least two, and both of its integrals are at
most one constant independent of N and of alpha. This is the analytic core
of the parent proof and the only place where the decay of Gamma is used. -/
theorem gamma_twist_mass519 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) ∧
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖) ≤ G ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ *
          Real.log (|t| + 2) ^ 3)) ≤ G := by
  have hM : Integrable (fun t : ℝ =>
      (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := integrable_majorant519
  have h2pi : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * 2 := by positivity
  have hMc : Integrable (fun t : ℝ => Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) := hM.const_mul _
  have hInt_nonneg : (0 : ℝ) ≤ ∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) :=
    integral_nonneg (fun t => by positivity)
  refine ⟨(∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
    ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) + 1, by linarith, ?_⟩
  intro N hN
  have hpt := gamma_twist_pointwise519 N hN
  have hApt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine519 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      have h3 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by positivity
      linarith
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖ * 1 := by ring
        _ ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
            apply mul_le_mul_of_nonneg_left hlogp1
            positivity
    exact h3.trans h
  have hBpt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      rw [show Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)) by ring]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith
    exact h3.trans h
  have hGamma_cont : Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) :=
    continuous_gamma_mellin519 N hN
  have hAcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul hGamma_cont.norm
  have hBcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3) :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul
      (hGamma_cont.norm.mul (((continuous_abs.add continuous_const).log
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < |t| + 2))).pow 3))
  have hAi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖) := by
    refine Integrable.mono' hMc hAcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact hApt t
  have hBi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    refine Integrable.mono' hMc hBcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) hlogp))]
    exact hBpt t
  exact ⟨hAi, hBi, (integral_mono hAi hMc hApt).trans (by linarith),
    (integral_mono hBi hMc hBpt).trans (by linarith)⟩


/-- LEAF. Fourth step of the parent proof, the integrability half of the
parent conclusion. The modulus of the kernel times the cube of the
logarithm of N times the sum of absolute t and two is integrable, for N at
least thirty two and alpha at most four over N. This is the first
conjunct of the parent statement on its own, without any estimate of the
integral. -/
theorem kernel_mass_integrable519 (N : ℕ) (α : ℝ) (hN : 32 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNr2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass519
  obtain ⟨hAi, hBi, -, -⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hcont : Continuous fun t : ℝ => ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have hg : Continuous fun t : ℝ => Complex.Gamma (mellinLine519 N t) :=
      continuous_gamma_mellin519 N hN2
    have he : Continuous fun t : ℝ =>
        Complex.exp (Complex.log z * (-(mellinLine519 N t))) :=
      Complex.continuous_exp.comp (continuous_const.mul (continuous_mellinLine519 N).neg)
    have h1 : Continuous fun t : ℝ => mellinKernel519 N α t := by
      have hfun : (fun t : ℝ => mellinKernel519 N α t) =
          fun t => Complex.exp (Complex.log z * (-(mellinLine519 N t))) *
            Complex.Gamma (mellinLine519 N t) := by
        funext t
        unfold mellinKernel519
        rw [Complex.cpow_def_of_ne_zero hz]
      rw [hfun]
      exact he.mul hg
    have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
      continuous_const.mul (continuous_abs.add continuous_const)
    have h2 : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
      harg.log (fun t => ne_of_gt (by positivity))
    exact h1.norm.mul (h2.pow 3)
  refine Integrable.mono' hdomint hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hbase := mellin_base_bound519 N α t hN2 hα
  have hlog := log_cube_split519 N t hN2
  have hk : ‖mellinKernel519 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ := by
    unfold mellinKernel519
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
  have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t, hNr2])
    positivity
  have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine519 N t)‖ := by positivity
  have h1 := mul_le_mul hk hlog hpos hf
  have hEq : (Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) *
      (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    ring
  rw [hEq] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos)]
  exact h1
/-- LEAF. Fifth step of the parent proof, the bookkeeping of the constant.
For N at least thirty two and a positive constant G, eight e times the
square root of N times the cube of log N times G plus G is at most the
cube of log N times the square root of N times the constant eight e G
times one plus the inverse cube of log two. The last factor absorbs the
additive G because the cube of log N is at least the cube of log two. -/
theorem mass_constant519 (N : ℕ) (G : ℝ) (hN : 32 ≤ N) (hG : 0 < G) :
    8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlr : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlogN : 0 < Real.log N := lt_of_lt_of_le hlog2 hlr
  have hl3 : Real.log 2 ^ 3 ≤ Real.log N ^ 3 := pow_le_pow_left₀ hlog2.le hlr 3
  have h19 : (1 : ℝ) ≤ Real.log N ^ 3 / Real.log 2 ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    simpa using hl3
  have hGeq : G ≤ G * (Real.log N ^ 3 / Real.log 2 ^ 3) := by
    simpa using mul_le_mul_of_nonneg_left h19 hG.le
  have hc : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N := by positivity
  have hkey : Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) := by
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith [hGeq]
  have hEq : Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) =
      Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
    field_simp
    try ring
  calc 8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)
      = 8 * (Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)) := by ring
    _ ≤ 8 * (Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3))) := by
        linarith [hkey]
    _ = 8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
        rw [hEq]; try ring

/-- The parent statement central_kernel_mass442, reassembled from the five
leaves above. No use of the parent theorem, no sorry. -/
theorem central_kernel_mass519 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
        Integrable (fun t : ℝ => ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
        (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
            C * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass519
  refine ⟨8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3), ?_, 31, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < 1 + 1 / Real.log 2 ^ 3 := by positivity
    positivity
  intro N hN α hα
  have hN32 : 32 ≤ N := hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hAi, hBi, hA, hB⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hpoint : ∀ t : ℝ, ‖mellinKernel519 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    intro t
    have hbase := mellin_base_bound519 N α t hN2 hα
    have hlog := log_cube_split519 N t hN2
    have hk : ‖mellinKernel519 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ := by
      unfold mellinKernel519
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t, hNr])
      positivity
    have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖ := by positivity
    have h1 := mul_le_mul hk hlog hpos hf
    have hEq : (Real.exp 1 * Real.sqrt N *
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine519 N t)‖) *
        (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
        8 * Real.exp 1 * Real.sqrt N *
          (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖) +
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
      ring
    rw [hEq] at h1
    exact h1
  have hval : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (∫ t : ℝ,
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine519 N t)‖) +
          ∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine519 N t)‖ *
              Real.log (|t| + 2) ^ 3)) := by
    rw [integral_const_mul, integral_add (hAi.const_mul _) hBi, integral_const_mul]
  have hub : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ * Real.log (|t| + 2) ^ 3))) ≤
      8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) := by
    rw [hval]
    have hc : (0 : ℝ) ≤ 8 * Real.exp 1 * Real.sqrt N := by positivity
    have hl : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN.le 3
    have h1 : Real.log N ^ 3 * (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine519 N t)‖) ≤ Real.log N ^ 3 * G :=
      mul_le_mul_of_nonneg_left hA hl
    have h2 : (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine519 N t)‖ *
            Real.log (|t| + 2) ^ 3)) ≤ G := hB
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  exact ⟨kernel_mass_integrable519 N α hN32 hα,
    (integral_mono (kernel_mass_integrable519 N α hN32 hα) hdomint hpoint).trans
      (hub.trans (mass_constant519 N G hN32 hGpos))⟩

/-- P0093 page 157 equation 4.4. The signed kernel with a continuous coefficient is jointly continuous in alpha and the finite line parameter. -/
theorem continuous_mellin_integrand519 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (fun p : ℝ × ℝ => mellinKernel519 N p.1 p.2 * M p.2) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hNr
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine519 N t) := by
    dsimp [mellinLine519]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine519 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hinv : 0 < 1 / Real.log N := by positivity
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact (((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)).mul (hM.comp continuous_snd)

/-- P0093 page 156 equation 4.1. Parameter integration of the continuous signed kernel makes the full Mellin value strongly measurable. -/
theorem stronglyMeasurable_mellinU519 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    StronglyMeasurable (mellinU519 N M) := by
  exact stronglyMeasurable_const.mul
    (continuous_mellin_integrand519 N hN M hM).stronglyMeasurable.integral_prod_right


/-- P0093 page 158 final sentence after equation 4.8. Reflecting alpha
conjugates the Mellin integral and reflects and conjugates its coefficient.
Positive N keeps the complex power base away from its branch cut.
No GRH or line bound is assumed. -/
theorem mellin_reflection519 (N : ℕ) (hN : 1 ≤ N) (M : ℝ → ℂ) (α : ℝ) :
    mellinU519 N (fun t => (starRingEnd ℂ) (M (-t))) α = (starRingEnd ℂ) (mellinU519 N M (-α)) := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * I
  have hx : x.arg ≠ Real.pi := by
    intro h
    have hh := (Complex.arg_eq_pi_iff.mp h).1
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hxp : 0 < x.re := by dsimp [x]; simp; positivity
    linarith
  have hline (t : ℝ) : mellinLine519 N (-t) = (starRingEnd ℂ) (mellinLine519 N t) := by
    simp only [mellinLine519, map_add, map_mul, Complex.conj_ofReal,
      Complex.ofReal_neg, Complex.conj_I]
    ring
  have hbase : (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * -α : ℝ) : ℂ) * I) = (starRingEnd ℂ) x := by
    dsimp [x]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold mellinU519
  rw [map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  conv_rhs => rw [← integral_neg_eq_self _ volume]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hbase, hline, map_mul, map_mul, ← Gamma_conj, conj_conj]
  have hp := Complex.conj_cpow x (-((starRingEnd ℂ) (mellinLine519 N t))) hx
  simp only [map_neg, conj_conj] at hp
  rw [hp, conj_conj]

/-- P0093 page 158 final sentence after equation 4.8. Reflecting and
conjugating a coefficient preserves continuity and the cubic logarithmic
line bound with the same constant. -/
theorem reflected_line_bound519 (N : ℕ) (B0 : ℝ) (M : ℝ → ℂ) (hM : Continuous M)
    (hb : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    Continuous (fun t => (starRingEnd ℂ) (M (-t))) ∧ ∀ t : ℝ,
      ‖(starRingEnd ℂ) (M (-t))‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  refine ⟨continuous_star.comp (hM.comp continuous_neg), fun t => ?_⟩
  simpa only [Complex.norm_conj, abs_neg] using hb (-t)

/-- P0093 page 158 final sentence after equation 4.8. The negative
half square integral equals the positive half square integral for the
reflected conjugate coefficient. Interval orientation is retained. -/
theorem mellin_negative_square519 (N : ℕ) (hN : 1 ≤ N) (M : ℝ → ℂ) (r : ℝ) :
    (∫ α in -r..0, ‖mellinU519 N M α‖ ^ 2) =
      ∫ α in 0..r, ‖mellinU519 N (fun t => (starRingEnd ℂ) (M (-t))) α‖ ^ 2 := by
  simp_rw [mellin_reflection519 N hN M, Complex.norm_conj]
  simpa only [neg_zero] using
    (intervalIntegral.integral_comp_neg (f := fun α => ‖mellinU519 N M α‖ ^ 2)
      (a := 0) (b := r)).symm

/-- P0093 page 158 before equation 4.8. The clean central absolute
kernel bound controls every coefficient with the cubic logarithmic line bound. -/
theorem central_mellin_bound519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
        ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU519 N M α‖ ≤ K * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass519
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, N0, ?_⟩
  intro N hN M hM α hα
  obtain ⟨hi, hm⟩ := hc N hN α hα
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel519 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination519 N α B0 hB0.le M hM hi
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (C * Real.sqrt N * Real.log N ^ 3) := by gcongr
    _ = _ := by ring

/-- P0093 page 158 equation 4.8. The positive central interval has
integrable square mass at most a constant times log to the sixth N.
This follows from the clean square root N pointwise bound and interval length. -/
theorem central_square_mass519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
        ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
        IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc 0 (4 / (N : ℝ))) ∧
        (∫ α in 0..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2) ≤ C * Real.log N ^ 6 := by
  obtain ⟨K, hK, Nk, hk⟩ := central_mellin_bound519 B0 hB0
  refine ⟨4 * K ^ 2, by positivity, max 3 Nk, ?_⟩
  intro N hN M hM
  have hN3 : 3 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : ∀ α ∈ Set.Icc (0 : ℝ) (4 / (N : ℝ)),
      ‖mellinU519 N M α‖ ^ 2 ≤ K ^ 2 * N * Real.log N ^ 6 := by
    intro α hα
    have hαabs : |α| ≤ 4 / (N : ℝ) := by rw [abs_of_nonneg hα.1]; exact hα.2
    have hh := hk N (by omega) M hM α hαabs
    calc _ ≤ (K * Real.sqrt N * Real.log N ^ 3) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hNp.le]; ring
  have hiC : IntegrableOn (fun _ : ℝ => K ^ 2 * N * Real.log N ^ 6)
      (Set.Icc 0 (4 / (N : ℝ))) := continuous_const.integrableOn_Icc
  have hi : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc 0 (4 / (N : ℝ))) := by
    refine hiC.mono' ((stronglyMeasurable_mellinU519 N hN3 M hM.1).norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖mellinU519 N M α‖)]
    exact hs α hα
  refine ⟨hi, ?_⟩
  have hiI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))).mpr hi
  calc
    _ ≤ ∫ α in (0 : ℝ)..(4 / (N : ℝ)), K ^ 2 * N * Real.log N ^ 6 :=
      intervalIntegral.integral_mono_on (by positivity) hiI intervalIntegrable_const hs
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp [hNp.ne'] <;> ring

/-- LEAF. P0093 page 158 equation 4.7, from the signed double frequency
calculation of pages 157 and 158 equations 4.4 through 4.6. Only the positive
outer interval remains. The Mellin integral stays signed before squaring.
There is no central interval, negative half, prime, character or GRH here. -/
theorem lemma2_outer_square519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  sorry

/-- P0093 page 158 equations 4.7 and 4.8. The full positive half interval
is assembled from the clean central part and the signed outer estimate.
CONDITIONAL ON lemma2_outer_square519. -/
theorem lemma2_positive_square519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc 0 (1 / R)) ∧
          (∫ α in 0..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨Cc, hCc, Nc, hc⟩ := central_square_mass519 B0 hB0
  obtain ⟨Co, hCo, No, ho⟩ := lemma2_outer_square519 B0 hB0
  have hscale : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 7)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp hscale
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp hlogs
  refine ⟨Cc + Co, by positivity, max 3 (max Nc (max No (max Ns Nl))), ?_⟩
  intro N hN R hR hRN M hM
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRp : 0 < R := by linarith
  have hlog : 1 ≤ Real.log N := hl N (by omega)
  have hlog0 : 0 ≤ Real.log N := by linarith
  have h4R : 4 * R ≤ N := by
    calc _ ≤ 4 * (N : ℝ) ^ (2 / 7 : ℝ) := mul_le_mul_of_nonneg_left hRN (by norm_num)
      _ ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right (hs N (by omega)) (by positivity)
      _ = N := by rw [← Real.rpow_add hNp]; norm_num
  have hδr : 4 / (N : ℝ) ≤ 1 / R :=
    (div_le_div_iff₀ hNp hRp).mpr (by simpa only [one_mul] using h4R)
  obtain ⟨hiC, hbC⟩ := hc N (by omega) M hM
  obtain ⟨hiO, hbO⟩ := ho N (by omega) R hR hRN M hM
  have hiCI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))).mpr hiC
  have hiOI := (intervalIntegrable_iff_integrableOn_Icc_of_le hδr).mpr hiO
  have hiP := hiCI.trans hiOI
  have hRleN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hRN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hNR : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRleN)
  have hlogscale : Real.log N ^ 13 ≤ (N : ℝ) / R * Real.log N ^ 13 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hNR (pow_nonneg hlog0 13)
  have hcu : (∫ α in 0..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2) ≤
      Cc * ((N : ℝ) / R * Real.log N ^ 13) :=
    hbC.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (by omega : 6 ≤ 13)) hCc.le).trans
        (mul_le_mul_of_nonneg_left hlogscale hCc.le))
  have hou : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
      Co * ((N : ℝ) / R * Real.log N ^ 13) := by
    apply hbO.trans
    gcongr
    norm_num
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 1 / R)).mp hiP, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiCI hiOI]
  calc _ ≤ Cc * ((N : ℝ) / R * Real.log N ^ 13) +
      Co * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hcu hou
    _ = _ := by ring

section PortB1122

open MeasureTheory Set Filter Complex Metric Topology Finset

set_option maxHeartbeats 1600000


/-! ### Gamma kernel domination (from Mellin473) -/

/-- P0093 page 157 Gamma kernel domination. Every positive exponential rate
makes the cubic absolute value weight integrable on the whole real line. -/
theorem exp_decay_cubic_integrable519x (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
  have hk (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (b := δ) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Ioi 0) := by
    apply (((hk 3).add ((hk 2).const_mul 3)).add ((hk 1).const_mul 3)).add (hk 0) |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  have hc : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) (Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3)
      (Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

/-! ### Step: the GRH strip bound on log L (Burst1122LogBound) -/


/-- P0093 page 155. The Euler logarithm series for one prime: the sum over k of
chi of p to the k + 1 times p to the minus k + 1 times s over k + 1 is minus the log of
one minus chi of p times p to the minus s, when re s exceeds 0. -/
theorem euler_log_term_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 0 < s.re) (p : Nat.Primes) :
    ∑' k : ℕ, (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) =
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  apply HasSum.tsum_eq
  apply Complex.hasSum_taylorSeries_neg_log'
  have hp : 0 < (p : ℕ) := p.2.pos
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  have hχ : ‖χ (p : ℕ)‖ ≤ 1 := χ.norm_le_one _
  have hlt : ((p : ℕ) : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hχ (by positivity)
    _ < 1 := by rw [one_mul]; exact hlt

/-- P0093 page 155 and page 159 before equation 5.1. A function G holomorphic on
re s greater than 1/2 that equals the prime power series on re s greater than 1 is a
logarithm of L there: exp of G is the Euler product on re s greater than 1, and the
identity theorem on the connected half plane extends the equality. -/
theorem exp_G_eq_LFunction_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : 1 / 2 < w.re) :
    Complex.exp (G w) = DirichletCharacter.LFunction χ w := by
  have hHo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : ∀ s : ℂ, 1 < s.re → Complex.exp (G s) = DirichletCharacter.LFunction χ s := by
    intro s hs
    rw [hGs s hs, tsum_congr fun p => euler_log_term_b1122x χ s (by linarith) p,
      DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs]
  have hA : AnalyticOnNhd ℂ (fun s => Complex.exp (G s)) {s : ℂ | 1 / 2 < s.re} :=
    hGd.cexp.analyticOnNhd hHo
  have hB : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 / 2 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hHo
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have hev : (fun s => Complex.exp (G s)) =ᶠ[𝓝 (2 : ℂ)] DirichletCharacter.LFunction χ := by
    filter_upwards [hVo.mem_nhds h2] with s hs
    exact h1 s hs
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt (r := 1 / 2)).isPreconnected (by norm_num) hev hw

/-- Titchmarsh 14.2 step one, with P0093 page 159. The real part of the logarithm G is
log of the norm of L, and the bound of L by q times the norm of w over re w gives
re G w at most log of 2 q times 4 plus the absolute imaginary part, for re w in
the range 1/2 to 4. -/
theorem re_G_le_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : 1 / 2 < w.re) (hw4 : w.re ≤ 4) :
    (G w).re ≤ Real.log (2 * q * (4 + |w.im|)) := by
  have he := exp_G_eq_LFunction_b1122x χ hχ G hGd hGs w hw
  have hn : Real.exp (G w).re = ‖DirichletCharacter.LFunction χ w‖ := by
    rw [← he, Complex.norm_exp]
  have hL := LeanLab.PNTPort.DirichletZF.norm_LFunction_le hχ (s := w) (by linarith)
  have hwn : ‖w‖ ≤ 4 + |w.im| := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos (by linarith : 0 < w.re)] at this
    linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hdiv : (q : ℝ) * ‖w‖ / w.re ≤ 2 * q * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ (q : ℝ) * ‖w‖ := by positivity
    nlinarith
  have hfin : Real.exp (G w).re ≤ 2 * q * (4 + |w.im|) := by
    rw [hn]
    calc _ ≤ _ := hL
      _ ≤ 2 * q * ‖w‖ := hdiv
      _ ≤ 2 * q * (4 + |w.im|) := by gcongr
  calc (G w).re = Real.log (Real.exp (G w).re) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) hfin

/-- P0093 page 155. The constant majorant K, the sum over primes of 3/2 times p to
the minus 2, is summable. -/
theorem summable_K_b1122x :
    Summable (fun p : Nat.Primes => (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  apply Summable.mul_left
  have h := (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  exact h.comp_injective Nat.Primes.coe_nat_injective

/-- P0093 page 155, the center of the Borel Caratheodory disc. On re w equal to 2 the
prime power series G w has norm at most K, the sum over primes of 3/2 times p to the
minus 2, since each Euler logarithm is at most 3/2 times p to the minus 2. -/
theorem norm_G_center_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (w : ℂ) (hw : w.re = 2) :
    ‖G w‖ ≤ ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  rw [hGs w (by rw [hw]; norm_num),
    tsum_congr fun p => euler_log_term_b1122x χ w (by rw [hw]; norm_num) p]
  apply tsum_of_norm_bounded summable_K_b1122x.hasSum
  intro p
  have hv : ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-w)‖ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hw]
    calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ = _ := one_mul _
  have hhalf : ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    calc ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
  have hw2 : ‖-(χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-w))‖ ≤ 1 / 2 := by
    rw [norm_neg]; exact hv.trans hhalf
  have hl := Complex.norm_log_one_add_half_le_self hw2
  rw [← sub_eq_add_neg, norm_neg] at hl
  rw [norm_neg]
  exact hl.trans (mul_le_mul_of_nonneg_left hv (by norm_num))

/-- Titchmarsh 14.2, Borel Caratheodory step, used for P0093 page 159 before 5.1.
With centre w0 equal to 2 + i Im s and radius 3/2 - 1/(2 l), where l at least 1 and
1/2 + 1/l at most re s at most 2, the norm of G s is at most K plus 8 l times
log of 2 q times the absolute imaginary part plus 6, plus K plus 1. -/
theorem G_strip_bound_b1122x {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (G : ℂ → ℂ) (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1))
    (l : ℝ) (hl : 1 ≤ l) (s : ℂ) (hs1 : 1 / 2 + 1 / l ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖G s‖ ≤ (∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) + 8 * l *
      (Real.log (2 * q * (|s.im| + 6)) +
        (∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) + 1) := by
  set K : ℝ := ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun p => by positivity
  set t : ℝ := s.im with ht
  set w0 : ℂ := ⟨2, t⟩ with hw0
  have hw0re : w0.re = 2 := rfl
  have hw0im : w0.im = t := rfl
  have hc := norm_G_center_b1122x χ G hGs w0 hw0re
  set R : ℝ := 3 / 2 - 1 / (2 * l) with hR
  have hl0 : 0 < l := by linarith
  have hinv : 1 / l ≤ 1 := by rw [div_le_one hl0]; exact hl
  have hinv0 : 0 < 1 / l := by positivity
  have h2l : 1 / (2 * l) = (1 / l) / 2 := by field_simp
  have hRpos : 0 < R := by rw [hR, h2l]; linarith
  have hR32 : R ≤ 3 / 2 := by rw [hR, h2l]; linarith
  set M : ℝ := Real.log (2 * q * (|t| + 6)) + K + 1 with hM
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log (2 * q * (|t| + 6)) := by
    apply Real.log_nonneg
    have : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hMpos : 0 < M := by rw [hM]; linarith
  set f : ℂ → ℂ := fun u => G (w0 + u) - G w0 with hf
  have hball : ∀ u ∈ ball (0 : ℂ) R, 1 / 2 + 1 / (2 * l) < (w0 + u).re ∧
      (w0 + u).re ≤ 4 ∧ |(w0 + u).im| ≤ |t| + 2 := by
    intro u hu
    have hu' : ‖u‖ < R := mem_ball_zero_iff.mp hu
    have hre := Complex.abs_re_le_norm u
    have him := Complex.abs_im_le_norm u
    rw [abs_le] at hre
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.add_re, hw0re]; rw [hR] at hu'; linarith [hre.1]
    · simp only [Complex.add_re, hw0re]; linarith [hre.2]
    · simp only [Complex.add_im, hw0im]
      calc |t + u.im| ≤ |t| + |u.im| := abs_add_le _ _
        _ ≤ |t| + 2 := by linarith
  have hmaps : Set.MapsTo (fun u => w0 + u) (ball (0 : ℂ) R) {s : ℂ | 1 / 2 < s.re} := by
    intro u hu
    have := (hball u hu).1
    have : 0 < 1 / (2 * l) := by positivity
    simp only [Set.mem_ofPred_eq]; linarith
  have hfd : DifferentiableOn ℂ f (ball (0 : ℂ) R) :=
    (hGd.comp (differentiableOn_const _ |>.add differentiableOn_id) hmaps).sub_const _
  have hf1 : Set.MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ M} := by
    intro u hu
    obtain ⟨hre1, hre4, him⟩ := hball u hu
    have hpos : 1 / 2 < (w0 + u).re := by
      have : 0 < 1 / (2 * l) := by positivity
      linarith
    have hG1 := re_G_le_b1122x χ hχ G hGd hGs (w0 + u) hpos hre4
    have hmono : Real.log (2 * q * (4 + |(w0 + u).im|)) ≤ Real.log (2 * q * (|t| + 6)) := by
      apply Real.log_le_log
      · have : 0 ≤ |(w0 + u).im| := abs_nonneg _
        nlinarith
      · have : (0 : ℝ) ≤ 2 * q := by positivity
        nlinarith
    have hc' : -(G w0).re ≤ K := by
      have := Complex.abs_re_le_norm (G w0)
      rw [abs_le] at this
      linarith
    simp only [Set.mem_ofPred_eq, hf, Complex.sub_re]
    rw [hM]; linarith
  set z : ℂ := s - w0 with hz
  have hzeq : z = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hz, hw0re]
    · simp [hz, hw0im, ht]
  have hzn : ‖z‖ = 2 - s.re := by
    rw [hzeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have hgap : 1 / (2 * l) ≤ R - ‖z‖ := by
    rw [hzn, hR, h2l]; linarith
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    have : 0 < 1 / (2 * l) := by positivity
    linarith
  have hf0 : f 0 = 0 := by simp [hf]
  have hBC := Complex.borelCaratheodory_zero hMpos hfd hf1 hRpos hzR hf0
  have hgap' : 1 / 2 ≤ l * (R - ‖z‖) := by
    have h := mul_le_mul_of_nonneg_left hgap hl0.le
    have : l * (1 / (2 * l)) = 1 / 2 := by field_simp
    linarith
  have hgpos : 0 < R - ‖z‖ := lt_of_lt_of_le (by positivity) hgap
  have hzle : ‖z‖ ≤ 2 := by rw [hzn]; linarith
  have hfz : ‖f z‖ ≤ 8 * l * M := by
    refine hBC.trans ?_
    rw [div_le_iff₀ hgpos]
    have h1 : 4 * M ≤ 8 * M * (l * (R - ‖z‖)) := by nlinarith
    have h2 : 2 * M * ‖z‖ ≤ 4 * M := by nlinarith [norm_nonneg z]
    nlinarith
  have hGs' : G s = f z + G w0 := by
    simp only [hf, hz]; ring_nf
  rw [hGs']
  calc ‖f z + G w0‖ ≤ ‖f z‖ + ‖G w0‖ := norm_add_le _ _
    _ ≤ 8 * l * M + K := add_le_add hfz hc
    _ = K + 8 * l * M := by ring

/-- P0093 page 159 before equation 5.1, the GRH bound for ln L used by Linnik, proved
here by the Titchmarsh 14.2 Borel Caratheodory method without GRH: for N above 2, q at
most N to the 1/7, chi nonprincipal and G the holomorphic logarithm of L fixed by the
prime power series on re s greater than 1, the norm of G on 1/2 + 1/ln N at most re s
at most 2 is at most B0 times the cube of ln of N times the absolute imaginary part
plus 2. The GRH hypothesis is not used. -/
theorem grh_strip_log_bound_proof_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ G : ℂ → ℂ,
          DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} →
          (∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
            (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) →
          ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
            ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 := by
  set K : ℝ := ∑' p : Nat.Primes, (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-2 : ℝ) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun p => by positivity
  refine ⟨9 * K + 57, by positivity, 2, ?_⟩
  intro N hN q _ hq1 hqN χ hχ G hGd hGs s hs1 hs2
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hB := G_strip_bound_b1122x χ hχ G hGd hGs (Real.log N) hl1 s hs1 hs2
  rw [← hK] at hB
  set t : ℝ := s.im with ht
  set X : ℝ := Real.log ((N : ℝ) * (|t| + 2)) with hX
  have hta : 0 ≤ |t| := abs_nonneg t
  have hlX : Real.log N ≤ X := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hX1 : 1 ≤ X := hl1.trans hlX
  have hqN' : (q : ℝ) ≤ N := by
    calc (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := hqN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlog : Real.log (2 * q * (|t| + 6)) ≤ 5 + X := by
    have h6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      linarith
    have hle : 2 * q * (|t| + 6) ≤ 6 * ((N : ℝ) * (|t| + 2)) := by nlinarith
    calc Real.log (2 * q * (|t| + 6)) ≤ Real.log (6 * ((N : ℝ) * (|t| + 2))) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 6 + X := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 5 + X := by linarith
  have hM : Real.log (2 * q * (|t| + 6)) + K + 1 ≤ (7 + K) * X := by nlinarith
  have hM0 : 0 ≤ Real.log (2 * q * (|t| + 6)) + K + 1 := by
    have : 0 ≤ Real.log (2 * q * (|t| + 6)) := Real.log_nonneg (by nlinarith)
    linarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have h1X3 : 1 ≤ X ^ 3 := by nlinarith
  have hstep : 8 * Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) ≤
      8 * (7 + K) * X ^ 3 := by
    have ha : Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) ≤ X * ((7 + K) * X) :=
      mul_le_mul hlX hM hM0 (by linarith)
    have : X * ((7 + K) * X) = (7 + K) * X ^ 2 := by ring
    nlinarith
  have hKX : K ≤ K * X ^ 3 := by nlinarith
  calc ‖G s‖ ≤ K + 8 * Real.log N * (Real.log (2 * q * (|t| + 6)) + K + 1) := hB
    _ ≤ (9 * K + 57) * X ^ 3 := by nlinarith

/-! ### Cahen Mellin (Burst1122CahenMellin) -/


/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
integrand of the Gamma function is continuous on the positive half line. -/
lemma laplace_continuousOn_b1122x (s z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.cpow_const
      (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht)
  · fun_prop

/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
integrand is integrable on the positive half line when re s and re z are positive. -/
lemma laplace_integrable_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re - 1) (b := z.re) (by linarith) (by norm_num) hz
  refine Integrable.mono' hb ((laplace_continuousOn_b1122x s z).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
transform of t to the s minus 1 is complex differentiable in the rate z on re z > 0,
by differentiation under the integral sign. -/
lemma laplace_differentiable_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)) z := by
  let F : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (s - 1) * (Complex.exp (-w * t) * (-t))
  let r : ℝ := z.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hm : ∀ w : ℂ, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) :=
    fun w => (laplace_continuousOn_b1122x s w).aestronglyMeasurable measurableSet_Ioi
  have hm' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    dsimp [F']
    simp only [← mul_assoc]
    exact (laplace_continuousOn_b1122x s z).mul
      (show ContinuousOn (fun t : ℝ => -(t : ℂ)) (Ioi 0) by fun_prop)
  have hb : IntegrableOn (fun t : ℝ => t ^ s.re * Real.exp (-r * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re) (b := r) (by linarith) (by norm_num) hr
  have hd : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      HasDerivAt (fun w => F w t) (F' w t) w := by
    apply Eventually.of_forall
    intro t w _
    dsimp [F, F']
    simpa using (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).const_mul
      ((t : ℂ) ^ (s - 1))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      ‖F' w t‖ ≤ t ^ s.re * Real.exp (-r * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    intro w hw
    have hw' : r ≤ w.re := by
      have hn : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
      have hre := Complex.abs_re_le_norm (w - z)
      have hre' := (abs_le.mp (le_trans hre hn.le)).1
      simp only [sub_re] at hre'
      dsimp [r] at *
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    have he : (-w * (t : ℂ)).re = -w.re * t := by simp
    rw [he]
    have hp : t ^ (s.re - 1) * t = t ^ s.re := by
      conv_lhs => arg 2; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc _ = (t ^ (s.re - 1) * t) * Real.exp (-w.re * t) := by simp; ring
      _ = t ^ s.re * Real.exp (-w.re * t) := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hw') ht.le))
        (Real.rpow_nonneg ht.le _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := ball z r) (μ := volume.restrict (Ioi 0))
    (ball_mem_nhds z hr) (Eventually.of_forall hm)
    (laplace_integrable_b1122x hs hz) hm' hbound hb hd
  exact h.2.differentiableAt

/-- Textbook Euler integral with complex rate, Whittaker and Watson 12.2, used at
P0093 page 156: for re s > 0 and re z > 0 the Laplace integral of t to the s minus 1
equals z to the minus s times Gamma s. Proved by the identity theorem in z from
the real rate case in Mathlib. -/
theorem laplace_eq_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) =
      z ^ (-s) * Complex.Gamma s := by
  set L : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)
    with hLdef
  change L z = _
  have hReal : ∀ r : ℝ, 0 < r → L (r : ℂ) = (r : ℂ) ^ (-s) * Complex.Gamma s := by
    intro r hr
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    simpa only [hLdef, one_div, Complex.inv_cpow_ofReal_nonneg hr.le,
      Complex.cpow_neg, Complex.ofReal_neg, Complex.ofReal_mul, neg_mul] using h
  have hL : AnalyticOnNhd ℂ L {w : ℂ | 0 < w.re} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (laplace_differentiable_b1122x hs hw).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hR : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-s) * Complex.Gamma s)
      {w : ℂ | 0 < w.re} := by
    apply DifferentiableOn.analyticOnNhd _
      (isOpen_lt continuous_const Complex.continuous_re)
    intro w hw
    have hp : DifferentiableAt ℂ (fun u : ℂ => u ^ (-s)) w :=
      differentiableAt_id.cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
    exact (hp.mul_const _).differentiableWithinAt
  have hc : (1 : ℂ) ∈ closure
      ({w : ℂ | L w = w ^ (-s) * Complex.Gamma s} \ {1}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d : ℝ := min (ε / 2) 1
    have hd : 0 < d := lt_min (by linarith) (by norm_num)
    refine ⟨((1 + d : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · exact hReal _ (by linarith)
      · simp only [mem_singleton_iff]
        intro h
        have h' := congr_arg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h'
        linarith
    · rw [dist_eq_norm]
      have he : ((1 + d : ℝ) : ℂ) - 1 = (d : ℂ) := by push_cast; ring
      rw [norm_sub_rev, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he := hL.eqOn_of_preconnected_of_mem_closure hR
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (1 : ℂ)) (by simp) hc
  exact he hz

/-- P0093 page 157 Gamma decay on the line re s = 2: by Gamma of s plus one equal to
s Gamma s and the strip bound at re s = 1, Gamma of 2 + it is at most
2 sqrt 2 pi times one plus |t| cubed times e to the minus pi |t| / 2. -/
lemma gamma_two_line_bound_b1122x (t : ℝ) :
    ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * Real.sqrt (2 * Real.pi) * ((1 + |t|) ^ 3 * Real.exp (-(Real.pi * |t| / 2))) := by
  set s1 : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hs1
  have hs1ne : s1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hs1] at this
  have he : (2 : ℂ) + (t : ℂ) * Complex.I = s1 + 1 := by rw [hs1]; ring
  rw [he, Complex.Gamma_add_one s1 hs1ne, norm_mul]
  have hre : s1.re = 1 := by simp [hs1]
  have him : s1.im = t := by simp [hs1]
  have hg := gamma_absolute_decay519 s1 (by rw [hre]; norm_num)
    (by rw [hre]; norm_num)
  rw [him] at hg
  have hn1 : ‖s1‖ ≤ 1 + |t| := by
    calc ‖s1‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          norm_one]
  have hn2 : ‖s1 + 1‖ ≤ 2 + |t| := by
    have he2 : s1 + 1 = (2 : ℂ) + (t : ℂ) * Complex.I := by rw [hs1]; ring
    rw [he2]
    calc ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ = 2 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  have hE : 0 ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
  have hS : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have ht : 0 ≤ |t| := abs_nonneg t
  have hpoly : (1 + |t|) * (2 + |t|) ≤ 2 * (1 + |t|) ^ 3 := by
    nlinarith [sq_nonneg |t|, pow_nonneg ht 3]
  calc ‖s1‖ * ‖Complex.Gamma s1‖
      ≤ (1 + |t|) * (Real.sqrt (2 * Real.pi) * (2 + |t|) *
          Real.exp (-(Real.pi * |t| / 2))) := by
        apply mul_le_mul hn1 (hg.trans ?_) (norm_nonneg _) (by positivity)
        gcongr
    _ = Real.sqrt (2 * Real.pi) * ((1 + |t|) * (2 + |t|)) *
          Real.exp (-(Real.pi * |t| / 2)) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (1 + |t|) ^ 3) *
          Real.exp (-(Real.pi * |t| / 2)) := by gcongr
    _ = _ := by ring

/-- P0093 page 156 kernel on the line re s = 2: for re z > 0 the function
t to z to the minus 2 + it times Gamma of 2 + it is continuous. -/
lemma kernel_two_continuous_b1122x {z : ℂ} (hz : 0 < z.re) :
    Continuous (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  apply Continuous.mul
  · exact Continuous.const_cpow (by fun_prop) (Or.inl hz0)
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    intro n he
    have hre := congrArg Complex.re he
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- P0093 page 156 kernel on the line re s = 2: for re z > 0, so that |arg z| is
less than pi / 2, the Mellin kernel z to the minus s times Gamma s is integrable
along re s = 2, by the Gamma decay e to the minus pi |t| / 2 against the growth
e to the |arg z| |t| of z to the minus s. -/
lemma kernel_two_integrable_b1122x {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have harg : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  set δ : ℝ := Real.pi / 2 - |Complex.arg z| with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set C : ℝ := ‖z‖ ^ (-2 : ℝ) * (2 * Real.sqrt (2 * Real.pi)) with hC
  refine ((exp_decay_cubic_integrable519x δ hδ).const_mul C).mono'
    (kernel_two_continuous_b1122x hz).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hcp : ‖z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      ‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
    rw [Complex.norm_cpow_of_ne_zero hz0]
    have hre : (-((2 : ℂ) + (t : ℂ) * Complex.I)).re = -2 := by simp
    have him : (-((2 : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
    rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
    gcongr
    have h1 : -(Complex.arg z * -t) = Complex.arg z * t := by ring
    rw [h1, ← abs_mul]
    exact le_abs_self _
  have hg := gamma_two_line_bound_b1122x t
  rw [norm_mul]
  calc ‖z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ *
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|)) *
        (2 * Real.sqrt (2 * Real.pi) *
          ((1 + |t|) ^ 3 * Real.exp (-(Real.pi * |t| / 2)))) :=
        mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
        rw [hC, hδdef]
        have hx : Real.exp (|Complex.arg z| * |t|) * Real.exp (-(Real.pi * |t| / 2)) =
            Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |t|)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ = ‖z‖ ^ (-2 : ℝ) * (2 * Real.sqrt (2 * Real.pi)) *
              ((Real.exp (|Complex.arg z| * |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                (1 + |t|) ^ 3) := by ring
          _ = _ := by rw [hx]

/-- P0093 page 159 equation 5.1, Cahen Mellin inversion for one frequency on the
line re s = 2: for re z > 0 and x > 0, one over 2 pi times the integral of
x to the minus s times z to the minus s times Gamma s is e to the minus z x. -/
theorem cahen_single_b1122x {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
        (z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (-z * x) := by
  let f : ℝ → ℂ := fun y => Complex.exp (-z * y)
  have hm : ∀ s : ℂ, 0 < s.re → mellin f s = z ^ (-s) * Complex.Gamma s := by
    intro s hs
    simpa only [mellin, f, smul_eq_mul] using laplace_eq_b1122x hs hz
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hline : ∀ t : ℝ, mellin f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [h2]
    exact hm _ (by simp)
  have hc : MellinConvergent f ((2 : ℝ) : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul] using
      laplace_integrable_b1122x (s := ((2 : ℝ) : ℂ)) (by simp) hz
  have hv : Complex.VerticalIntegrable (mellin f) 2 := by
    unfold Complex.VerticalIntegrable
    simp only [hline]
    exact kernel_two_integrable_b1122x hz
  have h := mellinInv_mellin_eq 2 f hx hc hv (by dsimp [f]; fun_prop)
  unfold mellinInv at h
  simp only [hline, smul_eq_mul, Complex.real_smul] at h
  simpa only [h2, f] using h

/-- P0093 page 159 before equation 5.1: the k + 1 st power term of the
logarithmic Euler series is one over k + 1 times chi of p to the k + 1
times the power p to the k + 1 raised to minus s. -/
lemma euler_term_eq_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (p k : ℕ) (s : ℂ) :
    (χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) =
      ((k : ℂ) + 1)⁻¹ * χ (p ^ (k + 1)) * ((((p : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-s) := by
  have h1 : ((p : ℂ) ^ (-s)) ^ (k + 1) = ((((p : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-s) := by
    rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
    push_cast
    rfl
  rw [mul_pow, h1, map_pow, div_eq_mul_inv]
  ring

/-- P0093 page 159 before equation 5.1: on re s = 2 each Euler term has norm at most
p to the minus 2 times 2 to the minus k. -/
lemma euler_term_norm_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (p : Nat.Primes) (k : ℕ)
    (t : ℝ) :
    ‖(χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) ^ (k + 1) /
        ((k : ℂ) + 1)‖ ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : 0 < (p : ℕ) := p.2.pos
  set r : ℝ := (((p : ℕ) : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := by
    rw [hr]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hbase : ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ≤ r := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hre : (-((2 : ℂ) + (t : ℂ) * Complex.I)).re = -2 := by simp
    rw [hre]
    have hrp : ((p : ℕ) : ℝ) ^ (-2 : ℝ) = r := by
      rw [hr, Real.rpow_neg (by positivity)]
      norm_cast
    rw [hrp]
    calc ‖χ (p : ℕ)‖ * r ≤ 1 * r :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) hr0
      _ = r := one_mul r
  have hk : (1 : ℝ) ≤ ‖((k : ℂ) + 1)‖ := by
    have : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact this
  rw [norm_div, norm_pow]
  calc ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ (k + 1) /
        ‖((k : ℂ) + 1)‖
      ≤ ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ (k + 1) :=
        div_le_self (by positivity) hk
    _ ≤ r ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hbase _
    _ = r * r ^ k := by ring
    _ ≤ r * (1 / 2 : ℝ) ^ k := by
        gcongr

/-- P0093 page 159 before equation 5.1: the sum over primes of p to the minus 2
converges. -/
lemma summable_prime_inv_sq_b1122x :
    Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  exact h.comp_injective Subtype.val_injective

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1:
on re s = 2 the Mellin integral of z to the minus s times Gamma s times G s, with G
the logarithmic Euler series of L of s and chi, is the damped prime power series
with exponential phases. -/
theorem cahen_mellin_line_two_proof_b1122 (N : ℕ) (hN : 1 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) (α : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
          G ((2 : ℂ) + (t : ℂ) * Complex.I)
      = ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)) := by
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : 0 < z.re := by
    rw [hzdef]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; simp [hNpos]
  set K : ℝ → ℂ := fun t => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) with hKdef
  have hK : Integrable K := kernel_two_integrable_b1122x hz
  have hKc : Continuous K := kernel_two_continuous_b1122x hz
  set T : Nat.Primes → ℕ → ℝ → ℂ := fun p k t =>
    (χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) ^ (k + 1) /
      ((k : ℂ) + 1) with hTdef
  set u : Nat.Primes → ℕ → ℝ := fun p k => (((p : ℕ) : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k with hudef
  have hTb : ∀ p k t, ‖T p k t‖ ≤ u p k := fun p k t => euler_term_norm_b1122x χ p k t
  have hu : ∀ p, Summable (u p) := fun p => summable_geometric_two.mul_left _
  have hu0 : ∀ p k, 0 ≤ u p k := fun p k => by rw [hudef]; positivity
  have hus : ∀ p, ∑' k, u p k = 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro p; rw [hudef]; simp only; rw [tsum_mul_left, tsum_geometric_two]; ring
  have hTc : ∀ p k, Continuous (T p k) := by
    intro p k
    rw [hTdef]
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    apply Continuous.div_const
    apply Continuous.pow
    apply Continuous.mul continuous_const
    exact Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  set H : Nat.Primes → ℝ → ℂ := fun p t => ∑' k, T p k t with hHdef
  have hHc : ∀ p, Continuous (H p) := fun p => continuous_tsum (hTc p) (hu p) (hTb p)
  have hHb : ∀ p t, ‖H p t‖ ≤ 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro p t
    rw [← hus p]
    exact tsum_of_norm_bounded (hu p).hasSum (fun k => hTb p k t)
  set IK : ℝ := ∫ t, ‖K t‖ with hIK
  -- inner interchange for fixed p
  have hFint : ∀ p k, Integrable (fun t => K t * T p k t) := by
    intro p k
    refine (hK.norm.mul_const (u p k)).mono' (hKc.mul (hTc p k)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hTb p k t) (norm_nonneg _)
  have hFnorm : ∀ p k, ∫ t, ‖K t * T p k t‖ ≤ IK * u p k := by
    intro p k
    rw [hIK, ← integral_mul_const]
    apply integral_mono (hFint p k).norm (hK.norm.mul_const _)
    intro t
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hTb p k t) (norm_nonneg _)
  have hIK0 : 0 ≤ IK := integral_nonneg fun t => norm_nonneg _
  have hinner : ∀ p, ∑' k, (∫ t, K t * T p k t) = ∫ t, K t * H p t := by
    intro p
    have hs : Summable fun k => ∫ t, ‖K t * T p k t‖ :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
        (hFnorm p) ((hu p).mul_left IK)
    rw [integral_tsum_of_summable_integral_norm (hFint p) hs]
    congr 1
    funext t
    rw [hHdef]
    exact tsum_mul_left
  -- outer interchange
  have hGint : ∀ p, Integrable (fun t => K t * H p t) := by
    intro p
    refine (hK.norm.mul_const (2 * (((p : ℕ) : ℝ) ^ 2)⁻¹)).mono'
      (hKc.mul (hHc p)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hHb p t) (norm_nonneg _)
  have hGsum : Summable fun p => ∫ t, ‖K t * H p t‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
      (fun p => ?_) ((summable_prime_inv_sq_b1122x.mul_left 2).mul_left IK)
    rw [hIK, ← integral_mul_const]
    apply integral_mono (hGint p).norm (hK.norm.mul_const _)
    intro t
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hHb p t) (norm_nonneg _)
  have houter : ∑' p, (∫ t, K t * H p t) = ∫ t, ∑' p, K t * H p t :=
    integral_tsum_of_summable_integral_norm hGint hGsum
  -- rewrite the left side
  have hlhs : (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) * G ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      fun t => ∑' p, K t * H p t := by
    funext t
    rw [hGs _ (by simp), tsum_mul_left]
  rw [hlhs, ← houter, ← tsum_mul_left]
  congr 1
  funext p
  rw [← hinner p, ← tsum_mul_left]
  congr 1
  funext k
  -- one term
  have hn : 0 < ((p : ℕ) : ℝ) ^ (k + 1) := by
    have : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    positivity
  have hterm : (fun t => K t * T p k t) = fun t : ℝ =>
      (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1))) *
        ((((((p : ℕ) : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
          (z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I))) := by
    funext t
    rw [hTdef, hKdef]
    simp only
    rw [euler_term_eq_b1122x χ (p : ℕ) k]
    ring
  have hexp : Complex.exp (-z * ((((p : ℕ) : ℝ) ^ (k + 1) : ℝ) : ℂ)) =
      (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hzdef]
    push_cast
    ring
  rw [hterm, integral_const_mul, mul_left_comm, cahen_single_b1122x hz hn, hexp]
  ring

/-! ### Line shift (Burst1122LineShift) -/


/-- Textbook step behind P0093 page 156: Cauchy's theorem on the rectangle with corners
a minus T i and b plus T i, for a function differentiable at every point of the closed
vertical strip a at most re s at most b. The difference of the two vertical integrals
times i equals the difference of the two horizontal integrals. -/
theorem rect_identity_b1122x (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s) (T : ℝ) :
    Complex.I * ((∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
    (∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * Complex.I)) -
      ∫ x : ℝ in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (⟨a, -T⟩ : ℂ) (⟨b, T⟩ : ℂ) ?_
  · dsimp only at H
    simp only [smul_eq_mul] at H
    linear_combination H
  · intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨h1, -⟩ := hs
    dsimp only at h1
    rw [Set.uIcc_of_le hab] at h1
    exact (hd s h1.1 h1.2).differentiableWithinAt

/-- Textbook step behind P0093 page 156: a vertical line of integration may be moved across
a strip where the integrand is holomorphic, integrable on both edges, and bounded by a
function of the height that tends to zero. The horizontal sides of the rectangles vanish
in the limit and the vertical sides tend to the two line integrals. -/
theorem strip_shift_b1122x (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (ha : Integrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)))
    (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hfg : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g |s.im|) :
    ∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I) := by
  have hre : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by intro x y; simp
  have him : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by intro x y; simp
  set Hh : ℝ → ℂ := fun y => ∫ x : ℝ in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I) with hHh
  have hH : ∀ y : ℝ, ‖Hh y‖ ≤ g |y| * |b - a| := by
    intro y
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have := hfg ((x : ℂ) + (y : ℂ) * Complex.I) (by rw [hre]; exact hx.1.le)
      (by rw [hre]; exact hx.2)
    rwa [him] at this
  have hlim0 : Tendsto (fun T : ℝ => Hh T - Hh (-T)) atTop (𝓝 0) := by
    have hg2 : Tendsto (fun T : ℝ => 2 * |b - a| * g T) atTop (𝓝 0) := by
      simpa using hg.const_mul (2 * |b - a|)
    apply squeeze_zero_norm' _ hg2
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have h1 := hH T
    have h2 := hH (-T)
    rw [abs_neg, abs_of_nonneg hT] at h2
    rw [abs_of_nonneg hT] at h1
    calc ‖Hh T - Hh (-T)‖ ≤ ‖Hh T‖ + ‖Hh (-T)‖ := norm_sub_le _ _
      _ ≤ g T * |b - a| + g T * |b - a| := add_le_add h1 h2
      _ = 2 * |b - a| * g T := by ring
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hlim1 := (hvb.sub hva).const_mul Complex.I
  have heq : (fun T : ℝ => Complex.I * ((∫ y : ℝ in -T..T, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      ∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * Complex.I))) =
      fun T : ℝ => Hh T - Hh (-T) := by
    funext T
    exact rect_identity_b1122x f a b hab hd T
  rw [heq] at hlim1
  have h0 := tendsto_nhds_unique hlim1 hlim0
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have := (mul_eq_zero.mp h0).resolve_left hI
  exact (sub_eq_zero.mp this).symm

/-- Textbook integrability step for P0093 page 157: every power of the absolute value
times a two sided exponential decay is integrable on the real line. -/
theorem abs_pow_exp_integrable_b1122x (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) := by
  have hk : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (b := δ) (by linarith [Nat.cast_nonneg (α := ℝ) k])
        (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Ioi 0) := by
    refine hk.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [abs_of_pos (show (0 : ℝ) < t from ht)]
  have hc : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|))) (Set.Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => |t| ^ k * Real.exp (-(δ * |t|)))
      (Set.Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hn.union hp

/-- Textbook integrability step for P0093 page 157: the weight one plus absolute t to the
fifth times exp of minus delta absolute t is integrable for delta positive. -/
theorem quintic_exp_integrable_b1122x (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ 5 * Real.exp (-(δ * |t|))) := by
  have h0 := abs_pow_exp_integrable_b1122x δ hδ 0
  have h5 := abs_pow_exp_integrable_b1122x δ hδ 5
  refine Integrable.mono' ((h0.add h5).const_mul 32) ?_ (ae_of_all _ fun t => ?_)
  · exact (by fun_prop : Continuous fun t : ℝ =>
      (1 + |t|) ^ 5 * Real.exp (-(δ * |t|))).aestronglyMeasurable
  · have hx : 0 ≤ |t| := abs_nonneg t
    have hpoly : (1 + |t|) ^ 5 ≤ 32 * (|t| ^ 0 + |t| ^ 5) := by
      rcases le_total |t| 1 with h | h
      · have h32 : (1 + |t|) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have h5 : 0 ≤ |t| ^ 5 := by positivity
        rw [pow_zero]
        linarith
      · have h32 : (1 + |t|) ^ 5 ≤ (2 * |t|) ^ 5 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 5
        rw [mul_pow] at h32
        rw [pow_zero]
        linarith
    have he : 0 < Real.exp (-(δ * |t|)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith

/-- Textbook limit for P0093 page 156: A times one plus u to the fifth times exp of minus
delta u tends to 0 as u tends to infinity, for delta positive. It kills the horizontal
sides of the rectangles. -/
theorem quintic_exp_tendsto_b1122x (A δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun u : ℝ => A * ((1 + u) ^ 5 * Real.exp (-(δ * u)))) atTop (𝓝 0) := by
  have hv : Tendsto (fun u : ℝ => δ * (1 + u)) atTop atTop :=
    (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hδ
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp hv).const_mul
    (A * Real.exp δ / δ ^ 5)
  rw [mul_zero] at h
  refine h.congr (fun u => ?_)
  simp only [Function.comp]
  rw [show -(δ * (1 + u)) = -δ + -(δ * u) by ring, Real.exp_add, Real.exp_neg δ]
  have he : Real.exp δ ≠ 0 := (Real.exp_pos δ).ne'
  have hd : δ ^ 5 ≠ 0 := pow_ne_zero 5 hδ.ne'
  field_simp

/-- P0093 page 157 Gamma decay, extended by the functional equation Gamma of s equals
s minus 1 times Gamma of s minus 1 to the strip from 1/2 to 2: the norm of Gamma s is at
most square root of 2 pi times 9 times one plus absolute im s squared times exp of minus
pi absolute im s over 2. -/
theorem gamma_strip_two_b1122x (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * (9 * (1 + |s.im|) ^ 2) *
      Real.exp (-(Real.pi * |s.im| / 2)) := by
  have ht := abs_nonneg s.im
  rcases le_or_gt s.re (3 / 2) with h | h
  · have hg := gamma_absolute_decay519 s hlo h
    have hn : ‖s + 1‖ ≤ 9 * (1 + |s.im|) ^ 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im (s + 1)
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
        add_zero] at hh
      rw [abs_of_pos (by linarith : 0 < s.re + 1)] at hh
      nlinarith
    calc ‖Complex.Gamma s‖ ≤ _ := hg
      _ ≤ _ := by gcongr
  · have hs1 : s - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have hrec : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
      have := Complex.Gamma_add_one (s - 1) hs1
      rwa [sub_add_cancel] at this
    have hre1 : (s - 1).re = s.re - 1 := by simp
    have him1 : (s - 1).im = s.im := by simp
    have hg := gamma_absolute_decay519 (s - 1) (by rw [hre1]; linarith)
      (by rw [hre1]; linarith)
    rw [sub_add_cancel, him1] at hg
    have hn1 : ‖s - 1‖ ≤ 3 * (1 + |s.im|) := by
      have hh := Complex.norm_le_abs_re_add_abs_im (s - 1)
      rw [hre1, him1, abs_of_pos (by linarith : 0 < s.re - 1)] at hh
      linarith
    have hn2 : ‖s‖ ≤ 3 * (1 + |s.im|) := by
      have hh := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos (by linarith : 0 < s.re)] at hh
      linarith
    have hg2 : ‖Complex.Gamma (s - 1)‖ ≤ Real.sqrt (2 * Real.pi) * (3 * (1 + |s.im|)) *
        Real.exp (-(Real.pi * |s.im| / 2)) := hg.trans (by gcongr)
    rw [hrec, norm_mul]
    calc ‖s - 1‖ * ‖Complex.Gamma (s - 1)‖
        ≤ (3 * (1 + |s.im|)) * (Real.sqrt (2 * Real.pi) * (3 * (1 + |s.im|)) *
            Real.exp (-(Real.pi * |s.im| / 2))) := by gcongr
      _ = _ := by ring

/-- P0093 page 156 size of the kernel z to the power minus s: for z nonzero and
0 at most re s at most 2, its norm is at most one plus norm z to the minus 2, times
exp of absolute arg z times absolute im s. -/
theorem cpow_neg_bound_b1122x (z : ℂ) (hz : z ≠ 0) (s : ℂ) (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖z ^ (-s)‖ ≤ (1 + ‖z‖ ^ (-2 : ℝ)) * Real.exp (|Complex.arg z| * |s.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hz]
  simp only [Complex.neg_re, Complex.neg_im]
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : ‖z‖ ^ (-s.re) ≤ 1 + ‖z‖ ^ (-2 : ℝ) := by
    rcases le_total 1 ‖z‖ with h | h
    · have := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith : -s.re ≤ 0)
      have := Real.rpow_nonneg hx.le (-2 : ℝ)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx h (by linarith : (-2 : ℝ) ≤ -s.re)
      linarith
  have he : 1 / Real.exp (Complex.arg z * -s.im) ≤ Real.exp (|Complex.arg z| * |s.im|) := by
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [← abs_mul]
    have h1 := le_abs_self (Complex.arg z * s.im)
    have h2 : -(Complex.arg z * -s.im) = Complex.arg z * s.im := by ring
    linarith
  rw [div_eq_mul_one_div]
  exact mul_le_mul hp he (by positivity) (by positivity)

/-- P0093 page 159 bound for log L on the line, made polynomial: for N at least 2 the
logarithm of N times absolute t plus 2 lies between 0 and log N plus 1 times one plus
absolute t. -/
theorem log_poly_b1122x (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    0 ≤ Real.log ((N : ℝ) * (|t| + 2)) ∧
      Real.log ((N : ℝ) * (|t| + 2)) ≤ (Real.log N + 1) * (1 + |t|) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht := abs_nonneg t
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine ⟨Real.log_nonneg (by nlinarith), ?_⟩
  rw [Real.log_mul (by positivity) (by positivity)]
  have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |t| + 2)
  nlinarith

/-- P0093 page 156 decay of the Mellin integrand z to the minus s times Gamma s times G s
on the closed strip from 1/2 plus 1/ln N to 2: a constant times one plus absolute im s to
the fifth times exp of minus pi over 2 minus absolute arg z, times absolute im s. -/
theorem integrand_bound_b1122x (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3)
    (z : ℂ) (hz : z ≠ 0) (s : ℂ) (h1 : 1 / 2 + 1 / Real.log N ≤ s.re) (h2 : s.re ≤ 2) :
    ‖z ^ (-s) * Complex.Gamma s * G s‖ ≤
      ((1 + ‖z‖ ^ (-2 : ℝ)) * Real.sqrt (2 * Real.pi) * 9 * |B0| * (Real.log N + 1) ^ 3) *
        ((1 + |s.im|) ^ 5 * Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |s.im|))) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hc : 1 / 2 ≤ s.re := by
    have : 0 < 1 / Real.log N := by positivity
    linarith
  have hA := cpow_neg_bound_b1122x z hz s (by linarith) h2
  have hB := gamma_strip_two_b1122x s hc h2
  obtain ⟨hl0, hl1⟩ := log_poly_b1122x N hN s.im
  have hC : ‖G s‖ ≤ |B0| * (Real.log N + 1) ^ 3 * (1 + |s.im|) ^ 3 := by
    calc ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 := hGb s h1 h2
      _ ≤ |B0| * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |B0| * ((Real.log N + 1) * (1 + |s.im|)) ^ 3 := by gcongr
      _ = _ := by ring
  rw [norm_mul, norm_mul]
  calc ‖z ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖G s‖
      ≤ ((1 + ‖z‖ ^ (-2 : ℝ)) * Real.exp (|Complex.arg z| * |s.im|)) *
        (Real.sqrt (2 * Real.pi) * (9 * (1 + |s.im|) ^ 2) *
          Real.exp (-(Real.pi * |s.im| / 2))) *
        (|B0| * (Real.log N + 1) ^ 3 * (1 + |s.im|) ^ 3) := by gcongr
    _ = _ := by
      have : Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |s.im|)) =
          Real.exp (|Complex.arg z| * |s.im|) * Real.exp (-(Real.pi * |s.im| / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      ring

/-- P0093 page 156 equation 4.1 and page 159 before equation 5.1: under the bound on G on
the strip, the Mellin integral on the line re s equal to 1/2 plus 1/ln N equals the one on
the line re s equal to 2, by Cauchy on rectangles and the decay of Gamma. -/
theorem mellin_line_shift_proof_b1122 (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ)
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re}) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3) (α : ℝ) :
    mellinU519 N (fun t : ℝ => G (mellinLine519 N t)) α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
            G ((2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hc12 : 1 / 2 < 1 / 2 + 1 / Real.log N := by
    have : 0 < 1 / Real.log N := by positivity
    linarith
  have hc2 : 1 / 2 + 1 / Real.log N ≤ 2 := by
    have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
    have h23 : (2 : ℝ) / 3 ≤ Real.log N := by
      have := Real.log_two_gt_d9; linarith
    have : 1 / Real.log N ≤ 3 / 2 := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hzre : 0 < z.re := by
    have h := one_div_pos.mpr (show (0 : ℝ) < N by linarith)
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact h
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hδ : 0 < Real.pi / 2 - |Complex.arg z| := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
    linarith
  let F : ℂ → ℂ := fun s => z ^ (-s) * Complex.Gamma s * G s
  have hFd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ F s := by
    intro s hs
    have hnp : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hG' : DifferentiableAt ℂ G s :=
      hGd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hz)).mul
      (Complex.differentiableAt_Gamma s hnp)).mul hG'
  let A : ℝ := (1 + ‖z‖ ^ (-2 : ℝ)) * Real.sqrt (2 * Real.pi) * 9 * |B0| *
    (Real.log N + 1) ^ 3
  let g : ℝ → ℝ := fun u => A * ((1 + u) ^ 5 * Real.exp (-((Real.pi / 2 - |Complex.arg z|) * u)))
  have hFb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 → ‖F s‖ ≤ g |s.im| :=
    fun s h1 h2 => integrand_bound_b1122x N hN G B0 hGb z hz s h1 h2
  have hgi : Integrable (fun t : ℝ => g |t|) :=
    (quintic_exp_integrable_b1122x _ hδ).const_mul A
  have hline : ∀ σ : ℝ, 1 / 2 + 1 / Real.log N ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    intro σ h1 h2
    have hre : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by intro t; simp
    have him : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by intro t; simp
    refine hgi.mono' ?_ (ae_of_all _ fun t => ?_)
    · have hcont : Continuous (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (hFd _ (by rw [hre]; linarith)).continuousAt.comp (by fun_prop)
      exact hcont.aestronglyMeasurable
    · have := hFb ((σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact h1) (by rw [hre]; exact h2)
      rwa [him] at this
  have hg : Tendsto g atTop (𝓝 0) := quintic_exp_tendsto_b1122x A _ hδ
  have key := strip_shift_b1122x F (1 / 2 + 1 / Real.log N) 2 hc2
    (fun s h1 _ => hFd s (by linarith)) (hline _ le_rfl hc2) (hline 2 hc2 le_rfl) g hg hFb
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at key
  rw [mellinU519]
  exact congrArg (fun w => ((1 / (2 * Real.pi) : ℝ) : ℂ) * w) key

/-! ### Prime power tail (SPLIT_grh_mellin_transfer519) -/

/-! ### Telescoping series with a shift -/

private lemma pp519_tel_shift (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1))
      = 1 / (M : ℝ) - 1 / ((K : ℝ) + M) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((K : ℝ) + M) ≠ 0 := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        positivity
      have h2 : ((K : ℝ) + M + 1) ≠ 0 := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        positivity
      push_cast
      field_simp
      try ring

private lemma pp519_tel_nonneg (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    0 ≤ (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1) := by
  have h1 : (0 : ℝ) < (k : ℝ) + M := by
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hle : (1 : ℝ) / ((k : ℝ) + M + 1) ≤ 1 / ((k : ℝ) + M) :=
    one_div_le_one_div_of_le h1 (by linarith)
  linarith

private lemma pp519_shift_tendsto (M : ℕ) :
    Tendsto (fun K : ℕ => (K : ℝ) + M) atTop atTop := by
  refine tendsto_atTop_mono (fun K => ?_) tendsto_natCast_atTop_atTop
  have h : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  linarith

private lemma pp519_tel_hasSum (M : ℕ) (hM : 1 ≤ M) :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1))
      (1 / (M : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (pp519_tel_nonneg M hM) (1 / (M : ℝ))]
  have hlim : Tendsto (fun K : ℕ => ((K : ℝ) + M)⁻¹) atTop (nhds 0) :=
    (pp519_shift_tendsto M).inv_tendsto_atTop
  have hlim2 : Tendsto (fun K : ℕ => (1 : ℝ) / ((K : ℝ) + M)) atTop (nhds 0) := by
    simpa only [one_div] using hlim
  have h0 : Tendsto (fun K : ℕ => (1 : ℝ) / (M : ℝ) - 1 / ((K : ℝ) + M)) atTop
      (nhds (1 / (M : ℝ) - 0)) := tendsto_const_nhds.sub hlim2
  simp only [sub_zero] at h0
  refine h0.congr' ?_
  filter_upwards with K
  exact (pp519_tel_shift M hM K).symm

/-! ### The tail of `1/n^2` -/

private lemma pp519_sq_term_le (k M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2
      ≤ (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1) := by
  set n : ℝ := (k : ℝ) + M + 1 with hn
  set m : ℝ := (k : ℝ) + M with hm
  have hm1 : n = m + 1 := by rw [hn, hm]
  have hm1' : (1 : ℝ) ≤ m := by
    rw [hm]
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hmp : (0 : ℝ) < m := by linarith
  have hnp : (0 : ℝ) < n := by rw [hm1]; linarith
  have hkey : (1 : ℝ) / (m * n) = 1 / m - 1 / n := by
    field_simp
    try rw [hm1]
    try ring
  rw [← hkey]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

private lemma pp519_tail_sq (M : ℕ) (hM : 1 ≤ M) :
    ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2 ≤ 1 / (M : ℝ) := by
  have hsum1 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_sq_term_le k M hM)
      (pp519_tel_hasSum M hM).summable
  calc ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2
      ≤ ∑' k : ℕ, ((1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1)) :=
        hsum1.tsum_le_tsum (fun k => pp519_sq_term_le k M hM) (pp519_tel_hasSum M hM).summable
    _ = 1 / (M : ℝ) := (pp519_tel_hasSum M hM).tsum_eq

/-! ### The telescoping square-root series -/

private lemma pp519_sqrt_tel_shift (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        ((1 : ℝ) / Real.sqrt ((k : ℝ) + M) - 1 / Real.sqrt ((k : ℝ) + M + 1))
      = 1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((K : ℝ) + M) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma pp519_sqrt_tel_nonneg (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    0 ≤ (1 : ℝ) / Real.sqrt ((k : ℝ) + M) - 1 / Real.sqrt ((k : ℝ) + M + 1) := by
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < Real.sqrt ((k : ℝ) + M) := by
    apply Real.sqrt_pos.mpr; linarith
  have hlt : Real.sqrt ((k : ℝ) + M) < Real.sqrt ((k : ℝ) + M + 1) := by
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hle : (1 : ℝ) / Real.sqrt ((k : ℝ) + M + 1) ≤ 1 / Real.sqrt ((k : ℝ) + M) :=
    one_div_le_one_div_of_le h1 hlt.le
  linarith

private lemma pp519_sqrt_tel_hasSum (M : ℕ) (hM : 1 ≤ M) :
    HasSum (fun k : ℕ => (1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) (1 / Real.sqrt (M : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (pp519_sqrt_tel_nonneg M hM) (1 / Real.sqrt (M : ℝ))]
  have hlim : Tendsto (fun K : ℕ => (Real.sqrt ((K : ℝ) + M))⁻¹) atTop (nhds 0) :=
    ((Real.tendsto_sqrt_atTop).comp (pp519_shift_tendsto M)).inv_tendsto_atTop
  have hlim2 : Tendsto (fun K : ℕ => (1 : ℝ) / Real.sqrt ((K : ℝ) + M)) atTop (nhds 0) := by
    simpa only [one_div] using hlim
  have h0 : Tendsto (fun K : ℕ => (1 : ℝ) / Real.sqrt (M : ℝ)
      - 1 / Real.sqrt ((K : ℝ) + M)) atTop (nhds (1 / Real.sqrt (M : ℝ) - 0)) :=
    tendsto_const_nhds.sub hlim2
  simp only [sub_zero] at h0
  refine h0.congr' ?_
  filter_upwards with K
  exact (pp519_sqrt_tel_shift M hM K).symm


/-! ### The termwise bound `1/(n √n) ≤ 2 (1/√(n-1) - 1/√n)` -/

private lemma pp519_cube_term_le (k M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) := by
  set n : ℝ := (k : ℝ) + M + 1 with hn
  set a : ℝ := Real.sqrt (n - 1) with ha_def
  set b : ℝ := Real.sqrt n with hb_def
  have hn2 : (2 : ℝ) ≤ n := by
    rw [hn]
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn1 : (0 : ℝ) ≤ n - 1 := by linarith
  have ha2 : a ^ 2 = n - 1 := by rw [ha_def]; exact Real.sq_sqrt hn1
  have hb2 : b ^ 2 = n := by rw [hb_def]; exact Real.sq_sqrt hn0
  have ha : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := by rw [hb_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hna : Real.sqrt ((k : ℝ) + M) = a := by rw [ha_def, hn]; ring_nf
  have hnb : Real.sqrt ((k : ℝ) + M + 1) = b := by rw [hb_def, hn]
  have hnk : ((k : ℝ) + M + 1) = n := by rw [hn]
  -- main inequality on a, b
  have key : a * (1 + 2 * b ^ 2) ≤ 2 * b ^ 3 := by
    have hsq : (a * (1 + 2 * b ^ 2)) ^ 2 ≤ (2 * b ^ 3) ^ 2 := by
      have expand : (a * (1 + 2 * b ^ 2)) ^ 2 = (n - 1) * (1 + 2 * n) ^ 2 := by
        rw [mul_pow, ha2, hb2]
      have expand2 : (2 * b ^ 3) ^ 2 = 4 * n ^ 3 := by
        have h3 : b ^ 3 = n * b := by rw [show b ^ 3 = b ^ 2 * b by ring, hb2]
        rw [h3]
        nlinarith [hb2]
      rw [expand, expand2]
      nlinarith
    have h1 : (0 : ℝ) ≤ a * (1 + 2 * b ^ 2) := by positivity
    by_contra hcon
    push_neg at hcon
    have hb3pos : (0 : ℝ) ≤ 2 * b ^ 3 := by linarith [pow_pos hb 3]
    have := pow_lt_pow_left₀ hcon hb3pos (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have hkey : (1 : ℝ) / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  have hgoal : (1 : ℝ) / b ^ 3 ≤ 2 * ((b - a) / (a * b)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < b ^ 3)]
    have e : 2 * ((b - a) / (a * b)) * b ^ 3 = 2 * b ^ 2 * (b - a) / a := by
      field_simp
    rw [e, le_div_iff₀ ha]
    nlinarith [key]
  have hb3 : (n : ℝ) * b = b ^ 3 := by
    have : b ^ 3 = b ^ 2 * b := by ring
    rw [this, hb2]
  have hmain : (1 : ℝ) / (n * b) ≤ 2 * ((b - a) / (a * b)) := by
    rw [hb3]
    exact hgoal
  calc (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      = 1 / (n * b) := by rw [hnk, hnb]
    _ ≤ 2 * ((b - a) / (a * b)) := hmain
    _ = 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) := by rw [hna, hnb, hkey]

private lemma pp519_tail_cube (M : ℕ) (hM : 1 ≤ M) :
    ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ 2 / Real.sqrt (M : ℝ) := by
  have hbig : HasSum (fun k : ℕ => 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
      - 1 / Real.sqrt ((k : ℝ) + M + 1))) (2 * (1 / Real.sqrt (M : ℝ))) :=
    (pp519_sqrt_tel_hasSum M hM).mul_left 2
  have hsum1 : Summable (fun k : ℕ =>
      (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_cube_term_le k M hM)
      hbig.summable
  calc ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ ∑' k : ℕ, 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
          - 1 / Real.sqrt ((k : ℝ) + M + 1)) :=
        hsum1.tsum_le_tsum (fun k => pp519_cube_term_le k M hM) hbig.summable
    _ = 2 / Real.sqrt (M : ℝ) := by
        rw [hbig.tsum_eq]; ring


/-! ### The exponential is at most the minimum of one and the inverse -/

private lemma pp519_exp_le_min {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ min 1 x⁻¹ := by
  refine le_min ?_ ?_
  · rw [Real.exp_le_one_iff]; linarith
  · rw [Real.exp_neg, ← one_div]
    have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    simpa [one_div] using one_div_le_one_div_of_le hx h1

private lemma pp519_sqrt_pow_two (j : ℕ) :
    Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private lemma pp519_sqrt_geo (ξ : ℝ) (hξ : 0 < ξ) (j : ℕ) :
    Real.sqrt ((ξ * (2 : ℝ) ^ j)⁻¹) = (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := by
  have hx : (0 : ℝ) ≤ ξ⁻¹ := le_of_lt (inv_pos.mpr hξ)
  rw [show (ξ * (2 : ℝ) ^ j)⁻¹ = ξ⁻¹ * ((2 : ℝ) ^ j)⁻¹ by rw [mul_inv],
    Real.sqrt_mul hx, Real.sqrt_inv, Real.sqrt_inv, pp519_sqrt_pow_two j, inv_pow]

private lemma pp519_min_one_le_sqrt {y : ℝ} (hy : 0 < y) : min 1 y ≤ Real.sqrt y := by
  rcases le_or_gt 1 y with h | h
  · rw [min_eq_left h]
    exact Real.one_le_sqrt.mpr h
  · rw [min_eq_right h.le]
    refine (Real.le_sqrt hy.le hy.le).mpr ?_
    nlinarith

private lemma pp519_geom (ξ : ℝ) (hξ : 0 < ξ) :
    ∑' j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹) ≤ 7 / 2 / Real.sqrt ξ := by
  have hr0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hr1 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  have hterm : ∀ j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)
      ≤ (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := by
    intro j
    have hy : (0 : ℝ) < (ξ * (2 : ℝ) ^ j)⁻¹ := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) _
      exact inv_pos.mpr (mul_pos hξ h2)
    exact (pp519_min_one_le_sqrt hy).trans (le_of_eq (pp519_sqrt_geo ξ hξ j))
  have hsum : Summable (fun j : ℕ => (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsumL : Summable (fun j : ℕ => min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hsum
  have h70 : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
    refine (Real.le_sqrt (by norm_num) (by norm_num)).mpr ?_
    norm_num
  have hinv : (Real.sqrt 2)⁻¹ ≤ 5 / 7 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 5) h70
    simpa [one_div] using h
  have hpos : (0 : ℝ) < 1 - (Real.sqrt 2)⁻¹ := by linarith
  have hle : (1 - (Real.sqrt 2)⁻¹)⁻¹ ≤ 7 / 2 := by
    have h2 : (0 : ℝ) < 2 / 7 := by norm_num
    have := (inv_le_inv₀ hpos h2).mpr (by linarith : (2 : ℝ) / 7 ≤ 1 - (Real.sqrt 2)⁻¹)
    simpa using this
  calc ∑' j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)
      ≤ ∑' j : ℕ, (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := hsumL.tsum_le_tsum hterm hsum
    _ = (Real.sqrt ξ)⁻¹ * (1 - (Real.sqrt 2)⁻¹)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 7 / 2 / Real.sqrt ξ := by
        have h0 : (0 : ℝ) ≤ (Real.sqrt ξ)⁻¹ := by positivity
        calc (Real.sqrt ξ)⁻¹ * (1 - (Real.sqrt 2)⁻¹)⁻¹
            ≤ (Real.sqrt ξ)⁻¹ * (7 / 2) := mul_le_mul_of_nonneg_left hle h0
          _ = 7 / 2 / Real.sqrt ξ := by
              rw [div_eq_mul_inv]
              ring

/-! ### Summability corollaries -/

private lemma pp519_summable_sq_shift :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 2) ^ 2)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using pp519_sq_term_le k 1 (by norm_num))
    (pp519_tel_hasSum 1 (by norm_num)).summable

private lemma pp519_summable_sq_tail (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + M + 1) ^ 2)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_sq_term_le k M hM)
    (pp519_tel_hasSum M hM).summable

private lemma pp519_summable_cube_shift :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using pp519_cube_term_le k 1 (by norm_num))
    ((pp519_sqrt_tel_hasSum 1 (by norm_num)).mul_left 2).summable

/-! ### The two scalar sums over `ℕ` -/

set_option maxHeartbeats 1000000 in
private lemma pp519_sum_one_aux (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hMn : (N : ℝ) ≤ ((M : ℝ)) ^ 2) (hMle : (M : ℝ) ≤ 2 * Real.sqrt (N : ℝ)) :
    ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 4 * Real.sqrt N := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum : Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun m => le_min zero_le_one (by positivity))
      (fun m => min_le_right _ _) ?_
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (pp519_summable_sq_shift.mul_left (N : ℝ))
    rw [show (N : ℝ) * (1 / (((m : ℝ) + 2) ^ 2)) = (N : ℝ) / (((m : ℝ) + 2) ^ 2) by ring]
  have hsplit := (hsum.sum_add_tsum_nat_add M).symm
  have hhead : ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ (M : ℝ) := by
    have hle : ∀ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 1 :=
      fun m _ => min_le_left _ _
    calc ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
        ≤ ∑ _m ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum hle
      _ = (M : ℝ) := by simp
  have hshift : ∀ k : ℕ, (((k + M : ℕ) : ℝ) + 2) = ((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) := by
    intro k; push_cast; ring
  have htail : ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
      ≤ (N : ℝ) * (1 / ((M : ℝ) + 1)) := by
    have hmaj : ∀ k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
        ≤ (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
      intro k
      rw [hshift k]
      calc min 1 ((N : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2))
          ≤ (N : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2) := min_le_right _ _
        _ = (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by ring
    have hs : Summable (fun k : ℕ => (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2))) :=
      (pp519_summable_sq_tail (M + 1) (by omega)).mul_left (N : ℝ)
    have hs' : Summable (fun k : ℕ => min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))) :=
      Summable.of_nonneg_of_le (fun k => le_min zero_le_one (by positivity)) hmaj hs
    calc ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
        ≤ ∑' k : ℕ, (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) :=
          hs'.tsum_le_tsum hmaj hs
      _ = (N : ℝ) * (∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
          rw [tsum_mul_left]
      _ ≤ (N : ℝ) * (1 / ((M : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hNpos)
          have h := pp519_tail_sq (M + 1) (by omega)
          have hcast : (((M + 1 : ℕ)) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
          rw [hcast] at h
          simpa [Nat.cast_add, Nat.cast_one] using h
  have hNM : (N : ℝ) * (1 / ((M : ℝ) + 1)) ≤ (M : ℝ) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [hMn, hMpos]
  calc ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
      = ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
        + ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2)) := hsplit
    _ ≤ (M : ℝ) + (M : ℝ) := by linarith
    _ ≤ 4 * Real.sqrt (N : ℝ) := by linarith

private lemma pp519_sum_one (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 4 * Real.sqrt N := by
  have hM1 : 1 ≤ Nat.sqrt N + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hMn : (N : ℝ) ≤ (((Nat.sqrt N + 1 : ℕ)) : ℝ) ^ 2 := by
    have h2 : ((N : ℕ) : ℝ) ≤ (((Nat.sqrt N + 1) ^ 2 : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_of_lt (Nat.lt_succ_sqrt' N)
    simpa using h2
  have hsqr : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h : (((Nat.sqrt N : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
    have h' := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by positivity)] at h'
  have hMle : (((Nat.sqrt N + 1 : ℕ)) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
    have h2 : (((Nat.sqrt N + 1 : ℕ)) : ℝ) = ((Nat.sqrt N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]; linarith
  exact pp519_sum_one_aux N (Nat.sqrt N + 1) hN hM1 hMn hMle

set_option maxHeartbeats 1000000 in
private lemma pp519_sum_two (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)) ≤ 2 * Real.sqrt N := by
  have hcongr : (∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
      = Real.sqrt (N : ℝ) *
        ∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hx : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : ((m : ℝ) + 2) ^ 3 = ((m : ℝ) + 2) ^ 2 * ((m : ℝ) + 2) := by ring
    rw [Real.sqrt_div (by positivity), h3, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx.le]
    field_simp
  have h2 : (∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2))) ≤ 2 := by
    have h := pp519_tail_cube 1 (by norm_num)
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  rw [hcongr]
  calc Real.sqrt (N : ℝ) * (∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)))
      ≤ Real.sqrt (N : ℝ) * 2 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt N := by ring

/-! ### The norm of a single prime power term -/

private lemma pp519_inv_cast_norm (k : ℕ) : ‖((k : ℂ) + 2)⁻¹‖ = ((k : ℝ) + 2)⁻¹ := by
  have hk : ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) := by push_cast; ring
  have hn : ‖(k : ℂ) + 2‖ = (k : ℝ) + 2 := by
    rw [hk, Complex.norm_natCast]
    push_cast
    ring
  rw [norm_inv, hn]

private lemma pp519_term_norm (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (α : ℝ) (p : Nat.Primes) (k : ℕ) :
    ‖((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by
  have hexp : ‖Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      = 1 := Complex.norm_exp_ofReal_mul_I _
  have hchi : ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ 1 := χ.norm_le_one _
  have hreal : ‖(Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ)‖
      = Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hpos : (0 : ℝ) < Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := Real.exp_pos _
  have hchip : ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ ((k : ℝ) + 2)⁻¹ := by
    have h0 : (0 : ℝ) ≤ ((k : ℝ) + 2)⁻¹ := by positivity
    calc ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ ((k : ℝ) + 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hchi h0
      _ = ((k : ℝ) + 2)⁻¹ := mul_one _
  calc ‖((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      = ‖((k : ℂ) + 2)⁻¹‖ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          ‖(Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ)‖ *
            ‖Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ = ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) * 1 := by
        rw [pp519_inv_cast_norm, hreal, hexp]
    _ = ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by rw [mul_one]
    _ ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hchip (le_of_lt hpos)

/-! ### The bound for one prime -/

set_option maxHeartbeats 1000000 in
private lemma pp519_inner (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (α : ℝ) (p : Nat.Primes) :
    ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
  let g : ℕ → ℂ := fun k => ((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)
  change ‖∑' k : ℕ, g k‖ ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hP0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkey : ∀ k : ℕ, ‖g k‖ ≤ ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) := by
    intro k
    have h := pp519_term_norm N hN q χ α p k
    have hPk : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (k + 2) := pow_pos hP0 _
    have hpos : (0 : ℝ) < (((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ)) := div_pos hPk hN0
    have h2 := pp519_exp_le_min hpos
    have heq : ((((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ)))⁻¹
        = (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := by rw [inv_div]
    rw [heq] at h2
    exact h.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hgeo : Summable (fun k : ℕ => ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) *
      ((((p : ℕ) : ℝ)⁻¹)) ^ k) := by
    have hr0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ)⁻¹ := by positivity
    have hr1 : ((p : ℕ) : ℝ)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      linarith
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hmaj : ∀ k : ℕ, ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
      ≤ ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) * ((((p : ℕ) : ℝ)⁻¹)) ^ k := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
    have hPk : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (k + 2) := pow_pos hP0 _
    have hX : (0 : ℝ) < (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := div_pos hN0 hPk
    have h1 : ((k : ℝ) + 2)⁻¹ ≤ 1 := by
      have hge : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith
      calc ((k : ℝ) + 2)⁻¹ ≤ (1 : ℝ)⁻¹ :=
            (inv_le_inv₀ hk2 (by norm_num : (0 : ℝ) < 1)).mpr hge
        _ = 1 := inv_one
    have h2 : min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := min_le_right _ _
    have h3 : (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))
        = ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) * ((((p : ℕ) : ℝ)⁻¹)) ^ k := by
      rw [inv_pow]
      field_simp
      ring
    have hstep1 : ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ ((k : ℝ) + 2)⁻¹ * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hstep2 : ((k : ℝ) + 2)⁻¹ * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ 1 * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) := by
      rw [one_mul]
      exact mul_le_of_le_one_left (le_of_lt hX) h1
    exact hstep1.trans (hstep2.trans (le_of_eq (by rw [one_mul, h3])))
  have hsum : Summable (fun k : ℕ => ‖g k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => (hkey k).trans (hmaj k)) hgeo
  have hsplit := (hsum.sum_add_tsum_nat_add 1).symm
  rw [Finset.sum_range_one] at hsplit
  have hk0 : ‖g 0‖ ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) := by
    have h := hkey 0
    simpa using h
  have hcube : Summable (fun i : ℕ => min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹) := by
    have hxi : (0 : ℝ) < (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
      have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
      exact div_pos h3 hN0
    have hr0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
    have hr1 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
    have hsumgeo : Summable (fun i : ℕ => (Real.sqrt ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ))))⁻¹
        * ((Real.sqrt 2)⁻¹) ^ i) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsumgeo
    have hy : (0 : ℝ) < ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
      have h2i : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos (by norm_num) _
      exact inv_pos.mpr (mul_pos hxi h2i)
    exact (pp519_min_one_le_sqrt hy).trans (le_of_eq (pp519_sqrt_geo _ hxi i))
  have htail : ∑' i : ℕ, ‖g (i + 1)‖ ≤ 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
    have hmaj2 : ∀ i : ℕ, ‖g (i + 1)‖ ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
      intro i
      refine (hkey (i + 1)).trans ?_
      have h1 : (((i + 1 : ℕ)) : ℝ) + 2 = (i : ℝ) + 3 := by push_cast; ring
      have hexp : (i + 1) + 2 = i + 3 := by omega
      rw [h1, hexp]
      have hfac : ((i : ℝ) + 3)⁻¹ ≤ 1 := by
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        have hi3 : (0 : ℝ) < (i : ℝ) + 3 := by linarith
        have hge : (1 : ℝ) ≤ (i : ℝ) + 3 := by linarith
        calc ((i : ℝ) + 3)⁻¹ ≤ (1 : ℝ)⁻¹ :=
              (inv_le_inv₀ hi3 (by norm_num : (0 : ℝ) < 1)).mpr hge
          _ = 1 := inv_one
      have hP3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
      have h2i : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos (by norm_num) _
      have hPi : (2 : ℝ) ^ i ≤ ((p : ℕ) : ℝ) ^ i :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 i
      have hden : ((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i ≤ ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i :=
        mul_le_mul_of_nonneg_left hPi (le_of_lt hP3)
      have hstep : (N : ℝ) / (((p : ℕ) : ℝ) ^ (i + 3))
          ≤ ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        have hpos1 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i := mul_pos hP3 h2i
        have hpos2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i :=
          mul_pos hP3 (pow_pos hP0 i)
        have hinv : (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)⁻¹
            ≤ (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i)⁻¹ :=
          (inv_le_inv₀ hpos2 hpos1).mpr hden
        have hle : (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)
            ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
          calc (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)
              = (N : ℝ) * ((((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i))⁻¹ := by
                rw [div_eq_mul_inv]
            _ ≤ (N : ℝ) * ((((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i))⁻¹ :=
                mul_le_mul_of_nonneg_left hinv (le_of_lt hN0)
            _ = (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
                rw [div_eq_mul_inv]
        have e1 : ((p : ℕ) : ℝ) ^ (i + 3) = ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i := by
          rw [pow_add, mul_comm]
        have e2 : ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹
            = (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
          rw [mul_inv]
          field_simp
        rw [e1, e2]
        exact hle
      have hmin : min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        rw [show (i + 1) + 2 = i + 3 by omega]
        exact min_le_min_left 1 hstep
      have hstep1 : ((i : ℝ) + 3)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ 1 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2))) := by
        rw [one_mul]
        have hNk : (0 : ℝ) ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)) := by
          have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ ((i + 1) + 2) := pow_pos hP0 _
          exact le_of_lt (div_pos hN0 h3)
        exact mul_le_of_le_one_left (le_min (by norm_num : (0 : ℝ) ≤ 1) hNk) hfac
      have hstep2 : 1 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        rw [one_mul]
        exact hmin
      exact hstep1.trans hstep2
    have hs1 : Summable (fun i : ℕ => ‖g (i + 1)‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hmaj2 hcube
    calc ∑' i : ℕ, ‖g (i + 1)‖
        ≤ ∑' i : ℕ, min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ :=
          hs1.tsum_le_tsum hmaj2 hcube
      _ ≤ 7 / 2 / Real.sqrt (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
          have hxi : (0 : ℝ) < (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
            have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
            exact div_pos h3 hN0
          exact pp519_geom _ hxi
      _ = 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
          rw [div_eq_mul_inv]
          congr 1
          rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), inv_div]
  have hnn : ‖∑' k : ℕ, g k‖ ≤ ∑' k : ℕ, ‖g k‖ := norm_tsum_le_tsum_norm hsum
  have hfin : ∑' k : ℕ, ‖g k‖ = ‖g 0‖ + ∑' i : ℕ, ‖g (i + 1)‖ := hsplit
  linarith [hnn, hk0, htail]

/-! ### Square root of a quotient cube -/

private lemma pp519_sqrt_div_eq (N : ℕ) (m : ℕ) :
    Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))
      = Real.sqrt (N : ℝ) * ((1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2))) := by
  have hx : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have h3 : ((m : ℝ) + 2) ^ 3 = ((m : ℝ) + 2) ^ 2 * ((m : ℝ) + 2) := by ring
  rw [Real.sqrt_div (by positivity), h3, Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
  field_simp

/-! ### Summability of the two scalar families -/

private lemma pp519_summable_min (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => min_le_right _ _) ?_
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (pp519_summable_sq_shift.mul_left (N : ℝ))
  rw [show (N : ℝ) * (1 / (((m : ℝ) + 2) ^ 2)) = (N : ℝ) / (((m : ℝ) + 2) ^ 2) by ring]

private lemma pp519_summable_sqrtN (N : ℕ) :
    Summable (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))) := by
  refine Summable.of_nonneg_of_le (fun m => Real.sqrt_nonneg _) (fun m => ?_)
    (pp519_summable_cube_shift.mul_left (Real.sqrt (N : ℝ)))
  rw [pp519_sqrt_div_eq N m]

/-! ### From primes to natural numbers -/

private lemma pp519_prime_shift_inj :
    Function.Injective (fun p : Nat.Primes => (p : ℕ) - 2) := by
  intro p q h
  have hp : ((p : ℕ) - 2) + 2 = (p : ℕ) := Nat.sub_add_cancel p.prop.two_le
  have hq : ((q : ℕ) - 2) + 2 = (q : ℕ) := Nat.sub_add_cancel q.prop.two_le
  have h' : ((p : ℕ) - 2) = ((q : ℕ) - 2) := h
  have h2 : (p : ℕ) = (q : ℕ) := by
    calc (p : ℕ) = ((p : ℕ) - 2) + 2 := hp.symm
      _ = ((q : ℕ) - 2) + 2 := by rw [h']
      _ = (q : ℕ) := hq
  exact Nat.Primes.coe_nat_injective h2

private lemma pp519_shift_cast (p : Nat.Primes) :
    (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = ((p : ℕ) : ℝ) := by
  have hp : 2 ≤ (p : ℕ) := p.prop.two_le
  have h : ((p : ℕ) - 2 : ℕ) + 2 = (p : ℕ) := Nat.sub_add_cancel hp
  calc (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = (((((p : ℕ) - 2 : ℕ)) + 2 : ℕ) : ℝ) := by push_cast; ring
    _ = ((p : ℕ) : ℝ) := by rw [h]

private lemma pp519_prime_le_one (N : ℕ) (hN : 1 ≤ N) :
    ∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
      ≤ ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) := by
  have hcongr : (∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)))
      = ∑' p : Nat.Primes, (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)))
          ((p : ℕ) - 2) := by
    refine tsum_congr (fun p : Nat.Primes => ?_)
    show min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
      = min 1 ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 2)
    rw [pp519_shift_cast p]
  rw [hcongr]
  exact tsum_comp_le_tsum_of_inj (pp519_summable_min N hN) (fun m => by positivity)
    pp519_prime_shift_inj

private lemma pp519_prime_le_two (N : ℕ) :
    ∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
      ≤ ∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)) := by
  have hcongr : (∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)))
      = ∑' p : Nat.Primes, (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
          ((p : ℕ) - 2) := by
    refine tsum_congr (fun p : Nat.Primes => ?_)
    show Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
      = Real.sqrt ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 3)
    rw [pp519_shift_cast p]
  rw [hcongr]
  exact tsum_comp_le_tsum_of_inj (pp519_summable_sqrtN N) (fun m => Real.sqrt_nonneg _)
    pp519_prime_shift_inj

private lemma pp519_summable_prime_one (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))) := by
  have h0 : Summable ((fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)))
      ∘ (fun p : Nat.Primes => (p : ℕ) - 2)) :=
    (pp519_summable_min N hN).comp_injective pp519_prime_shift_inj
  exact h0.congr (fun p => by
    show min 1 ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 2)
      = min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
    rw [pp519_shift_cast p])

private lemma pp519_summable_prime_two (N : ℕ) :
    Summable (fun p : Nat.Primes => Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) := by
  have h0 : Summable ((fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
      ∘ (fun p : Nat.Primes => (p : ℕ) - 2)) :=
    (pp519_summable_sqrtN N).comp_injective pp519_prime_shift_inj
  exact h0.congr (fun p => by
    show Real.sqrt ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 3)
      = Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
    rw [pp519_shift_cast p])

/-- LEAF. Prime power tail step. The part of the prime power double sum with
exponents at least two, summed over all primes and all such exponents, is at
most a constant independent of N, of the character and of alpha, times the
square root of N. The exponential damping at the prime powers is what makes the
double sum absolutely convergent. No zero hypothesis, no Mellin integral and no
estimate on the character occur here. -/
theorem prime_power_tail519 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
        ‖∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
          ≤ B * Real.sqrt N := by
  refine ⟨11, by norm_num, 0, ?_⟩
  intro N hN q hq χ α
  have hmin : Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) :=
    pp519_summable_min N hN
  have hsq : Summable (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))) :=
    pp519_summable_sqrtN N
  have hp1 : Summable (fun p : Nat.Primes => min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))) :=
    pp519_summable_prime_one N hN
  have hp2 : Summable (fun p : Nat.Primes => Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
    pp519_summable_prime_two N
  have hmaj : Summable (fun p : Nat.Primes =>
      1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
    (hp1.mul_left (1 / 2)).add (hp2.mul_left (7 / 2))
  have hinner : Summable (fun p : Nat.Primes =>
      ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => pp519_inner N hN q χ α p) hmaj
  have h1 := pp519_prime_le_one N hN
  have h2 := pp519_prime_le_two N
  have hb1 := pp519_sum_one N hN
  have hb2 := pp519_sum_two N hN
  calc ‖∑' p : Nat.Primes, ∑' k : ℕ,
        (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ ∑' p : Nat.Primes, ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖ :=
        norm_tsum_le_tsum_norm hinner
    _ ≤ ∑' p : Nat.Primes, (1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
          + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
        hinner.tsum_le_tsum (fun p => pp519_inner N hN q χ α p) hmaj
    _ = 1 / 2 * (∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)))
          + 7 / 2 * (∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) := by
        rw [Summable.tsum_add (hp1.mul_left (1 / 2)) (hp2.mul_left (7 / 2)),
          tsum_mul_left, tsum_mul_left]
    _ ≤ 1 / 2 * (4 * Real.sqrt (N : ℝ)) + 7 / 2 * (2 * Real.sqrt (N : ℝ)) := by
        have h3 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        nlinarith [h1, h2, hb1, hb2]
    _ ≤ 11 * Real.sqrt (N : ℝ) := by
        have h3 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        linarith

/-! ### GRH nonvanishing, holomorphic log, and the assembly (Burst1122GrhTransfer519) -/


open MeasureTheory Filter Finset Topology

/-! ### Step 1. Nonvanishing on the half plane under GRH -/

/-- P0093 page 159 before equation 5.1. Under GRH, the L-function of a nonprincipal
character has no zero with real part greater than 1/2: in the strip below 1 by GRH,
and on re s at least 1 by the nonvanishing theorem of Mathlib. -/
theorem lfunction_ne_zero_half_b1122 (hG : LeanLab.DERZ1997.GRH) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 / 2 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h0
  rcases lt_or_ge s.re 1 with h1 | h1
  · have := hG q χ s h0 (by linarith) h1
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1 h0

/-! ### Step 2. The holomorphic logarithm of L on the half plane -/

/-- Two logarithms of the same function near a point. If d is continuous at s0 and
exp of d is eventually the constant exp of d s0, then d is eventually the constant d s0,
because two logarithms differ by an integer multiple of 2 pi i. -/
theorem eventually_eq_of_exp_eventually_eq_b1122 (d : ℂ → ℂ) (s0 : ℂ)
    (hd : ContinuousAt d s0) (he : ∀ᶠ s in 𝓝 s0, Complex.exp (d s) = Complex.exp (d s0)) :
    ∀ᶠ s in 𝓝 s0, d s = d s0 := by
  have hsmall : ∀ᶠ s in 𝓝 s0, ‖d s - d s0‖ < 2 * Real.pi := by
    have h : ContinuousAt (fun s => ‖d s - d s0‖) s0 := (hd.sub continuousAt_const).norm
    have h0 : ‖d s0 - d s0‖ < 2 * Real.pi := by
      rw [sub_self, norm_zero]; positivity
    exact h.eventually (Iio_mem_nhds h0)
  filter_upwards [hsmall, he] with s hs he'
  have h1 : Complex.exp (d s - d s0) = 1 := by
    rw [Complex.exp_sub, he', div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hn0 : n = 0 := by
    by_contra hne
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
    have hnorm : ‖d s - d s0‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    rw [hnorm] at hs
    nlinarith [Real.pi_pos]
  rw [hn0] at hn
  simpa [sub_eq_zero] using hn

/-- The open half plane re s greater than 1/2 is simply connected, being convex. -/
theorem halfplane_isSimplyConnected_b1122 (c : ℝ) :
    IsSimplyConnected {s : ℂ | c < s.re} := by
  have hne : ({s : ℂ | c < s.re}).Nonempty := ⟨(c + 1 : ℝ), by simp⟩
  have := (convex_halfSpace_re_gt (r := c)).contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- A continuous logarithm of a holomorphic nonvanishing function on an open set is
holomorphic there: near each point it is a constant plus the principal logarithm of a
quotient close to one. -/
theorem differentiableOn_of_continuous_log_b1122 {U : Set ℂ} (hU : IsOpen U)
    {f G : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ s ∈ U, f s ≠ 0)
    (hGc : ContinuousOn G U) (hGe : ∀ s ∈ U, Complex.exp (G s) = f s) :
    DifferentiableOn ℂ G U := by
  intro s0 hs0
  have hfa : DifferentiableAt ℂ f s0 := hf.differentiableAt (hU.mem_nhds hs0)
  have hf00 := hf0 s0 hs0
  set h : ℂ → ℂ := fun s => G s0 + Complex.log (f s / f s0) with hh
  have hslit : f s0 / f s0 ∈ Complex.slitPlane := by
    rw [div_self hf00]; exact Complex.one_mem_slitPlane
  have hhd : DifferentiableAt ℂ h s0 :=
    (differentiableAt_const _).add ((hfa.div_const _).clog hslit)
  have hd : ContinuousAt (fun s => G s - h s) s0 :=
    (hGc.continuousAt (hU.mem_nhds hs0)).sub hhd.continuousAt
  have hev : ∀ᶠ s in 𝓝 s0, Complex.exp (G s - h s) = Complex.exp (G s0 - h s0) := by
    have hnz : ∀ᶠ s in 𝓝 s0, f s ≠ 0 :=
      hfa.continuousAt.eventually_ne hf00
    filter_upwards [hU.mem_nhds hs0, hnz] with s hs hfs
    have hq : f s / f s0 ≠ 0 := div_ne_zero hfs hf00
    simp only [hh, Complex.exp_sub, Complex.exp_add, Complex.exp_log hq,
      Complex.exp_log (div_ne_zero hf00 hf00), hGe s hs, hGe s0 hs0]
    field_simp
  have hloc := eventually_eq_of_exp_eventually_eq_b1122 _ s0 hd hev
  have hzero : G s0 - h s0 = 0 := by
    simp [hh, div_self hf00]
  have hEq : G =ᶠ[𝓝 s0] h := by
    filter_upwards [hloc] with s hs
    rw [hzero] at hs
    exact sub_eq_zero.mp hs
  exact (hhd.congr_of_eventuallyEq hEq).differentiableWithinAt

/-- P0093 page 159 before equation 5.1 and page 155. A holomorphic nonvanishing
function on an open simply connected set has a holomorphic logarithm there. -/
theorem exists_holomorphic_log_b1122 {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ s ∈ U, f s ≠ 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ ∀ s ∈ U, Complex.exp (G s) = f s := by
  obtain ⟨G, hGc, hGe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hf.continuousOn
    (by rintro ⟨s, hs, h0⟩; exact hf0 s hs h0)
  exact ⟨G, differentiableOn_of_continuous_log_b1122 hUo hf hf0 hGc (fun s hs => hGe hs),
    fun s hs => hGe hs⟩

/-- P0093 page 155. The Euler logarithm series: the sum over primes p and exponents
k at least 1 of chi of p to the k times p to the minus k s over k. -/
theorem euler_log_term_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' k : ℕ, (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) =
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) := by
  apply HasSum.tsum_eq
  apply Complex.hasSum_taylorSeries_neg_log'
  have hp : 0 < (p : ℕ) := p.2.pos
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  have hχ : ‖χ (p : ℕ)‖ ≤ 1 := χ.norm_le_one _
  have hlt : ((p : ℕ) : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hχ (by positivity)
    _ < 1 := by rw [one_mul]; exact hlt

/-- The norm of the Euler factor variable is at most p to the minus sigma. -/
theorem euler_var_norm_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (p : Nat.Primes) :
    ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  calc ‖χ (p : ℕ)‖ * ((p : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ = _ := one_mul _

/-- P0093 page 155. The Euler logarithm sum over primes is continuous on re s
greater than 1, by local uniform convergence. -/
theorem continuousOn_euler_log_b1122 {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun s : ℂ => ∑' p : Nat.Primes,
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) {s : ℂ | 1 < s.re} := by
  intro s0 hs0
  simp only [Set.mem_ofPred_eq] at hs0
  set σ : ℝ := (1 + s0.re) / 2 with hσ
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  have hW : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs0W : s0 ∈ {s : ℂ | σ < s.re} := by simp only [Set.mem_ofPred_eq, hσ]; linarith
  have hsum : Summable (fun p : Nat.Primes => (3 / 2 : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)) := by
    apply Summable.mul_left
    have h := (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
    exact h.comp_injective Nat.Primes.coe_nat_injective
  have hcont : ContinuousOn (fun s : ℂ => ∑' p : Nat.Primes,
      -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))) {s : ℂ | σ < s.re} := by
    have hvar : ∀ p : Nat.Primes, ∀ s : ℂ, σ < s.re →
        ‖χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-σ) := by
      intro p s hs
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
      exact (euler_var_norm_b1122 χ s p).trans
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
    have hhalf : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
      intro p
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
      calc ((p : ℕ) : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = ((p : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    refine continuousOn_tsum (fun p => ?_) hsum (fun p s hs => ?_)
    · have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      intro s hs
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.neg
      apply ContinuousAt.clog
      · exact continuousAt_const.sub (continuousAt_const.mul
          (continuousAt_neg.const_cpow (Or.inl hp0)))
      · rw [sub_eq_add_neg]
        apply Complex.mem_slitPlane_of_norm_lt_one
        rw [norm_neg]
        exact ((hvar p s hs).trans (hhalf p)).trans_lt (by norm_num)
    · have hw := hvar p s hs
      have hw2 : ‖-(χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hw.trans (hhalf p)
      have hl := Complex.norm_log_one_add_half_le_self hw2
      rw [← sub_eq_add_neg, norm_neg] at hl
      rw [norm_neg]
      exact hl.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  exact (hcont.continuousAt (hW.mem_nhds hs0W)).continuousWithinAt


/-- Two continuous logarithms of the same function on an open preconnected set differ
by a constant: a continuous function with exp equal to one there is constant. -/
theorem const_of_exp_eq_one_b1122 {V : Set ℂ} (hVo : IsOpen V) (hVp : IsPreconnected V)
    {d : ℂ → ℂ} (hdc : ContinuousOn d V) (he : ∀ s ∈ V, Complex.exp (d s) = 1)
    {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V) : d x = d y := by
  set n : ℂ → ℤ := fun s => round ((d s / (2 * Real.pi * Complex.I)).re) with hn
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hrep : ∀ s ∈ V, d s = (n s : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (he s hs)
    have hq : d s / (2 * Real.pi * Complex.I) = (m : ℂ) := by
      rw [hm, mul_div_assoc, div_self h2pi, mul_one]
    have : n s = m := by
      simp only [hn, hq, Complex.intCast_re, round_intCast]
    rw [this, hm]
  have hnc : ContinuousOn n V := by
    intro s0 hs0
    apply ContinuousAt.continuousWithinAt
    have hev : ∀ᶠ s in 𝓝 s0, Complex.exp (d s) = Complex.exp (d s0) := by
      filter_upwards [hVo.mem_nhds hs0] with s hs
      rw [he s hs, he s0 hs0]
    have hloc := eventually_eq_of_exp_eventually_eq_b1122 d s0
      (hdc.continuousAt (hVo.mem_nhds hs0)) hev
    have hne : n =ᶠ[𝓝 s0] fun _ => n s0 := by
      filter_upwards [hloc] with s hs
      simp only [hn, hs]
    exact continuousAt_const.congr hne.symm
  rw [hrep x hx, hrep y hy, hVp.constant hnc hx hy]

/-- P0093 page 159 before equation 5.1 and page 155. Under GRH, for a nonprincipal
character there is a holomorphic logarithm G of the L-function on the open half plane
re s greater than 1/2 which on re s greater than 1 equals the prime power series, the
sum over primes p and k at least 1 of chi of p to the k times p to the minus k s over k. -/
theorem holomorphic_log_L_b1122 (hG : LeanLab.DERZ1997.GRH) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
        (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) := by
  have hHo : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨G0, hG0d, hG0e⟩ := exists_holomorphic_log_b1122 (halfplane_isSimplyConnected_b1122 _)
    hHo (f := DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    (fun s hs => lfunction_ne_zero_half_b1122 hG q χ hχ s hs)
  set E : ℂ → ℂ := fun s => ∑' p : Nat.Primes,
    -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) with hE
  have hVo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVp : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt (r := 1)).isPreconnected
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs; simp only [Set.mem_ofPred_eq] at hs ⊢; linarith
  have hEexp : ∀ s : ℂ, 1 < s.re → Complex.exp (E s) = DirichletCharacter.LFunction χ s := by
    intro s hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs]
  have hdc : ContinuousOn (fun s => G0 s - E s) {s : ℂ | 1 < s.re} :=
    (hG0d.continuousOn.mono hsub).sub (continuousOn_euler_log_b1122 χ)
  have hde : ∀ s ∈ {s : ℂ | 1 < s.re}, Complex.exp (G0 s - E s) = 1 := by
    intro s hs
    rw [Complex.exp_sub, hG0e s (hsub hs), hEexp s hs,
      div_self (lfunction_ne_zero_half_b1122 hG q χ hχ s (hsub hs))]
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  refine ⟨fun s => G0 s - (G0 2 - E 2), hG0d.sub_const _, fun s hs => ?_⟩
  have hc := const_of_exp_eq_one_b1122 hVo hVp hdc hde hs h2
  have : G0 s - (G0 2 - E 2) = E s := by
    have hc' : G0 s - E s = G0 2 - E 2 := hc
    rw [← hc']; ring
  show G0 s - (G0 2 - E 2) = _
  rw [this, hE]
  exact tsum_congr fun p => (euler_log_term_b1122 χ s hs p).symm

/-! ### Step 3. The cited GRH bound for the logarithm of L -/

/-- P0093 page 159 before equation 5.1, the ERH bound for ln L. Formerly a HARD LEAF,
PROVED in burst session S57 by grh_strip_log_bound_proof_b1122 of Burst1122LogBound via
Borel Caratheodory, with no zero sum. Former citation wall: the classical bound for log L under the generalized Riemann
hypothesis, Titchmarsh, The Theory of the Riemann Zeta-Function, section 14.2 and
Montgomery and Vaughan, Multiplicative Number Theory I, chapter 13. Under GRH, for
N large, q at most N to the 1/7, a nonprincipal character chi and the holomorphic
logarithm G of its L-function normalised by the prime power series on re s greater
than 1, the norm of G at every s with 1/2 + 1/ln N at most re s at most 2 is at most
B0 times the cube of ln of N times the absolute imaginary part plus 2. The constant
B0 does not depend on N, q or chi. -/
theorem grh_strip_log_bound_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ G : ℂ → ℂ,
          DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} →
          (∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
            (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) →
          ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
            ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3 :=
  grh_strip_log_bound_proof_b1122 hG

/-! ### Step 4. Mellin inversion on re s equal to 2 and the shift of the line -/

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1,
the Cahen Mellin formula on the line re s equal to 2. Formerly a MEDIUM LEAF, PROVED in
burst session S57 by cahen_mellin_line_two_proof_b1122 of Burst1122CahenMellin.
For z equal to 1/N + 2 pi i alpha, e to the minus n z is 1/(2 pi i) times the integral
of Gamma of s times n z to the minus s over re s equal to 2. Inserting the prime power
series of G, absolutely convergent on that line, and integrating term by term gives
the damped prime power series with weight 1/k. No zero hypothesis is used. -/
theorem cahen_mellin_line_two_b1122 (N : ℕ) (hN : 1 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) (α : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
          G ((2 : ℂ) + (t : ℂ) * Complex.I)
      = ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)) :=
  cahen_mellin_line_two_proof_b1122 N hN q χ G hGs α

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1,
the shift of the Mellin line from re s equal to 2 to re s equal to 1/2 + 1/ln N. Formerly a
MEDIUM LEAF, PROVED in burst session S57 by mellin_line_shift_proof_b1122 of Burst1122LineShift.
Cauchy's theorem on the rectangle with vertical sides on the two lines: G is
holomorphic on re s greater than 1/2, Gamma decays like e to the minus pi |t| / 2 while
z to the minus s grows at most like e to the |t| |arg z| with |arg z| less than pi / 2,
and G grows at most like a power of ln |t| in the strip, so the horizontal sides tend
to zero. No zero hypothesis is used beyond the holomorphy of G. -/
theorem mellin_line_shift_b1122 (N : ℕ) (hN : 2 ≤ N) (G : ℂ → ℂ)
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re}) (B0 : ℝ)
    (hGb : ∀ s : ℂ, 1 / 2 + 1 / Real.log N ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ B0 * Real.log ((N : ℝ) * (|s.im| + 2)) ^ 3) (α : ℝ) :
    mellinU519 N (fun t : ℝ => G (mellinLine519 N t)) α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
            G ((2 : ℂ) + (t : ℂ) * Complex.I) :=
  mellin_line_shift_proof_b1122 N hN G hGd B0 hGb α


/-! ### Separation of the exponent one terms -/

/-- For a prime p and k at least 0, p + k is at most p to the k + 1. -/
theorem prime_add_le_pow_b1122 (p : Nat.Primes) (k : ℕ) :
    (p : ℕ) + k ≤ (p : ℕ) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hpos : 1 ≤ (p : ℕ) ^ (k + 1) := Nat.one_le_pow _ _ p.2.pos
    rw [pow_succ]
    nlinarith

/-- The damping at a prime power is at most the damping at p times a geometric factor. -/
theorem damp_pow_le_b1122 (N : ℕ) (hN : 1 ≤ N) (p : Nat.Primes) (k : ℕ) :
    Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) ≤
      Real.exp (-((p : ℕ) : ℝ) / N) * Real.exp (-1 / (N : ℝ)) ^ k := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := prime_add_le_pow_b1122 p k
  have hR : ((p : ℕ) : ℝ) + k ≤ ((p : ℕ) : ℝ) ^ (k + 1) := by exact_mod_cast h
  have hdiv : (((p : ℕ) : ℝ) + k) / N ≤ ((p : ℕ) : ℝ) ^ (k + 1) / N :=
    div_le_div_of_nonneg_right hR hNp.le
  have heq : -((p : ℕ) : ℝ) / N + (k : ℝ) * (-1 / (N : ℝ)) = -((((p : ℕ) : ℝ) + k) / N) := by
    ring
  rw [heq]
  linarith

/-- P0093 page 159 before equation 5.1. Separating the exponent one terms of the
damped prime power series with weight 1/k leaves the damped character prime series
plus the prime power double sum with exponents at least two. -/
theorem exponent_one_split_b1122 (N : ℕ) (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (α : ℝ) :
    ∑' p : Nat.Primes, ∑' k : ℕ,
        (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I))
      = characterPrime519 χ N α + ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)) := by
  set f : Nat.Primes → ℕ → ℂ := fun p k =>
    ((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
      (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)
    with hf
  set r : ℝ := Real.exp (-1 / (N : ℝ)) with hr
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (by norm_num) hNp
  have hgeo : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hnorm : ∀ p k, ‖f p k‖ ≤ Real.exp (-((p : ℕ) : ℝ) / N) * r ^ k := by
    intro p k
    refine le_trans ?_ (damp_pow_le_b1122 N hN p k)
    simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : ‖((k : ℂ) + 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos k
    have h2 : ‖χ ((p : ℕ) ^ (k + 1))‖ ≤ 1 := χ.norm_le_one _
    calc ‖((k : ℂ) + 1)⁻¹‖ * ‖χ ((p : ℕ) ^ (k + 1))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ)))
        ≤ 1 * 1 * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumk : ∀ p, Summable (f p) := fun p =>
    Summable.of_norm_bounded (hgeo.mul_left _) (hnorm p)
  have hdamp : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
  have ha : Summable (fun p => f p 0) :=
    Summable.of_norm_bounded hdamp (fun p => by simpa using hnorm p 0)
  have hb : Summable (fun p => ∑' k : ℕ, f p (k + 1)) := by
    refine Summable.of_norm_bounded (hdamp.mul_right (∑' k : ℕ, r ^ (k + 1))) (fun p => ?_)
    have hs1 : Summable (fun k : ℕ => ‖f p (k + 1)‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hnorm p (k + 1))
        ((summable_nat_add_iff 1).mpr hgeo |>.mul_left _)
    calc ‖∑' k : ℕ, f p (k + 1)‖ ≤ ∑' k : ℕ, ‖f p (k + 1)‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' k : ℕ, Real.exp (-((p : ℕ) : ℝ) / N) * r ^ (k + 1) :=
          hs1.tsum_le_tsum (fun k => hnorm p (k + 1))
            ((summable_nat_add_iff 1).mpr hgeo |>.mul_left _)
      _ = _ := tsum_mul_left
  have hinner : ∀ p, ∑' k : ℕ, f p k = f p 0 + ∑' k : ℕ, f p (k + 1) := fun p =>
    (hsumk p).tsum_eq_zero_add
  rw [tsum_congr hinner, ha.tsum_add hb]
  congr 1
  · unfold characterPrime519
    refine tsum_congr fun p => ?_
    simp only [hf, Nat.cast_zero, zero_add, inv_one, one_mul, pow_one, neg_div]
  · refine tsum_congr fun p => tsum_congr fun k => ?_
    simp only [hf]
    push_cast
    ring_nf

/-! ### Assembly -/

/-- P0093 page 159 before equation 5.1, with page 156 equation 4.1. The statement of
grh_mellin_transfer519, with M equal to G composed with mellinLine519 N for the
holomorphic logarithm G of the L-function. CONDITIONAL ON grh_strip_log_bound_b1122,
cahen_mellin_line_two_b1122 and mellin_line_shift_b1122. -/
theorem grh_mellin_transfer519_b1122 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖characterPrime519 χ N α - mellinU519 N M α‖ ≤ B * Real.sqrt N := by
  obtain ⟨B0, hB0, N1, h3⟩ := grh_strip_log_bound_b1122 hG
  obtain ⟨B, hB, N2, htail⟩ := prime_power_tail519
  refine ⟨B0, hB0, B, hB, max N1 (max N2 2), ?_⟩
  intro N hN q hq hqt χ hχ
  have : NeZero q := ⟨by omega⟩
  obtain ⟨G, hGd, hGs⟩ := holomorphic_log_L_b1122 hG q χ hχ
  have hN2 : 2 ≤ N := by omega
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2R
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
  have hbound := h3 N (by omega) q hq hqt χ hχ G hGd hGs
  have hre : ∀ t : ℝ, (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : ∀ t : ℝ, (mellinLine519 N t).im = t := by
    intro t
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hle2 : 1 / 2 + 1 / Real.log N ≤ 2 := by
    have h23 : (2 : ℝ) / 3 ≤ Real.log N := by
      have := Real.log_two_gt_d9; linarith
    have : 1 / Real.log N ≤ 3 / 2 := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith
  refine ⟨fun t => G (mellinLine519 N t), ⟨?_, fun t => ?_⟩, fun α => ?_⟩
  · apply hGd.continuousOn.comp_continuous
    · unfold mellinLine519; fun_prop
    · intro t
      show 1 / 2 < (mellinLine519 N t).re
      rw [hre]; linarith [one_div_pos.mpr hlogpos]
  · have := hbound (mellinLine519 N t) (hre t).ge (by rw [hre]; exact hle2)
    rwa [him] at this
  · rw [mellin_line_shift_b1122 N hN2 G hGd B0 hbound α,
      cahen_mellin_line_two_b1122 N (by omega) q χ G hGs α,
      exponent_one_split_b1122 N (by omega) χ α, sub_add_cancel_left, norm_neg]
    exact htail N (by omega) q hq χ α

end PortB1122

/-- LEAF. P0093 page 159 before equation 5.1. GRH supplies the logarithm
of L on the vertical line with its uniform cubic logarithmic bound. The
Mellin identity retains the prime power correction bounded by square root N.
This is the corrected transfer already recorded for mellin_transfer1622.
There is no arc integral or rational system in this input. -/
theorem grh_mellin_transfer519 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖characterPrime519 χ N α - mellinU519 N M α‖ ≤ B * Real.sqrt N :=
  grh_mellin_transfer519_b1122 hG

/-- P0093 pages 156 through 158 Lemma 2 equations 4.1 through 4.8.
The diagonal square estimate is assembled from the clean central interval,
the signed outer estimate and the proved conjugate reflection.
CONDITIONAL ON lemma2_outer_square519. No GRH or prime occurs here. -/
theorem lemma2_square519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc (-(1 / R)) (1 / R)) ∧
          (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨C, hC, Np, hp⟩ := lemma2_positive_square519 B0 hB0
  refine ⟨2 * C, by positivity, max 1 Np, ?_⟩
  intro N hN R hR hRN M hM
  have hN1 : 1 ≤ N := by omega
  have hr0 : (0 : ℝ) ≤ 1 / R := by positivity
  obtain ⟨hiP, hbP⟩ := hp N (by omega) R hR hRN M hM
  have hMref := reflected_line_bound519 N B0 M hM.1 hM.2
  obtain ⟨hiQ, hbQ⟩ := hp N (by omega) R hR hRN
    (fun t => (starRingEnd ℂ) (M (-t))) hMref
  have hiN : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (-(1 / R)) 0) := by
    simpa only [Set.neg_Icc, neg_zero, mellin_reflection519 N hN1 M,
      Complex.norm_conj, neg_neg] using hiQ.comp_neg
  have hiPI := (intervalIntegrable_iff_integrableOn_Icc_of_le hr0).mpr hiP
  have hiNI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (neg_nonpos.mpr hr0)).mpr hiN
  have hiFull := hiNI.trans hiPI
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (show -(1 / R) ≤ 1 / R by linarith)).mp hiFull, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiNI hiPI,
    mellin_negative_square519 N hN1 M (1 / R)]
  calc _ ≤ C * ((N : ℝ) / R * Real.log N ^ 13) +
      C * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hbQ hbP
    _ = _ := by ring

/-- P0093 page 159 equation 5.2. The corrected Mellin transfer and the
abstract square estimate imply the nonprincipal character square estimate.
CONDITIONAL ON grh_mellin_transfer519 and lemma2_square519. -/
theorem nonprincipal_mass519 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
            (∫ α in -(1 / R)..(1 / R), ‖characterPrime519 χ N α‖ ^ 2) ≤
              C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := grh_mellin_transfer519 hG
  obtain ⟨C, hC, Nm, hm⟩ := lemma2_square519 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 4 * B ^ 2, by positivity, max 1 (max L (max Nt Nm)), ?_⟩
  intro N hN q hq hqN χ hχ R hR hRN
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hNt : Nt < N := by omega
  have hNm : Nm < N := by omega
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  obtain ⟨M, hM, hrem⟩ := ht N hNt q hq hqN χ hχ
  obtain ⟨hiM, hmass⟩ := hm N hNm R hR hRN M hM
  have hc := (continuous_character_prime519 χ N hN1).norm.pow 2
  have hle : ∀ α : ℝ, ‖characterPrime519 χ N α‖ ^ 2 ≤
      2 * ‖mellinU519 N M α‖ ^ 2 + 2 * B ^ 2 * N := by
    intro α
    have htri : ‖characterPrime519 χ N α‖ ≤
        ‖mellinU519 N M α‖ + B * Real.sqrt N := by
      have := norm_add_le (mellinU519 N M α)
        (characterPrime519 χ N α - mellinU519 N M α)
      have he : mellinU519 N M α +
          (characterPrime519 χ N α - mellinU519 N M α) = characterPrime519 χ N α := by ring
      rw [he] at this
      exact this.trans (add_le_add le_rfl (hrem α))
    nlinarith [sq_nonneg (‖mellinU519 N M α‖ - B * Real.sqrt N),
      Real.sq_sqrt hNp.le, norm_nonneg (characterPrime519 χ N α),
      norm_nonneg (mellinU519 N M α), Real.sqrt_nonneg (N : ℝ)]
  have hiMi : IntervalIntegrable (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      volume (-(1 / R)) (1 / R) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))).mpr
    exact hiM
  have hh := intervalIntegral.integral_mono_on (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))
    (hc.intervalIntegrable _ _)
    ((hiMi.const_mul 2).add (intervalIntegrable_const (a := -(1 / R)) (b := 1 / R)))
    (fun α _ => hle α)
  rw [intervalIntegral.integral_add (hiMi.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hh
  calc
    _ ≤ 2 * (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := hh
    _ ≤ 2 * (C * ((N : ℝ) / R * Real.log N ^ 13)) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := by gcongr
    _ ≤ (2 * C + 4 * B ^ 2) * ((N : ℝ) / R * Real.log N ^ 13) := by
      have he : (1 / R - -(1 / R)) * (2 * B ^ 2 * N) =
          4 * B ^ 2 * ((N : ℝ) / R) := by ring
      rw [he]
      have := mul_le_mul_of_nonneg_left hlog13
        (show 0 ≤ 4 * B ^ 2 * ((N : ℝ) / R) by positivity)
      nlinarith

/-- P0093 page 166 passage from equation 9.1 to 9.3. The logarithmic
totient ratio keeps the full q saving on the specified minor denominator range. -/
theorem principal_arithmetic519 (N q : ℕ) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hq : (N : ℝ) ^ (1 / 10 : ℝ) ≤ q) (hqN : (q : ℝ) ≤ N) :
    (N : ℝ) / q.totient ≤ 4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : 1 ≤ q := by
    exact_mod_cast (Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφp : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hratio : (q : ℝ) / q.totient ≤ 4 * Real.log N := by
    have ht := LeanLab.Perelli1996.TotientRatio320.ratio_le_log q (by omega)
    have hl := Real.log_le_log hqp hqN
    linarith
  have hdiv : (N : ℝ) / q ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) :=
        div_le_div_of_nonneg_left hNp.le (by positivity) hq
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
        rw [← Real.rpow_sub hNp]
        norm_num
  calc
    _ = ((N : ℝ) / q) * ((q : ℝ) / q.totient) := by field_simp
    _ ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (4 * Real.log N) :=
      mul_le_mul hdiv hratio (by positivity) (by positivity)
    _ = _ := by ring

/-- P0093 page 166 equation 9.1. The finite character expansion and the
nonprincipal square estimate give the system bound before power absorption.
CONDITIONAL ON grh_mellin_transfer519 and lemma2_square519. -/
theorem system_character_bound519 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < q →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem519 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111_up111 N α‖ ^ 2) ≤
            C * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := by
  classical
  obtain ⟨B, hB, hb⟩ := doubled_system_characters1622_split
  obtain ⟨X, hX, Nx, hx⟩ := nonprincipal_mass519 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  have hτev : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 7)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp hτev
  refine ⟨B * (10 + 2 * X), by positivity, max 1 (max L (max Nx Nt)), ?_⟩
  intro N hN q hq hqt
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hq1R : (1 : ℝ) < q :=
    (Real.one_le_rpow hNR (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans_lt hq
  have hq2 : 2 ≤ q := by exact_mod_cast hq1R
  have hqp : (0 : ℝ) < q := by linarith
  haveI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hτ : 4 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := ht N (by omega)
  have hτp : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hqN : (q : ℝ) ≤ N := hqt.trans (by
    calc (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
      _ = N := Real.rpow_one _)
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  let τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ)
  let R : ℝ := (q : ℝ) * τ / 2
  let r : ℝ := 2 / ((q : ℝ) * τ)
  have hR1 : 1 ≤ R := by dsimp [R, τ]; nlinarith
  have hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have hqq : (q : ℝ) * τ ≤ τ * τ := mul_le_mul_of_nonneg_right hqt hτp.le
    have he : τ * τ = (N : ℝ) ^ (2 / 7 : ℝ) := by
      dsimp [τ]; rw [← Real.rpow_add hNp]; norm_num
    dsimp [R]; rw [← he]; nlinarith [mul_nonneg hτp.le hτp.le]
  have hr0 : 0 ≤ r := by dsimp [r, τ]; positivity
  have hrh : r ≤ 1 / 2 := by
    dsimp [r, τ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hrR : 1 / R = r := by dsimp [R, r]; ring
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  have hsum : (∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2) ≤
      (q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
    have hi : ∀ χ ∈ F, (∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2) ≤
        X * ((N : ℝ) / R * Real.log N ^ 13) := by
      intro χ hχ
      have hh := hx N (by omega) q (by omega) hqt χ (Finset.mem_filter.mp hχ).2 R hR1 hRN
      simpa only [hrR] using hh
    have hc : (F.card : ℝ) ≤ q.totient := by
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
      have hfilter : F.card ≤ q.totient := by
        simpa only [F, Finset.card_univ, hcard] using
          Finset.card_filter_le (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
            (p := fun χ => χ ≠ 1)
      exact_mod_cast hfilter
    calc _ ≤ (F.card : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
          simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul F _ _ hi
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hprin := character_local_mass519 (1 : DirichletCharacter ℂ q) N hN1 r hr0 hrh
  have he : (N : ℝ) / τ ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc _ = (N : ℝ) ^ (6 / 7 : ℝ) := by
          dsimp [τ]; conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
          rw [← Real.rpow_sub hNp]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have hp := principal_arithmetic519 N q hN1 hlog hq.le hqN
  have hp13 : (N : ℝ) / q.totient ≤
      4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13 := by
    have hl : Real.log N ≤ Real.log N ^ 13 := by
      calc _ = Real.log N ^ 1 := by ring
        _ ≤ _ := pow_le_pow_right₀ hlog (by omega)
    exact hp.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have hcorr : (q.totient : ℝ) * r * Real.log q ^ 2 ≤
      2 * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := by
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hlq : Real.log q ^ 2 ≤ Real.log N ^ 13 := by
      have h0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
      have hl := Real.log_le_log hqp hqN
      exact (pow_le_pow_left₀ h0 hl 2).trans (pow_le_pow_right₀ hlog (by omega))
    have hrr : (q : ℝ) * r = 2 / τ := by dsimp [r]; field_simp
    calc _ ≤ (q : ℝ) * r * Real.log N ^ 13 := by gcongr
      _ = 2 / τ * Real.log N ^ 13 := by rw [hrr]
      _ ≤ 2 * ((N : ℝ) / τ) * Real.log N ^ 13 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [mul_div_assoc', div_le_div_iff₀ hτp hτp]
        nlinarith
      _ ≤ (2 * (N : ℝ) ^ (9 / 10 : ℝ)) * Real.log N ^ 13 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity)
      _ = _ := by ring
  have hmass := hb N q τ hN1 hq2 hτ
  have hm : (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1,
      ‖primeFourier111_up111 N α‖ ^ 2) ≤
      B / (q.totient : ℝ) * (2 * N + (q : ℝ) *
        ((q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)))) +
        B * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    exact hmass.trans (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hprin
        (mul_le_mul_of_nonneg_left hsum hqp.le)) (by positivity)) le_rfl)
  have hid : B / (q.totient : ℝ) * (2 * N + (q : ℝ) *
      ((q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)))) =
      2 * B * ((N : ℝ) / q.totient) +
        2 * B * X * ((N : ℝ) / τ * Real.log N ^ 13) := by
    dsimp [R]; field_simp [hφ.ne', hqp.ne', hτp.ne'] <;> ring
  rw [hid] at hm
  calc
    _ ≤ 2 * B * ((N : ℝ) / q.totient) +
        2 * B * X * ((N : ℝ) / τ * Real.log N ^ 13) +
        B * ((q.totient : ℝ) * r * Real.log q ^ 2) := by simpa only [mul_assoc] using hm
    _ ≤ 2 * B * (4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) +
        2 * B * X * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) +
        B * (2 * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13)) := by gcongr
    _ = _ := by ring

/-- P0093 page 166 equations 9.1 and 9.3. Logarithmic absorption of
the character system estimate on the minor denominator range.
CONDITIONAL ON grh_mellin_transfer519 and lemma2_square519. -/
theorem system_mass519 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem519 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111_up111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (93 / 100 : ℝ) := by
  obtain ⟨C, hC, Ns, hs⟩ := system_character_bound519 hG
  have hlo := (isLittleO_log_rpow_rpow_atTop (13 : ℝ)
    (by norm_num : (0 : ℝ) < 3 / 100)).def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hlo)
  refine ⟨C, hC, max 1 (max Ns Nl), ?_⟩
  intro N hN q hq hqt
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlN : Real.log N ^ 13 ≤ (N : ℝ) ^ (3 / 100 : ℝ) := by
    have hh := hl N (by omega)
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg (pow_nonneg hlog 13), abs_of_pos (Real.rpow_pos_of_pos hNp _)] using hh
  calc
    _ ≤ C * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := hs N (by omega) q hq hqt
    _ ≤ C * ((N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (3 / 100 : ℝ)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

/-- P0093 page 166 equations 9.1 and 9.3. The denominator range is
nonempty at arbitrarily large integral scales: N is k to seventy and q
is k to nine for any integer k at least two. -/
theorem denominator_range519 (k : ℕ) (hk : 2 ≤ k) :
    (((k ^ 70 : ℕ) : ℝ) ^ (1 / 10 : ℝ) < (k ^ 9 : ℕ)) ∧
      ((k ^ 9 : ℕ) : ℝ) ≤ ((k ^ 70 : ℕ) : ℝ) ^ (1 / 7 : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkl : (1 : ℝ) < k := by exact_mod_cast hk
  have he10 : (((k ^ 70 : ℕ) : ℝ) ^ (1 / 10 : ℝ)) = (k : ℝ) ^ (7 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hk0]
    norm_num
  have he7 : (((k ^ 70 : ℕ) : ℝ) ^ (1 / 7 : ℝ)) = (k : ℝ) ^ (10 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hk0]
    norm_num
  rw [he10, he7, Nat.cast_pow]
  exact ⟨pow_lt_pow_right₀ hkl (by omega), pow_le_pow_right₀ hkl.le (by omega)⟩

/-- P0093 page 166 passage from equation 9.1 to 9.3. Arithmetic audit
of the earlier square root totient route. A bound at exponent nineteen
twentieths cannot imply any fixed constant bound at ninety three hundredths.
This compares candidate bounds and asserts no failure of the paper. -/
theorem square_root_totient_loss519 (C : ℝ) : ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    C * (N : ℝ) ^ (93 / 100 : ℝ) < (N : ℝ) ^ (19 / 20 : ℝ) := by
  have he : ∀ᶠ N : ℕ in atTop, C < (N : ℝ) ^ (1 / 50 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp he
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hC := hN0 N (by omega)
  calc _ < (N : ℝ) ^ (1 / 50 : ℝ) * (N : ℝ) ^ (93 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hNp _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

/-- P0093 page 159 equation 5.2. The nonprincipal character domain
has a concrete inhabitant modulo three. This instance assumes no GRH. -/
theorem nonprincipal_mod_three519 : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  have hc : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3]
    rw [Nat.totient_prime Nat.prime_three]
  exact Fintype.exists_ne_of_one_lt_card (by omega) 1

/-- P0093 page 166 definition of the doubled system. A concrete membership. -/
example : (1 / 2 : ℝ) ∈ arcSystem519 2 4 := by
  refine ⟨(1 / 2 : ℚ), by norm_num, ?_⟩
  norm_num

/-! Axiom audit for every public and private theorem in this port. -/
#print axioms continuous_character_prime519
#print axioms series_square_integral519
#print axioms character_coefficients_summable519
#print axioms character_series_nat519
#print axioms character_full_mass519
#print axioms character_periodic519
#print axioms character_local_mass519
#print axioms card_reduced1622
#print axioms rational_cover519
#print axioms rational_cover_integral519
#print axioms exp_phase_nat
#print axioms full_sum_nat
#print axioms multiples_sum_nat
#print axioms coprime_indicator_nat
#print axioms ramanujan_sum_one_nat
#print axioms unit_sum_addChar_le_one
#print axioms unit_gauss_principal_le
#print axioms two_pow_primeFactors_card_le
#print axioms primeFactors_card_le_log
#print axioms corr_bound
#print axioms sum_Gunit_mul_char
#print axioms Gunit_eq_mul
#print axioms sum_unit_char_of_ne_one
#print axioms sum_unit_char_mul_inv
#print axioms sum_Gunit_orth
#print axioms Gunit_one_principal_le
#print axioms Gunit_one_norm_sq_le
#print axioms char_expansion_pointwise
#print axioms exp_split_phase
#print axioms prime_fourier_expansion
#print axioms sum_normSq_chi_combo
#print axioms card_reduced_aux1622
#print axioms pointwise_assembly
#print axioms rational_pointwise_characters519
#print axioms doubled_system_characters1622_split
#print axioms line_coefficient_one519
#print axioms grh_mellin_transfer519
#print axioms lemma2_square519
#print axioms nonprincipal_mass519
#print axioms principal_arithmetic519
#print axioms system_character_bound519
#print axioms system_mass519

#print axioms denominator_range519

#print axioms square_root_totient_loss519

#print axioms nonprincipal_mod_three519

#print axioms mellin_reflection519

#print axioms reflected_line_bound519

#print axioms mellin_negative_square519

#print axioms mellin_kernel_domination519
#print axioms sqrt_scale519
#print axioms gamma_absolute_decay519
#print axioms gamma_mellin_line519
#print axioms pi_gap519
#print axioms arg_base_bound519
#print axioms mellin_base_bound519
#print axioms log_cube_split519
#print axioms integrable_exp_neg_abs519
#print axioms shift_pow_five_le_exp519
#print axioms integrable_majorant519
#print axioms continuous_mellinLine519
#print axioms gamma_line_uniform519
#print axioms gamma_twist_pointwise519
#print axioms continuous_gamma_mellin519
#print axioms gamma_twist_mass519
#print axioms kernel_mass_integrable519
#print axioms mass_constant519
#print axioms central_kernel_mass519
#print axioms continuous_mellin_integrand519
#print axioms stronglyMeasurable_mellinU519

#print axioms central_mellin_bound519

#print axioms central_square_mass519

#print axioms lemma2_outer_square519
#print axioms lemma2_positive_square519

end LeanLab.Linnik1951.Task519
