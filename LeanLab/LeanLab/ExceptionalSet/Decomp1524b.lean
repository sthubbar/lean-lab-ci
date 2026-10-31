/-
CODEX task85 status: nine original leaves now have proofs. Only gallagher_lemma remains open. The major arc approximation is conditional on its explicit progression discrepancy hypothesis.
AI wrote the Lean code. Binary Goldbach is open.
-/
/-
P0015 Montgomery and Vaughan 1975, The exceptional set in Goldbach's problem, Acta Arith. 27,
353-370. Unit U-1524, run 20261025T2003Z-426, ARCHITECT DECOMPOSE.

File b of three: the major arc approximation of `S(α) = Σ_{n ≤ N} Λ(n) e(nα)` near `a/q`,
split into LEAF lemmas. In the paper this is the passage from `S(a/q + η)` to
`μ(q)/φ(q) T(η)` plus character sums `Σ_χ τ(χ̄) χ(a) Σ χ(n)Λ(n) e(nη)`, sections 4 to 7 and
(8.1) to (8.3); the mean square of the error over an arc is controlled by Gallagher's lemma.

SOURCE: the impan.pl scan could not be fetched in this unit (WebFetch CLIENT_ERROR). The leaves
follow the standard argument: Davenport, Mult. Number Theory, Ch. 26 (major arcs, Ramanujan
sums) and Ch. 9 (Gauss sums); Montgomery-Vaughan, MNT I, Sections 4.1 (Ramanujan sums), 9.2, 9.3 (Gauss sums of
imprimitive characters); Montgomery, Topics, LNM 227, Lemma 1.9 (Gallagher's lemma);
P. X. Gallagher, A large sieve density estimate near σ = 1, Invent. Math. 11 (1970), Lemma 1.

Leaves (sorry): `S_split_residue`, `nonCoprime_vonMangoldt_le`, `abel_bound`,
`ramanujan_coprime`, `ramanujan_norm_le_gcd`, `geom_sum_le`, `gallagher_lemma`,
`char_expansion`, `tau_norm_le`, `major_arc_approx`.

AI-written Lean code, Claude, unit U-1524. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.Decomp1524a
import LeanLab.PNTPort.Vinogradov.MajorArc
import LeanLab.Xi2012.Ramanujan
import LeanLab.HardyLittlewood1923.CharacterExpansion

namespace LeanLab.ExceptionalSet.Decomp1524b

open Real MeasureTheory Finset ArithmeticFunction
open ZMod Complex ComplexConjugate
open LeanLab.ExceptionalSet.Decomp1524a

attribute [local instance] Classical.propDecidable

/-- `S_N(α) = Σ_{n=1}^{N} Λ(n) e(nα)`. -/
noncomputable def S (N : ℕ) (α : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * e (n * α)

/-- `T_N(η) = Σ_{n=1}^{N} e(nη)`. -/
noncomputable def T (N : ℕ) (η : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, e (n * η)

/-- `ψ(N; q, b) = Σ_{n ≤ N, n ≡ b mod q} Λ(n)`, with `b` the least residue. -/
noncomputable def psiAP (N q b : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = b), ArithmeticFunction.vonMangoldt n

/-- LEAF. Splitting by residues: for `q ≥ 1` and `a ∈ ℤ`,
`S_N(a/q + η) = Σ_{b=0}^{q-1} e(ab/q) Σ_{n ≤ N, n ≡ b (q)} Λ(n) e(nη)`, since `e(an/q)` depends
only on `n mod q`. Davenport, Mult. Number Theory, Ch. 26; Montgomery-Vaughan 1975 section 4.
Unit U-1524. -/
theorem S_split_residue {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (N : ℕ) (η : ℝ) :
    S N ((a : ℝ) / q + η) = ∑ b ∈ Finset.range q, e ((a : ℝ) * b / q) *
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = b), (ArithmeticFunction.vonMangoldt n : ℂ) * e (n * η) := by
  have hq0 : 0 < q := by omega
  have hqR : (0:ℝ) < q := by exact_mod_cast hq0
  have he (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  unfold S
  simp_rw [he, mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => n%q)
    (fun n (hn : n ∈ Icc 1 N) => mem_range.mpr (Nat.mod_lt n hq0))]
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro n hn
  have hnb := (mem_filter.mp hn).2
  have hnum : (n:ℝ) = b + q * (n/q:ℕ) := by
    have hh := Nat.mod_add_div n q
    rw [hnb] at hh
    exact_mod_cast hh.symm
  have harg : (n:ℝ)*((a:ℝ)/q+η) = ((a:ℝ)*b/q+n*η)+(a*(n/q:ℕ):ℤ) := by
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hnum]
    field_simp [hqR.ne']
    ring
  rw [harg, LeanLab.PNTPort.LargeSieve.e_add, LeanLab.PNTPort.LargeSieve.e_int, mul_one,
    LeanLab.PNTPort.LargeSieve.e_add]
  ring

/-- LEAF. Prime powers sharing a factor with `q ≥ 1`:
`Σ_{n ≤ N, (n,q) > 1} Λ(n) ≤ ω(q) log N`, since for each `p | q` the sum over `p^k ≤ N` of
`log p` is at most `log N`. Davenport, Mult. Number Theory, Ch. 26. Unit U-1524. -/
theorem nonCoprime_vonMangoldt_le {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      (q.primeFactors.card : ℝ) * Real.log N := by
  by_cases hN : N = 0
  · subst N; simp
  have hN1 : 1 ≤ N := by omega
  set D := ∏ p ∈ q.primeFactors, p ^ (Nat.log p N) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  -- step 1: psiBad ≤ log D
  have step1 : (∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) ≤ Real.log D := by
    rw [← vonMangoldt_sum, ← Finset.sum_filter_ne_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hcop⟩, hΛ⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
      have hpq : p ∣ q := by
        by_contra h
        exact hcop (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))
      have hpm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
      have hkl : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hnN
      rw [Nat.mem_divisors]
      exact ⟨(pow_dvd_pow p hkl).trans (Finset.dvd_prod_of_mem _ hpm), hD0⟩
    · intro _ _ _; exact vonMangoldt_nonneg
  -- step 2: log D ≤ #pf * log N
  have step2 : Real.log D ≤ q.primeFactors.card * Real.log N := by
    rw [hD, Nat.cast_prod, Real.log_prod]
    · rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      apply Real.log_le_log
      · have := hp'.pos; positivity
      · exact_mod_cast Nat.pow_log_le_self p (by omega)
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have := hp'.pos
      positivity
  exact step1.trans step2

/-- LEAF. Partial summation: if every partial sum `|Σ_{n ≤ m} c_n| ≤ B` for `m ≤ N`, then
`|Σ_{n ≤ N} c_n e(nη)| ≤ (1 + 2π|η|N) B`, using `|e((n+1)η) - e(nη)| ≤ 2π|η|`.
Davenport, Mult. Number Theory, Ch. 26 (Abel summation).
Unit U-1524. -/
theorem abel_bound (c : ℕ → ℂ) (N : ℕ) (η B : ℝ)
    (h : ∀ m ≤ N, ‖∑ n ∈ Finset.Icc 1 m, c n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * η)‖ ≤ (1 + 2 * π * |η| * N) * B := by
  have he (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hh := LeanLab.PNTPort.Vinogradov.abel_e c N η h
  simpa only [mul_comm B] using hh

/-- LEAF. Ramanujan's sum at a unit: for `q ≥ 1` and `(a, q) = 1`,
`Σ_{b mod q, (b,q)=1} e(ab/q) = μ(q)`. Montgomery-Vaughan, MNT I, Theorem 4.1;
Davenport, Mult. Number Theory, Ch. 26. Unit U-1524. -/
theorem ramanujan_coprime {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (ha : Int.gcd a q = 1) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((a : ℝ) * b / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have he (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact LeanLab.PNTPort.Vinogradov.ramanujan_coprime hq (Int.isCoprime_iff_gcd_eq_one.mpr ha)

/-- LEAF. Size of a Ramanujan sum: for `q ≥ 1` and `n ∈ ℤ`,
`|c_q(n)| = |Σ_{(b,q)=1} e(bn/q)| ≤ (n, q)`, from `c_q(n) = μ(q/g) φ(q)/φ(q/g)`, `g = (n,q)`.
Montgomery-Vaughan, MNT I, Theorem 4.1; used for the singular series,
Montgomery-Vaughan 1975 section 6. Unit U-1524. -/
theorem ramanujan_norm_le_gcd {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ‖∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((b : ℝ) * n / q)‖ ≤
      (Int.gcd n q : ℝ) := by
  have hnat (k : ℕ) : ‖∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((b : ℝ) * k / q)‖ ≤
      (Nat.gcd k q : ℝ) := by
    have heq : (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((b : ℝ) * k / q)) =
        LeanLab.Xi2012.NatEncoding.ramanujanSum q k := by
      unfold LeanLab.Xi2012.NatEncoding.ramanujanSum
      apply sum_congr rfl
      intro b hb
      unfold e LeanLab.Xi2012.NatEncoding.fourierPhase
      congr 1
      push_cast
      ring
    rw [heq]
    exact LeanLab.Xi2012.NatEncoding.norm_ramanujanSum_le_gcd hq k
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simpa using hnat n
  · let k := (-n).toNat
    have hk : (k:ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hn' : n = -(k:ℤ) := by omega
    rw [hn', Int.gcd_comm, Int.gcd_neg, Int.gcd_comm, Int.gcd_natCast_natCast]
    have hconj (u : ℝ) : conj (e u) = e (-u) := by
      unfold e
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_ofReal, map_ofNat]
    have hs : (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((b : ℝ) * (-(k:ℤ):ℤ) / q)) =
        conj (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), e ((b : ℝ) * k / q)) := by
      rw [map_sum]
      apply sum_congr rfl
      intro b hb
      rw [hconj]
      congr 1
      push_cast
      ring
    rw [hs, Complex.norm_conj]
    exact hnat k

/-- LEAF. The geometric sum: for `0 < |η| ≤ 1/2`, `|T_N(η)| = |Σ_{n ≤ N} e(nη)| ≤ 1/(2|η|)`,
from `|T| ≤ 1/|sin πη|` and `sin πη ≥ 2|η|`. Davenport, Mult. Number Theory, Ch. 25, (3).
Unit U-1524. -/
theorem geom_sum_le (N : ℕ) {η : ℝ} (hη0 : 0 < |η|) (hη : |η| ≤ 1 / 2) :
    ‖T N η‖ ≤ 1 / (2 * |η|) := by
  have he (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hd : LeanLab.PNTPort.LargeSieve.dist0 η = |η| := by
    have hb := abs_le.mp hη
    by_cases hh : η < 1/2
    · have hr : round η = 0 := round_eq_zero_iff.mpr ⟨hb.1, hh⟩
      simp [LeanLab.PNTPort.LargeSieve.dist0, hr]
    · have hh' : η = 1/2 := by linarith
      rw [hh']
      norm_num [LeanLab.PNTPort.LargeSieve.dist0, round_eq_iff]
  have hs : (∑ n ∈ Icc 1 N, LeanLab.PNTPort.LargeSieve.e ((n:ℝ)*η)) =
      LeanLab.PNTPort.LargeSieve.e η * ∑ k ∈ range N, LeanLab.PNTPort.LargeSieve.e ((k:ℝ)*η) := by
    rw [mul_sum]
    refine sum_nbij' (fun n : ℕ => n-1) (fun k => k+1) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [mem_Icc] at hn; apply mem_range.mpr; omega
    · intro k hk; simp only [mem_range] at hk; apply mem_Icc.mpr; omega
    · intro n hn; have hh := mem_Icc.mp hn; omega
    · intro k hk; omega
    · intro n hn
      rw [← LeanLab.PNTPort.LargeSieve.e_add]
      congr 1
      rw [Nat.cast_sub (Finset.mem_Icc.mp hn).1]
      push_cast
      ring
  unfold T
  simp_rw [he]
  rw [hs, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
  have hh := LeanLab.PNTPort.LargeSieve.norm_geom_le (θ := η) N (by rw [hd]; exact hη0)
  rw [hd] at hh
  exact hh

/-- LEAF. Gallagher's lemma: for a finite `s ⊆ ℤ` and `T > 0`,
`∫_{-T}^{T} |Σ_{n ∈ s} a_n e(nt)|² dt ≤ π² T² ∫_ℝ |Σ_{n ∈ s, x < n ≤ x + 1/(2T)} a_n|² dx`.
Proof: Plancherel for the step function `C(x)`, whose transform is `S(-t) sin(πt/2T)/(πt)` up
to a unimodular factor, and `sin u ≥ 2u/π` on `[0, π/2]`. Gallagher 1970 Lemma 1;
Montgomery, Topics, Lemma 1.9. Unit U-1524. -/
theorem gallagher_lemma (s : Finset ℤ) (a : ℤ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖trig s a t‖ ^ 2 ≤
      π ^ 2 * T ^ 2 * ∫ x : ℝ, ‖∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)),
        a n‖ ^ 2 := by
  sorry

/-- LEAF. Expansion of `e(an/q)` into characters: for `q ≥ 1`, `(a,q) = (n,q) = 1`,
`e(an/q) = φ(q)⁻¹ Σ_{χ mod q} χ(a) χ(n) τ(χ̄)`. Davenport, Mult. Number Theory, Ch. 9, (1)-(2);
Montgomery-Vaughan 1975 section 4. Unit U-1524. -/
theorem char_expansion {q : ℕ} (hq : 1 ≤ q) (a n : ℤ) (ha : Int.gcd a q = 1)
    (hn : Int.gcd n q = 1) :
    e ((a : ℝ) * n / q) = ((Nat.totient q : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * χ (n : ZMod q) * tau χ⁻¹ := by
  letI : NeZero q := ⟨by omega⟩
  let z : ZMod q := (a:ZMod q)*(n:ZMod q)
  have haU : IsUnit (a:ZMod q) := (ZMod.coe_int_isUnit_iff_isCoprime a q).2 (Int.isCoprime_iff_gcd_eq_one.mpr ha).symm
  have hnU : IsUnit (n:ZMod q) := (ZMod.coe_int_isUnit_iff_isCoprime n q).2 (Int.isCoprime_iff_gcd_eq_one.mpr hn).symm
  have hzU : IsUnit z := haU.mul hnU
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega)).ne'
  have ht (χ : DirichletCharacter ℂ q) : tau χ = gaussSum χ stdAddChar := by
    have hh := gaussSum_mulShift_eq_sum χ 1
    simpa [tau] using hh.symm
  have hi (χ : DirichletCharacter ℂ q) : χ⁻¹ z = χ z⁻¹ := by
    simpa only [MulChar.star_apply'] using LeanLab.RieselVaughan1983.GaussImprim.star_apply_unit χ hzU
  have hinv := Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q))
    (fun χ => χ⁻¹ z * gaussSum χ stdAddChar)
    (fun χ => χ z * gaussSum χ⁻¹ stdAddChar) (fun χ => by simp)
  have hsum : (∑ χ : DirichletCharacter ℂ q, χ (a:ZMod q)*χ (n:ZMod q)*tau χ⁻¹) =
      (q.totient:ℂ)*stdAddChar z := by
    calc _ = ∑ χ : DirichletCharacter ℂ q, χ z * gaussSum χ⁻¹ stdAddChar := by
          simp_rw [ht, ← map_mul]; rfl
      _ = ∑ χ : DirichletCharacter ℂ q, χ⁻¹ z * gaussSum χ stdAddChar := hinv.symm
      _ = ∑ χ : DirichletCharacter ℂ q, χ z⁻¹ * gaussSum χ stdAddChar := by simp_rw [hi]
      _ = _ := LeanLab.HardyLittlewood1923.Task52.additive_character_expansion stdAddChar hzU
  have he : stdAddChar z = e ((a:ℝ)*n/q) := by
    have hz : z = ((a*n:ℤ):ZMod q) := by dsimp [z]; push_cast; rfl
    rw [hz, stdAddChar_coe]
    unfold e
    congr 1
    push_cast
    ring
  rw [hsum, he]
  field_simp

/-- LEAF. Every character mod `q ≥ 1`, primitive or not, has `|τ(χ)| ≤ √q`: for `χ` induced by
the primitive `χ*` mod `q*`, `τ(χ) = μ(q/q*) χ*(q/q*) τ(χ*)`. Montgomery-Vaughan, MNT I,
Theorem 9.10; Davenport, Mult. Number Theory, Ch. 9. Unit U-1524. -/
theorem tau_norm_le {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    ‖tau χ‖ ≤ Real.sqrt q := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hb := LeanLab.ExceptionalSet.Lu2010GaussBound.induced_gauss_norm_sq_le
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive χ.conductor_dvd_level
  rw [χ.changeLevel_primitiveCharacter] at hb
  have hc : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (show 0 < q by omega) χ.conductor_dvd_level
  have ht : tau χ = gaussSum χ stdAddChar := by
    have hh := gaussSum_mulShift_eq_sum χ 1
    simpa [tau] using hh.symm
  rw [ht]
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg (q : ℝ), norm_nonneg (gaussSum χ stdAddChar)]

/-- LEAF. Major arc approximation: for `q ≥ 1`, `(a,q) = 1`, if
`|ψ(m; q, b) - m/φ(q)| ≤ Δ` for every reduced residue `b` and every `m ≤ N`, then
`|S_N(a/q + η) - μ(q)/φ(q) T_N(η)| ≤ φ(q)(1 + 2π|η|N) Δ + ω(q) log N`.
Proof: `S_split_residue`, `ramanujan_coprime` for the main term, `abel_bound` with
`c_n = Λ(n) 1_{n ≡ b} - 1/φ(q)`, and `nonCoprime_vonMangoldt_le` for the residues with
`(b,q) > 1`. Montgomery-Vaughan 1975 sections 4 and 8, (8.1); Davenport, Mult. Number Theory,
Ch. 26. Unit U-1524. -/
theorem major_arc_approx {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (ha : Int.gcd a q = 1) (N : ℕ)
    (η Δ : ℝ)
    (hΔ : ∀ b ∈ Finset.range q, Nat.Coprime b q → ∀ m ≤ N,
      |psiAP m q b - (m : ℝ) / Nat.totient q| ≤ Δ) :
    ‖S N ((a : ℝ) / q + η) - (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)) * T N η‖ ≤
      Nat.totient q * (1 + 2 * π * |η| * N) * Δ + (q.primeFactors.card : ℝ) * Real.log N := by
  classical
  let C := (range q).filter (fun b => Nat.Coprime b q)
  let B := (range q).filter (fun b => ¬ Nat.Coprime b q)
  let f : ℕ → ℕ → ℂ := fun b n => if n%q=b then (ArithmeticFunction.vonMangoldt n:ℂ) else 0
  let R : ℕ → ℂ := fun b => ∑ n ∈ Icc 1 N, (f b n - (q.totient:ℂ)⁻¹)*e (n*η)
  let W : ℕ → ℂ := fun b => ∑ n ∈ (Icc 1 N).filter (fun n => n%q=b), (ArithmeticFunction.vonMangoldt n:ℂ)*e (n*η)
  let phase : ℕ → ℂ := fun b => e ((a:ℝ)*b/q)
  let H := 1 + 2*π*|η| * N
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega)).ne'
  have hR (b : ℕ) (hb : b ∈ C) : ‖R b‖ ≤ H*Δ := by
    have hpart : ∀ m ≤ N, ‖∑ n ∈ Icc 1 m, (f b n - (q.totient:ℂ)⁻¹)‖ ≤ Δ := by
      intro m hm
      have hd := hΔ b (mem_filter.mp hb).1 (mem_filter.mp hb).2 m hm
      have hs : (∑ n ∈ Icc 1 m, f b n) = (psiAP m q b : ℂ) := by
        dsimp [f, psiAP]
        rw [Complex.ofReal_sum, sum_filter]
      rw [sum_sub_distrib, hs, sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_one]
      change ‖(psiAP m q b:ℂ)-(m:ℂ)/(q.totient:ℂ)‖ ≤ Δ
      have heq : (psiAP m q b:ℂ)-(m:ℂ)/(q.totient:ℂ) =
          ((psiAP m q b - (m:ℝ)/(q.totient:ℝ) : ℝ):ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact hd
    have hh := abel_bound (fun n => f b n - (q.totient:ℂ)⁻¹) N η Δ hpart
    exact hh
  have hRW (b : ℕ) : R b = W b - (q.totient:ℂ)⁻¹ * T N η := by
    dsimp [R,W,T]
    simp_rw [sub_mul]
    rw [sum_sub_distrib, ← mul_sum]
    congr 1
    dsimp [f]
    simp only [ite_mul, zero_mul]
    rw [sum_filter]
  have hsplit : S N ((a:ℝ)/q+η) - (((ArithmeticFunction.moebius q:ℤ):ℂ)/(q.totient:ℂ))*T N η =
      (∑ b ∈ C, phase b * R b) + ∑ b ∈ B, phase b * W b := by
    rw [S_split_residue hq a N η]
    change (∑ b ∈ range q, phase b * W b) - _ = _
    have hc : (∑ b ∈ C, phase b) = ((ArithmeticFunction.moebius q:ℤ):ℂ) := ramanujan_coprime hq a ha
    have hfib := sum_filter_add_sum_filter_not (s := range q) (p := fun b => Nat.Coprime b q) (f := fun b => phase b * W b)
    change (∑ b ∈ C, phase b * W b) + (∑ b ∈ B, phase b * W b) = _ at hfib
    rw [← hfib]
    simp_rw [hRW, mul_sub]
    rw [sum_sub_distrib]
    have hconst : (∑ b ∈ C, phase b * ((q.totient:ℂ)⁻¹ * T N η)) =
        ((ArithmeticFunction.moebius q:ℤ):ℂ)/(q.totient:ℂ)*T N η := by
      rw [← sum_mul, hc]
      ring
    rw [hconst]
    ring
  have hGood : ‖∑ b ∈ C, phase b * R b‖ ≤ (q.totient:ℝ)*H*Δ := by
    refine (norm_sum_le _ _).trans ?_
    have hcard : C.card = q.totient := by simpa [C, Nat.totient_eq_card_coprime, Nat.coprime_comm]
    calc ∑ b ∈ C, ‖phase b * R b‖ ≤ ∑ _b ∈ C, H*Δ := by
          apply sum_le_sum
          intro b hb
          rw [norm_mul, show ‖phase b‖=1 from norm_e _, one_mul]
          exact hR b hb
      _ = _ := by rw [sum_const,nsmul_eq_mul,hcard]; ring
  have hBad : ‖∑ b ∈ B, phase b * W b‖ ≤ (q.primeFactors.card:ℝ)*Real.log N := by
    have hW (b : ℕ) : ‖W b‖ ≤ psiAP N q b := by
      refine (norm_sum_le _ _).trans ?_
      apply le_of_eq
      dsimp [W,psiAP]
      apply sum_congr rfl
      intro n hn
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hb : ∑ b ∈ B, psiAP N q b =
        ∑ n ∈ (Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n := by
      have heq : ∑ b ∈ B, psiAP N q b = ∑ b ∈ B, LeanLab.HeathBrown1985.psi (N:ℝ) q b := by
        apply sum_congr rfl
        intro b hb
        have hbq := mem_range.mp (mem_filter.mp hb).1
        simp [psiAP, LeanLab.HeathBrown1985.psi, Nat.mod_eq_of_lt hbq]
      rw [heq]
      simpa [B, LeanLab.PNTPort.BV.psiBad] using LeanLab.PNTPort.Vinogradov.sum_psi_bad q hq N
    calc ‖∑ b ∈ B, phase b * W b‖ ≤ ∑ b ∈ B, ‖phase b * W b‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ B, psiAP N q b := by
          apply sum_le_sum
          intro b hb
          rw [norm_mul, show ‖phase b‖=1 from norm_e _, one_mul]
          exact hW b
      _ ≤ _ := by rw [hb]; exact nonCoprime_vonMangoldt_le hq N
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hGood hBad)

/-! ### Vacuity instances -/

/-- The hypothesis of `major_arc_approx` holds at `q = 1`, `N = 0` with `Δ = 0`. -/
example : ∀ b ∈ Finset.range 1, Nat.Coprime b 1 → ∀ m ≤ (0 : ℕ),
    |psiAP m 1 b - (m : ℝ) / Nat.totient 1| ≤ 0 := by
  intro b _ _ m hm
  obtain rfl : m = 0 := by omega
  simp [psiAP]

/-- `ramanujan_coprime` has a nonempty range of hypotheses: `gcd(1, q) = 1`. -/
example (q : ℕ) : Int.gcd 1 q = 1 := by simp

end LeanLab.ExceptionalSet.Decomp1524b
