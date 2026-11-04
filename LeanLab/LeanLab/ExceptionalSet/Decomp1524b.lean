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

open scoped FourierTransform RealInnerProductSpace ENNReal
/-! ### Self-adjointness of the Fourier integral on `ℝ` -/

/-- `∫ 𝓕f · conj g = ∫ f · conj (𝓕⁻ g)` for integrable `f`, `g`: the Fourier integral is
self-adjoint.  A direct instantiation of `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`. -/
theorem fourier_sesq_swap (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, inner ℂ (𝓕 f ξ) (g ξ) = ∫ x, inner ℂ (f x) (𝓕⁻ g x) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (V := ℝ) (W := ℝ) (f := f) (g := g) (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ ℝ) (innerSL ℂ) continuous_fourierChar
    continuous_inner hf hg
  rw [show (-(innerₗ ℝ).flip : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) = -innerₗ ℝ from by ext x; simp] at h
  exact h

/-! ### Inner products of `Lp` classes -/

/-- The inner product of two `Lp` classes is the integral of the inner products of their
representatives. -/
theorem lp_inner_toLp {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℂ (f x) (g x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  rw [h1, h2]

/-- Plancherel's identity in inner-product form, with a Schwartz test function: for integrable
`f` and a Schwartz `φ`, `∫ ⟪𝓕f, 𝓕φ⟫ = ∫ ⟪f, φ⟫`. -/
theorem schwartz_sesq (f : ℝ → ℂ) (hf : Integrable f) (φ : SchwartzMap ℝ ℂ) :
    ∫ ξ, inner ℂ (𝓕 f ξ) (((𝓕 φ : SchwartzMap ℝ ℂ)) ξ) =
      ∫ x, inner ℂ (f x) (φ x) := by
  have hinv : (𝓕⁻ (((𝓕 φ : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) = ⇑φ := by
    rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
  have h := fourier_sesq_swap f (((𝓕 φ : SchwartzMap ℝ ℂ)) : ℝ → ℂ) hf
    ((𝓕 φ : SchwartzMap ℝ ℂ).integrable)
  rwa [hinv] at h

/-- The L² form of `schwartz_sesq`. -/
theorem schwartz_lp_inner (f : ℝ → ℂ) (hf : Integrable f) (hF : MemLp (𝓕 f) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    inner ℂ (hF.toLp (𝓕 f)) ((𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume) =
      ∫ x, inner ℂ (f x) (φ x) := by
  rw [show (𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume
      = ((𝓕 φ : SchwartzMap ℝ ℂ).memLp 2 volume).toLp (((𝓕 φ : SchwartzMap ℝ ℂ)) : ℝ → ℂ)
      from rfl]
  rw [lp_inner_toLp hF ((𝓕 φ : SchwartzMap ℝ ℂ).memLp 2 volume)]
  exact schwartz_sesq f hf φ

/-! ### Density of the Schwartz Fourier classes in `L²` -/

/-- The images of the Schwartz classes under the L² Fourier transform are dense. -/
theorem denseRange_schwartz_fourier :
    DenseRange (fun φ : SchwartzMap ℝ ℂ => (𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume) := by
  have hd : DenseRange (fun φ : SchwartzMap ℝ ℂ => φ.toLp (2 : ℝ≥0∞) volume) :=
    SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
  intro h
  have hcl : 𝓕⁻ h ∈ closure (Set.range (fun φ : SchwartzMap ℝ ℂ => φ.toLp (2 : ℝ≥0∞) volume)) :=
    hd _
  have h1 : h ∈ (𝓕 : Lp ℂ 2 volume → Lp ℂ 2 volume) ''
      closure (Set.range (fun φ : SchwartzMap ℝ ℂ => φ.toLp (2 : ℝ≥0∞) volume)) :=
    ⟨𝓕⁻ h, hcl, by simp⟩
  refine closure_mono ?_
    (image_closure_subset_closure_image (s := Set.range (fun φ : SchwartzMap ℝ ℂ =>
      φ.toLp (2 : ℝ≥0∞) volume))
      (f := (𝓕 : Lp ℂ 2 volume → Lp ℂ 2 volume)) FourierTransform.continuous_fourier h1)
  rintro a ⟨F, hF, rfl⟩
  obtain ⟨ψ, rfl⟩ := hF
  exact ⟨ψ, (SchwartzMap.toLp_fourier_eq ψ).symm⟩

/-! ### From the dense family to a norm bound -/

/-- A bound on the inner products against the Schwartz Fourier classes bounds the norm. -/
theorem norm_le_of_schwartz_fourier (x : Lp ℂ 2 volume) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ φ : SchwartzMap ℝ ℂ,
      ‖inner ℂ x ((𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume)‖ ≤
        C * ‖(𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume‖) :
    ‖x‖ ≤ C := by
  classical
  have hclosed : IsClosed {y : Lp ℂ 2 volume | ‖inner ℂ x y‖ ≤ C * ‖y‖} :=
    isClosed_le ((continuous_const.inner continuous_id).norm) (continuous_const.mul continuous_norm)
  have hsub : Set.range (fun φ : SchwartzMap ℝ ℂ =>
      (𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume) ⊆
      {y : Lp ℂ 2 volume | ‖inner ℂ x y‖ ≤ C * ‖y‖} := by
    rintro _ ⟨φ, rfl⟩
    exact h φ
  have huniv : (Set.univ : Set (Lp ℂ 2 volume)) ⊆
      {y : Lp ℂ 2 volume | ‖inner ℂ x y‖ ≤ C * ‖y‖} := by
    intro y _
    exact closure_minimal hsub hclosed (denseRange_schwartz_fourier y)
  have hall : ∀ y : Lp ℂ 2 volume, ‖inner ℂ x y‖ ≤ C * ‖y‖ :=
    fun y => huniv (Set.mem_univ y)
  have hxx := hall x
  have hsq : ‖inner ℂ x x‖ = ‖x‖ ^ 2 := by
    rw [← inner_self_re_eq_norm]
    exact (norm_sq_eq_re_inner x).symm
  rw [hsq] at hxx
  have hxx2 : ‖x‖ ^ 2 ≤ C * ‖x‖ := hxx
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
  · rw [← h0]; exact hC
  · refine le_of_mul_le_mul_right ?_ h0
    rwa [sq] at hxx2


/-- `‖f.toLp 2‖² = ∫ ‖f‖²`. -/
theorem norm_toLp_sq (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have key : inner ℂ (hf.toLp f) (hf.toLp f) = ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [lp_inner_toLp hf hf]
    have hpt : ∀ x : ℝ, inner ℂ (f x) (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    simp only [hpt]
    exact integral_ofReal
  have h := congrArg RCLike.re key
  rw [← norm_sq_eq_re_inner] at h
  simpa using h

/-- Plancherel's inequality for integrable `f` with `𝓕 f ∈ L²`. -/
theorem integral_norm_sq_fourier_le (f : ℝ → ℂ) (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hF : MemLp (𝓕 f) 2 volume) :
    ∫ x, ‖𝓕 f x‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
  have hbound : ‖hF.toLp (𝓕 f)‖ ≤ ‖hf2.toLp f‖ := by
    refine norm_le_of_schwartz_fourier _ _ (norm_nonneg _) ?_
    intro φ
    have h1 : inner ℂ (hF.toLp (𝓕 f)) ((𝓕 φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume)
        = ∫ x, inner ℂ (f x) (φ x) := schwartz_lp_inner f hf hF φ
    have h2 : inner ℂ (hf2.toLp f) ((φ : SchwartzMap ℝ ℂ).toLp (2 : ℝ≥0∞) volume)
        = ∫ x, inner ℂ (f x) (φ x) := lp_inner_toLp hf2 (φ.memLp 2 volume)
    rw [h1, ← h2]
    refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
    rw [SchwartzMap.norm_fourier_toL2_eq]
  calc ∫ x, ‖𝓕 f x‖ ^ 2 = ‖hF.toLp (𝓕 f)‖ ^ 2 := (norm_toLp_sq _ hF).symm
    _ ≤ ‖hf2.toLp f‖ ^ 2 := by nlinarith [hbound, norm_nonneg (hF.toLp (𝓕 f))]
    _ = ∫ x, ‖f x‖ ^ 2 := norm_toLp_sq _ hf2


/-! ### The moving-window step function

`A(x) = Σ_{n ∈ s, x < n ≤ x + w} a n`, a finite sum of indicators of the windows
`Ico (n - w) n`.  This is the function whose `L²` norm appears on the right-hand side of
Gallagher's lemma. -/

/-- The moving window step function: `A(x) = Σ_{n ∈ s, x < n ≤ x + w} a n`. -/
noncomputable def win (w : ℝ) (a : ℤ → ℂ) (s : Finset ℤ) : ℝ → ℂ :=
  fun x => ∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + w), a n

/-- Indicactor form of the window sum. -/
theorem win_eq_indicator (x : ℝ) : win w a s x =
    ∑ n ∈ s, a n * (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ)) x := by
  unfold win
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : x < (n : ℝ) ∧ (n : ℝ) ≤ x + w
  · have hm : x ∈ Set.Ico ((n : ℝ) - w) (n : ℝ) := by
      rw [Set.mem_Ico]; constructor <;> linarith [h.1, h.2]
    rw [Set.indicator_of_mem hm]
    simp [h]
  · have hm : x ∉ Set.Ico ((n : ℝ) - w) (n : ℝ) := by
      rw [Set.mem_Ico]
      intro hx
      exact h ⟨hx.2, by linarith [hx.1]⟩
    rw [Set.indicator_of_notMem hm]
    simp [h]

theorem measurable_win : Measurable (win w a s) := by
  rw [show win w a s = fun x => ∑ n ∈ s,
      a n * (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ)) x from
    funext fun x => win_eq_indicator x]
  refine Finset.measurable_sum _ fun n _ => ?_
  exact measurable_const.mul (measurable_const.indicator measurableSet_Ico)

theorem norm_win_le (x : ℝ) : ‖win w a s x‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  rw [win_eq_indicator]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  by_cases hx : x ∈ Set.Ico ((n : ℝ) - w) (n : ℝ)
  · rw [Set.indicator_of_mem hx]; simp
  · rw [Set.indicator_of_notMem hx]; simp

theorem memLp_win : MemLp (win w a s) 2 volume := by
  rw [show win w a s = fun x => ∑ n ∈ s,
      a n * (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ)) x from
    funext fun x => win_eq_indicator x]
  refine memLp_finsetSum s fun n _ => ?_
  have h1 : MemLp ((Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet (1 : ℂ)
      (Or.inr (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  exact h1.const_mul (a n)

theorem integrable_win : Integrable (win w a s) := by
  rw [show win w a s = fun x => ∑ n ∈ s,
      a n * (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ)) x from
    funext fun x => win_eq_indicator x]
  refine integrable_finsetSum s fun n _ => ?_
  have h1 : Integrable ((Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => (1 : ℂ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  exact h1.const_mul (a n)

/-- The general exponential integral over a half-open interval. -/
theorem integral_Ico_exp_mul {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ico a b, Complex.exp (c₀ * (x : ℂ)) =
      (Complex.exp (c₀ * (b : ℂ)) - Complex.exp (c₀ * (a : ℂ))) / c₀ := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Complex.exp (c₀ * (y : ℂ)) / c₀)
        (Complex.exp (c₀ * (x : ℂ))) x := by
    intro x _
    have hlin : HasDerivAt (fun y : ℝ => c₀ * (y : ℂ)) c₀ x := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul c₀
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c₀ * (y : ℂ)))
        (Complex.exp (c₀ * (x : ℂ)) * c₀) x :=
      (Complex.hasDerivAt_exp (c₀ * (x : ℂ))).comp x hlin
    have h := hexp.div_const c₀
    convert h using 1
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c₀ * (x : ℂ))) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (c₀ * (x : ℂ))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  field_simp

/-- The integral of `e (x t)` over one window `Ico (c - w) c`. -/
theorem integral_window_e {t : ℝ} (ht : t ≠ 0) {w c : ℝ} (hw : 0 < w) :
    ∫ x in Set.Ico (c - w) c, Decomp1524a.e (x * t)
      = (Decomp1524a.e (c * t) - Decomp1524a.e ((c - w) * t)) / (2 * π * I * (t : ℂ)) := by
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc₀ : ((2 : ℂ) * π * I * (t : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) ht'
  have hmain := integral_Ico_exp_mul (c₀ := (2 : ℂ) * π * I * (t : ℂ)) hc₀
    (a := c - w) (b := c) (by linarith)
  have hL : ∫ x in Set.Ico (c - w) c, Decomp1524a.e (x * t)
      = ∫ x in Set.Ico (c - w) c, Complex.exp (((2 : ℂ) * π * I * (t : ℂ)) * (x : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    unfold Decomp1524a.e
    congr 1
    push_cast
    ring
  rw [hL, hmain]
  unfold Decomp1524a.e
  congr 2 <;> push_cast <;> ring


/-! ### Additivity of `e` -/

theorem e_add (x y : ℝ) : Decomp1524a.e (x + y) =
    Decomp1524a.e x * Decomp1524a.e y := by
  unfold Decomp1524a.e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_neg (x : ℝ) : Decomp1524a.e (-x) = (Decomp1524a.e x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← e_add, add_neg_cancel]
  unfold Decomp1524a.e
  simp

theorem e_sub (x y : ℝ) : Decomp1524a.e (x - y) =
    Decomp1524a.e x * (Decomp1524a.e y)⁻¹ := by
  rw [sub_eq_add_neg, e_add, e_neg]

theorem norm_e (x : ℝ) : ‖Decomp1524a.e x‖ = 1 := by
  unfold Decomp1524a.e
  rw [Complex.norm_exp]
  simp [Complex.ofReal_re]

/-! ### The Fourier character as a complex number -/

theorem fourierChar_smul (y : ℝ) (z : ℂ) :
    Real.fourierChar y • z = Decomp1524a.e y * z := by
  have harg : (↑(2 * π * y) * Complex.I) = 2 * π * Complex.I * (y : ℂ) := by
    push_cast; ring
  rw [Circle.smul_def, Real.fourierChar_apply, harg, smul_eq_mul]
  unfold Decomp1524a.e
  rfl

/-- The phase factor of the inverse Fourier transform is `e (v * t)`. -/
theorem fourierInv_integrand (f : ℝ → ℂ) (t v : ℝ) :
    Real.fourierChar ⟪v, t⟫ • f v = Decomp1524a.e (v * t) * f v := by
  rw [fourierChar_smul, Real.inner_apply]


/-! ### The inverse Fourier transform of the window step function -/

theorem continuous_e_mul (t : ℝ) : Continuous fun v : ℝ => Decomp1524a.e (v * t) := by
  unfold Decomp1524a.e
  fun_prop

theorem integrable_indicator_phase (t : ℝ) (c : ℂ) (n : ℤ) :
    Integrable ((Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator
      (fun v : ℝ => Decomp1524a.e (v * t) * c)) := by
  refine Integrable.mono'
    (g := (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator (fun _ => ‖c‖)) ?_ ?_ ?_
  · exact (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  · exact (((continuous_e_mul t).measurable.mul measurable_const).indicator
      measurableSet_Ico).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v => ?_
    by_cases hv : v ∈ Set.Ico ((n : ℝ) - w) (n : ℝ)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, norm_mul, norm_e, one_mul]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, norm_zero]

theorem fourierInv_win_eq {t : ℝ} (ht : t ≠ 0) (hw : 0 < w) :
    𝓕⁻ (win w a s) t =
      ((1 - Decomp1524a.e (-(w * t))) / (2 * π * I * (t : ℂ))) * Decomp1524a.trig s a t := by
  rw [Real.fourierInv_eq]
  have h1 : ∀ v : ℝ, Real.fourierChar ⟪v, t⟫ • win w a s v
      = Decomp1524a.e (v * t) * win w a s v := fun v => fourierInv_integrand _ t v
  simp_rw [h1]
  have h2 : ∀ v : ℝ, Decomp1524a.e (v * t) * win w a s v
      = ∑ n ∈ s, (Set.Ico ((n : ℝ) - w) (n : ℝ)).indicator
          (fun v => Decomp1524a.e (v * t) * a n) v := by
    intro v
    rw [win_eq_indicator, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hv : v ∈ Set.Ico ((n : ℝ) - w) (n : ℝ)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; ring
  simp_rw [h2]
  rw [integral_finsetSum]
  · rw [show Decomp1524a.trig s a t
        = ∑ n ∈ s, a n * Decomp1524a.e ((n : ℝ) * t) from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hwt : ((n : ℝ) - w) * t = (n : ℝ) * t + (-(w * t)) := by ring
    rw [integral_indicator measurableSet_Ico, integral_mul_const,
      integral_window_e (w := w) ht hw, hwt, e_add]
    field_simp
  · intro n _
    exact integrable_indicator_phase t (a n) n


/-! ### Bounds on the window transform -/

theorem norm_trig_le (t : ℝ) : ‖Decomp1524a.trig s a t‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_mul, norm_e, mul_one]

theorem norm_sub_one_sq {z : ℂ} (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq, hz]
  simp only [Complex.normSq_one, map_one, mul_one, Complex.sub_re, Complex.one_re]
  ring

theorem e_eq_exp (y : ℝ) : Decomp1524a.e y = Complex.exp ((2 * π * y : ℝ) * Complex.I) := by
  unfold Decomp1524a.e
  congr 1
  push_cast
  ring

/-- `‖1 - e y‖ ≤ 2π|y|`. -/
theorem norm_one_sub_e_le (y : ℝ) :
    ‖(1 : ℂ) - Decomp1524a.e y‖ ≤ 2 * π * |y| := by
  have hsq : ‖(1 : ℂ) - Decomp1524a.e y‖ ^ 2 = 2 - 2 * Real.cos (2 * π * y) := by
    rw [norm_sub_rev, norm_sub_one_sq (norm_e y), e_eq_exp, Complex.exp_ofReal_mul_I_re]
  have hcos : 2 - 2 * Real.cos (2 * π * y) ≤ (2 * π * y) ^ 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * π * y)
    nlinarith [h]
  have h2 : ‖(1 : ℂ) - Decomp1524a.e y‖ ^ 2 ≤ (2 * π * |y|) ^ 2 := by
    rw [hsq]
    refine hcos.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  have hc : (0:ℝ) ≤ 2 * π * |y| := by positivity
  calc ‖(1 : ℂ) - Decomp1524a.e y‖ = Real.sqrt (‖(1 : ℂ) - Decomp1524a.e y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2 * π * |y|) ^ 2) := Real.sqrt_le_sqrt h2
    _ = 2 * π * |y| := Real.sqrt_sq hc

/-- `‖1 - e y‖ ≤ 2`. -/
theorem norm_one_sub_e_le_two (y : ℝ) : ‖(1 : ℂ) - Decomp1524a.e y‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_e]
  norm_num

theorem norm_den (t : ℝ) : ‖((2 : ℂ) * π * I * (t : ℂ))‖ = 2 * π * |t| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs]
  have hπ : (0:ℝ) < π := Real.pi_pos
  rw [abs_of_pos hπ]
  have : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [this]; ring

/-- The phase factor of `𝓕⁻ A` times `1 + π w |t|` is bounded by `2w`. -/
theorem norm_phase_mul_le {t : ℝ} (ht : t ≠ 0) (hw : 0 < w) :
    ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ * (1 + π * w * |t|)
      ≤ 2 * w := by
  have hat : (0:ℝ) < |t| := abs_pos.mpr ht
  have hden := norm_den t
  rw [norm_div, hden]
  rcases le_or_gt (π * w * |t|) 1 with hle | hgt
  · have hnum : ‖(1 : ℂ) - Decomp1524a.e (-(w * t))‖ ≤ 2 * π * (w * |t|) := by
      have h := norm_one_sub_e_le (-(w * t))
      rwa [abs_neg, abs_mul, abs_of_pos hw] at h
    have hdenpos : (0:ℝ) < 2 * π * |t| := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hdenpos]
    have h1 : ‖(1 : ℂ) - Decomp1524a.e (-(w * t))‖ * (1 + π * w * |t|) ≤
        (2 * π * (w * |t|)) * 2 :=
      mul_le_mul hnum (by linarith) (by positivity) (by positivity)
    nlinarith [h1, Real.pi_pos, hat, hw]
  · have hnum : ‖(1 : ℂ) - Decomp1524a.e (-(w * t))‖ ≤ 2 := norm_one_sub_e_le_two _
    have hdenpos : (0:ℝ) < 2 * π * |t| := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hdenpos]
    have h1 : ‖(1 : ℂ) - Decomp1524a.e (-(w * t))‖ * (1 + π * w * |t|) ≤ 2 * (1 + π * w * |t|) :=
      mul_le_mul hnum (by linarith) (by positivity) (by norm_num)
    nlinarith [h1, hgt, Real.pi_pos, hat, hw]


theorem continuous_fourierInv_win : Continuous (𝓕⁻ (win w a s)) :=
  VectorFourier.fourierIntegral_continuous (V := ℝ) (W := ℝ) (f := win w a s)
    (e := Real.fourierChar) (L := -innerₗ ℝ) (μ := volume)
    Real.continuous_fourierChar continuous_inner.neg integrable_win

/-- The transform of the window step function is `L²`. -/
theorem memLp_fourierInv_win (hw : 0 < w) : MemLp (𝓕⁻ (win w a s)) 2 volume := by
  classical
  set K := ∑ n ∈ s, ‖a n‖ with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set m := min 1 (π * w) with hmdef
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hm2 : m ≤ π * w := min_le_right _ _
  have hmeas : AEStronglyMeasurable (𝓕⁻ (win w a s)) volume :=
    continuous_fourierInv_win.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine Integrable.mono'
    (g := fun t : ℝ => (2 * w * K) ^ 2 / m ^ 2 * (1 + t ^ 2)⁻¹) ?_ ?_ ?_
  · have h : Integrable fun x : ℝ => (1 + x ^ 2)⁻¹ := integrable_inv_one_add_sq
    exact h.const_mul _
  · exact hmeas.norm.pow 2
  · have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with t ht
    have hb : ‖𝓕⁻ (win w a s) t‖ * (1 + π * w * |t|) ≤ 2 * w * K := by
      rw [fourierInv_win_eq ht hw, norm_mul]
      have h1 : ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ *
          (1 + π * w * |t|) ≤ 2 * w := norm_phase_mul_le ht hw
      calc ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ *
            ‖Decomp1524a.trig s a t‖ * (1 + π * w * |t|)
          = (‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ *
            (1 + π * w * |t|)) * ‖Decomp1524a.trig s a t‖ := by ring
        _ ≤ (2 * w) * K :=
          mul_le_mul h1 (norm_trig_le t) (norm_nonneg _) (by positivity)
    have hmle : m * (1 + |t|) ≤ 1 + π * w * |t| := by
      nlinarith [hm1, hm2, abs_nonneg t]
    have hstep : m ^ 2 * (1 + t ^ 2) ≤ (1 + π * w * |t|) ^ 2 := by
      have h1 : (m * (1 + |t|)) ^ 2 ≤ (1 + π * w * |t|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmle 2
      have h2 : (1:ℝ) + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
      nlinarith [h1, h2, hm0, sq_nonneg m, sq_nonneg (1 + |t|)]
    have hD : ‖𝓕⁻ (win w a s) t‖ ^ 2 * (1 + π * w * |t|) ^ 2 ≤ (2 * w * K) ^ 2 := by
      have h0 : (0:ℝ) ≤ ‖𝓕⁻ (win w a s) t‖ * (1 + π * w * |t|) := by positivity
      calc ‖𝓕⁻ (win w a s) t‖ ^ 2 * (1 + π * w * |t|) ^ 2
          = (‖𝓕⁻ (win w a s) t‖ * (1 + π * w * |t|)) ^ 2 := by ring
        _ ≤ (2 * w * K) ^ 2 := pow_le_pow_left₀ h0 hb 2
    have hgoal : ‖‖𝓕⁻ (win w a s) t‖ ^ 2‖ ≤ (2 * w * K) ^ 2 / m ^ 2 * (1 + t ^ 2)⁻¹ := by
      rw [Real.norm_of_nonneg (by positivity)]
      rw [show (2 * w * K) ^ 2 / m ^ 2 * (1 + t ^ 2)⁻¹
          = (2 * w * K) ^ 2 / (m ^ 2 * (1 + t ^ 2)) from by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hD, hstep, sq_nonneg ‖𝓕⁻ (win w a s) t‖]
    exact hgoal


/-! ### The pointwise bound `‖S(t)‖ ≤ πT ‖𝓕⁻A(t)‖` -/

theorem continuous_trig : Continuous fun t : ℝ => Decomp1524a.trig s a t := by
  unfold Decomp1524a.trig
  refine continuous_finset_sum _ fun n _ => ?_
  exact continuous_const.mul (by unfold Decomp1524a.e; fun_prop)

theorem norm_one_sub_e_eq (y : ℝ) :
    ‖(1 : ℂ) - Decomp1524a.e y‖ = 2 * |Real.sin (π * y)| := by
  have hsq : ‖(1 : ℂ) - Decomp1524a.e y‖ ^ 2 = (2 * |Real.sin (π * y)|) ^ 2 := by
    rw [norm_sub_rev, norm_sub_one_sq (norm_e y), e_eq_exp, Complex.exp_ofReal_mul_I_re]
    have h := Real.cos_two_mul' (π * y)
    rw [show (2 : ℝ) * (π * y) = 2 * π * y from by ring] at h
    rw [h, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (π * y)]
  have hc : (0:ℝ) ≤ 2 * |Real.sin (π * y)| := by positivity
  calc ‖(1 : ℂ) - Decomp1524a.e y‖ = Real.sqrt (‖(1 : ℂ) - Decomp1524a.e y‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((2 * |Real.sin (π * y)|) ^ 2) := by rw [hsq]
    _ = 2 * |Real.sin (π * y)| := Real.sqrt_sq hc

theorem trig_le_phase {T t : ℝ} (hT : 0 < T) (ht : t ≠ 0) (htT : |t| ≤ T) :
    ‖Decomp1524a.trig s a t‖ ≤ π * T * ‖𝓕⁻ (win (1 / (2 * T)) a s) t‖ := by
  set w := 1 / (2 * T) with hwdef
  have hw : (0:ℝ) < w := by positivity
  have htT' : (0:ℝ) < |t| := abs_pos.mpr ht
  have hu : π * (w * |t|) ≤ π / 2 := by
    have he : π * (w * |t|) = π * |t| / (2 * T) := by
      rw [hwdef]; field_simp
    rw [he, div_le_iff₀ (by positivity : (0:ℝ) < 2 * T)]
    nlinarith [htT, Real.pi_pos]
  have hsin_low : 2 * w * |t| ≤ |Real.sin (π * (w * t))| := by
    have h1 : |π * (w * t)| ≤ π / 2 := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hw]
      exact hu
    have h2 := Real.mul_le_sin (abs_nonneg (π * (w * t))) h1
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [h1, Real.pi_pos])] at h2
    calc 2 * w * |t| = 2 / π * |π * (w * t)| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hw]
          field_simp
      _ ≤ |Real.sin (π * (w * t))| := h2
  have hcval : ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖
      = |Real.sin (π * (w * t))| / (π * |t|) := by
    rw [norm_div, norm_den, norm_one_sub_e_eq,
      show π * (-(w * t)) = -(π * (w * t)) from by ring, Real.sin_neg, abs_neg]
    field_simp
  have hclow : 2 * w / π ≤ ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ := by
    rw [hcval, div_le_iff₀ (by positivity : (0:ℝ) < π)]
    rw [show |Real.sin (π * (w * t))| / (π * |t|) * π = |Real.sin (π * (w * t))| / |t| from by
      field_simp]
    rw [le_div_iff₀ htT']
    linarith [hsin_low]
  have hkey : ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ *
      ‖Decomp1524a.trig s a t‖ = ‖𝓕⁻ (win w a s) t‖ := by
    rw [fourierInv_win_eq ht hw, norm_mul]
  have hTw : π * T * (2 * w / π) = 1 := by
    rw [hwdef]; field_simp
  calc ‖Decomp1524a.trig s a t‖
      = π * T * (2 * w / π) * ‖Decomp1524a.trig s a t‖ := by rw [hTw, one_mul]
    _ ≤ π * T * ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ *
          ‖Decomp1524a.trig s a t‖ := by
        have h0 : (0:ℝ) ≤ ‖Decomp1524a.trig s a t‖ := norm_nonneg _
        have h1 : π * T * (2 * w / π) ≤ π * T *
            ‖(1 - Decomp1524a.e (-(w * t))) / ((2 : ℂ) * π * I * (t : ℂ))‖ := by
          have : (0:ℝ) < π * T := by positivity
          exact mul_le_mul_of_nonneg_left hclow this.le
        exact mul_le_mul_of_nonneg_right h1 h0
    _ = π * T * ‖𝓕⁻ (win w a s) t‖ := by rw [← hkey]; ring

theorem hne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  rw [MeasureTheory.ae_iff]; simp


theorem continuous_fourier_win : Continuous (𝓕 (win w a s)) := by
  have h : (𝓕 (win w a s)) = fun t => 𝓕⁻ (win w a s) (-t) := by
    funext t
    rw [Real.fourierInv_eq_fourier_neg]
    simp
  rw [h]
  exact continuous_fourierInv_win.comp continuous_neg

/-- LEAF. Gallagher's lemma: for a finite `s ⊆ ℤ` and `T > 0`,
`∫_{-T}^{T} |Σ_{n ∈ s} a_n e(nt)|² dt ≤ π² T² ∫_ℝ |Σ_{n ∈ s, x < n ≤ x + 1/(2T)} a_n|² dx`.
Proof: Plancherel for the step function `C(x)`, whose transform is `S(-t) sin(πt/2T)/(πt)` up
to a unimodular factor, and `sin u ≥ 2u/π` on `[0, π/2]`. Gallagher 1970 Lemma 1;
Montgomery, Topics, Lemma 1.9. Unit U-1524. -/
theorem gallagher_lemma (s : Finset ℤ) (a : ℤ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖trig s a t‖ ^ 2 ≤
      π ^ 2 * T ^ 2 * ∫ x : ℝ, ‖∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)),
        a n‖ ^ 2 := by
  have hw : (0:ℝ) < 1 / (2 * T) := by positivity
  have hF : MemLp (𝓕 (win (1 / (2 * T)) a s)) 2 volume := by
    have h1 : MemLp (fun t : ℝ => 𝓕 (win (1 / (2 * T)) a s) (-t)) 2 volume := by
      rw [show (fun t : ℝ => 𝓕 (win (1 / (2 * T)) a s) (-t))
          = 𝓕⁻ (win (1 / (2 * T)) a s) from
        funext fun t => (Real.fourierInv_eq_fourier_neg _ t).symm]
      exact memLp_fourierInv_win hw
    have h2 := h1.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
    simpa [Function.comp_def, neg_neg] using h2
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (-T) T →
      ‖Decomp1524a.trig s a t‖ ^ 2 ≤
        (π * T) ^ 2 * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2 := by
    filter_upwards [hne_zero] with t ht htI
    have h1 := trig_le_phase (s := s) (a := a) hT ht (abs_le.mpr ⟨htI.1, htI.2⟩)
    rw [show 𝓕⁻ (win (1 / (2 * T)) a s) t = 𝓕 (win (1 / (2 * T)) a s) (-t) from
      Real.fourierInv_eq_fourier_neg _ t] at h1
    calc ‖Decomp1524a.trig s a t‖ ^ 2
        ≤ (π * T * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (π * T) ^ 2 * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2 := by ring
  have hfi : IntervalIntegrable (fun t : ℝ => ‖Decomp1524a.trig s a t‖ ^ 2) volume (-T) T :=
    (continuous_trig.norm.pow 2).intervalIntegrable _ _
  have hgi : IntervalIntegrable
      (fun t : ℝ => (π * T) ^ 2 * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2) volume (-T) T :=
    ((continuous_const.mul ((continuous_fourier_win.comp continuous_neg).norm.pow 2))).intervalIntegrable _ _
  have hmono : ∫ t in (-T)..T, ‖Decomp1524a.trig s a t‖ ^ 2
      ≤ ∫ t in (-T)..T, (π * T) ^ 2 * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_ae_restrict (μ := volume) (by linarith : -T ≤ T) hfi hgi ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr hbound
  have hInt : Integrable fun t : ℝ => ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hplanch : ∫ t, ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2 ≤
      ∫ t, ‖win (1 / (2 * T)) a s t‖ ^ 2 :=
    integral_norm_sq_fourier_le _ integrable_win memLp_win hF
  calc ∫ t in (-T)..T, ‖Decomp1524a.trig s a t‖ ^ 2
      ≤ ∫ t in (-T)..T, (π * T) ^ 2 * ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2 := hmono
    _ = (π * T) ^ 2 * ∫ t in (-T)..T, ‖𝓕 (win (1 / (2 * T)) a s) (-t)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ = (π * T) ^ 2 * ∫ t in (-T)..T, ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2 := by
        rw [intervalIntegral.integral_comp_neg (f := fun t => ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2)]
        norm_num
    _ ≤ (π * T) ^ 2 * ∫ t, ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2 := by
        have hle : ∫ t in (-T)..T, ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2
            ≤ ∫ t, ‖𝓕 (win (1 / (2 * T)) a s) t‖ ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
          exact setIntegral_le_integral hInt (Filter.Eventually.of_forall fun t => by positivity)
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ (π * T) ^ 2 * ∫ t, ‖win (1 / (2 * T)) a s t‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hplanch (by positivity)
    _ = π ^ 2 * T ^ 2 * ∫ x : ℝ,
          ‖∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)), a n‖ ^ 2 := by
        have hA : (win (1 / (2 * T)) a s) = fun x : ℝ =>
            ∑ n ∈ s.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)), a n := rfl
        rw [hA]
        congr 1
        ring



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
