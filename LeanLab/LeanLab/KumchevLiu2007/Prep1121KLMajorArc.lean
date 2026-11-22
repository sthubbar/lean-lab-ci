/-
PREP 2026-11-21, KL-cited splitter. SPLIT of Task628.major_arc_block, BlockInputs628.lean.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 5 to 7, displays 16 to 28.

DECISION. Display 28 is proved IN PLACE on pages 5 to 7 from the hypotheses
(A1.2) and (A2.2) of page 5. Those two hypotheses are a CITATION WALL: page 15
asserts them for the primes and for lambda0 only by "the same methods as
Huxley's result on primes in short intervals", with no proof printed. They are
taken here as the named Props A12Corr and A22Corr, not as open leaves.

The printed (A1.2) and (A2.2) put the character chi on both the weight and the
main term f_j. For a principal character of modulus q above one that form is
false, see LevelExceedingOneFails and Eq33RouteE, Eq33RouteF. The circle method
step of display 25 needs chi on the weight only. A12Corr and A22Corr use that
corrected form. This is a QUESTION about the printed hypotheses, not a finding.

The in place part is cut into the Fourier split of the representation count
into major and minor parts, PROVED here, and seven LEAF lemmas: the four term
identity of display 28, the two bounds of display 22, and the four error bounds of displays
20, 24, 26 and 27. The paper keeps eta arbitrary; the leaves fix eta = 1/4,
so every error is at most C Y^(1/2) P^(-1/4), a consequence of the printed bounds.
The final theorem major_arc_block_of_char_inputs proves the exact statement of
Task628.major_arc_block from the leaves, CONDITIONAL ON A12Corr and A22Corr.
For epsilon above 7/18 the block range is empty and nothing is used.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628
import LeanLab.KumchevLiu2007.QuadraticEnergy674

namespace LeanLab.KumchevLiu2007.Prep1121KLMajor

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 5, the function T1 after hypothesis (A2.2), with the weight
f1(u) = 1/log u of page 15 on the interval I1 of page 2 display 5. -/
noncomputable def T1 (X Y β : ℝ) : ℂ :=
  ∑ m ∈ primeWindow X Y, ((1 / Real.log (m : ℝ) : ℝ) : ℂ) *
    fourier (m : ℤ) (β : AddCircle (1 : ℝ))

/-- P0088 page 5, the function T2 after hypothesis (A2.2), with the weight
f2 of page 15 and z0 = Y^(1/4) P^(-2) of page 8 display 34. -/
noncomputable def T2 (Y P β : ℝ) : ℂ :=
  ∑ m ∈ squareWindow Y, ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ) *
    fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))

/-- P0088 page 4 display 15. The pairs q, a with q at most P, a from 0 to q and
a coprime to q, which index the major arcs meeting the period interval. -/
noncomputable def arcPairs (P : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊P⌋₊) ×ˢ Finset.range (⌊P⌋₊ + 1)).filter
    (fun v => v.2 ≤ v.1 ∧ Nat.Coprime v.2 v.1)

/-- P0088 page 4 display 15, the closed arc M(q, a) of width R^(-1) in q alpha. -/
def arc (R : ℝ) (v : ℕ × ℕ) : Set ℝ := {α | |(v.1 : ℝ) * α - v.2| ≤ R⁻¹}

/-- P0088 page 5, S1* on M: mu(q)/phi(q) T1(alpha - a/q) on M(q, a), Q = H/P. -/
noncomputable def S1star (X Y H P α : ℝ) : ℂ :=
  ∑ v ∈ arcPairs P, (arc (H / P) v).indicator
    (fun α => ((ArithmeticFunction.moebius v.1 : ℤ) : ℂ) / (Nat.totient v.1 : ℂ) *
      T1 X Y (α - v.2 / v.1)) α

/-- P0088 page 5, S2* on M: S(q, a)/phi(q) T2(alpha - a/q) on M(q, a), with S(q, a)
of page 3 display 8. -/
noncomputable def S2star (Y H P α : ℝ) : ℂ :=
  ∑ v ∈ arcPairs P, (arc (H / P) v).indicator
    (fun α => U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
      T2 Y P (α - v.2 / v.1)) α

/-- P0088 page 7 display 28, left side: the integral of S1 S2 e(-alpha n) over the
major arcs M in one period. -/
noncomputable def majorIntegral (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * roughSum Y P α)

/-- P0088 page 7 display 28, first term: S1* S2* over M0, where M0 of display 23
has width 1/(q Q0), Q0 = Y P^(-3) of display 14, written as majorArcs (Y P^(-2)) P. -/
noncomputable def termA (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (S1star X Y H P α * S2star Y H P α)

/-- P0088 page 7 display 28, second term, bounded in display 20. -/
noncomputable def termB (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      (primeSum X Y α * (roughSum Y P α - S2star Y H P α))

/-- P0088 page 7 display 28, third term over m0 = M minus M0, bounded in display 24. -/
noncomputable def termC (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P),
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) * (primeSum X Y α * S2star Y H P α)

/-- P0088 page 7 display 28, fourth term over M0, bounded in display 26. -/
noncomputable def termD (X Y H P : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P,
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      ((primeSum X Y α - S1star X Y H P α) * S2star Y H P α)

/-- P0088 page 7 display 28 error size O(Y^(1/2) P^(-1/2 + eta)) with eta = 1/4, in
the block range of Task628.major_arc_block and the window Y = X^(7/12 + eps/2) of
page 16. The range is empty for eps above 7/18. -/
def BlockErrorBound (E : ℝ → ℝ → ℝ → ℝ → ℕ → ℂ) : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ n : ℕ, ‖E X (windowY X ε) H (Real.log X ^ B) n‖ ≤
        C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-(1 / 4 : ℝ))

/-- P0088 page 5 hypothesis (A1.2) for the primes, defect with chi on the weight
only, the form the character expansion of display 25 uses. -/
noncomputable def primeDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (X Y u v : ℝ) : ℂ :=
  ∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
    ((if m.Prime then χ m else 0) -
      (if χ = 1 then ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0))

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A1.2) for lambda1 the primes, as asserted on
page 15 by the methods of Huxley's theorem, with chi on the weight only. -/
def A12Corr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)

/-- P0088 page 5 hypothesis (A2.2) for lambda2 = lambda0 of display 34, defect with chi
on the weight only. -/
noncomputable def roughDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (Y P δ t : ℝ) : ℂ :=
  ∑ m ∈ (squareWindow Y).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
    (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
      (if χ = 1 then ((f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
       else 0))

/-- CITED, NAMED HYPOTHESIS. P0088 page 5 (A2.2) for lambda0 with the f2 of page 15,
asserted there by the same Huxley type methods, with chi on the weight only,
for 0 < delta at most q Q / Y, Q = H/P of display 14. -/
def A22Corr : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 * (Real.log X ^ B) ^ (-4 : ℤ)

/-- P0088 page 6 display 22 for j = 1, all |beta| at most 1/2. -/
def T1BoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
    ∀ β : ℝ, |β| ≤ 1 / 2 →
      ‖T1 X (windowY X ε) β‖ ≤ C * windowY X ε / (1 + windowY X ε * |β|)

/-- P0088 page 6 display 22 for j = 2, only for |beta| at most Y^(-1/2)/4, where the
phase derivative is at most 1/2. For larger beta display 22 fails for T2: near
beta = 1/3 the sum has no cancellation. QUESTION Q2 of the step notes. -/
def T2BoundProp : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
    ∀ β : ℝ, |β| ≤ 1 / (4 * Real.sqrt (windowY X ε)) →
      ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤
        C * Real.sqrt (windowY X ε) / (1 + windowY X ε * |β|)

/-- PROVED. P0088 page 4 display 13 split at display 15. The representation count is the
major arc integral plus the minor arc Fourier coefficient, by
representationPolynomial_fourierCoeff, fourierCoeff_eq_intervalIntegral and
representationPolynomial_eq_prime_mul_rough. -/
theorem roughCount_eq_major_add_minor (X Y H P : ℝ) (n : ℕ) :
    (roughCount X Y P n : ℂ) = majorIntegral X Y H P n + minorCoefficient X Y H P n := by
  have hcont : Continuous (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      representationPolynomial X Y P (α : AddCircle (1 : ℝ))) := by
    have hc : Continuous (fun α : ℝ => (α : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
    refine ((fourier _).continuous.comp hc).mul ?_
    unfold representationPolynomial
    exact continuous_finsetSum _ (fun v _ => (fourier _).continuous.comp hc)
  have hint : IntegrableOn (fun α : ℝ => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ)) *
      representationPolynomial X Y P (α : AddCircle (1 : ℝ))) (Set.Ioc 0 1) :=
    hcont.integrableOn_Ioc
  rw [← representationPolynomial_fourierCoeff X Y P n,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add,
    intervalIntegral.integral_of_le zero_le_one, div_one, one_smul]
  simp_rw [smul_eq_mul]
  rw [← integral_inter_add_sdiff (measurableSet_majorArcs H P) hint, majorIntegral,
    minorCoefficient, Set.sdiff_eq]
  congr 1
  refine setIntegral_congr_fun ((measurableSet_Ioc).inter (measurableSet_majorArcs H P)) ?_
  intro α _
  simp only [representationPolynomial_eq_prime_mul_rough]

/-- Page 5 display 21: every shifted Fourier character is essentially bounded. -/
theorem fourier_shift_memLp_top (k : ℤ) (c : ℝ) :
    MemLp (fun α : ℝ => fourier k ((α - c : ℝ) : AddCircle (1 : ℝ))) ⊤ volume := by
  apply memLp_top_of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun α => by simp [fourier_apply, Circle.norm_coe])

/-- Page 5 display 21: the finite model sum T1 is essentially bounded. -/
theorem T1_memLp_top (X Y c : ℝ) : MemLp (fun α => T1 X Y (α - c)) ⊤ volume := by
  unfold T1
  exact memLp_finsetSum _ (fun m _ => (fourier_shift_memLp_top (m : ℤ) c).const_mul _)

/-- Page 5 display 21: the finite model sum T2 is essentially bounded. -/
theorem T2_memLp_top (Y P c : ℝ) : MemLp (fun α => T2 Y P (α - c)) ⊤ volume := by
  unfold T2
  exact memLp_finsetSum _ (fun m _ => (fourier_shift_memLp_top ((m ^ 2 : ℕ) : ℤ) c).const_mul _)

/-- Page 4 display 15: each closed major arc is measurable. -/
theorem measurableSet_arc (R : ℝ) (v : ℕ × ℕ) : MeasurableSet (arc R v) := by
  unfold arc
  exact measurableSet_le (by fun_prop) measurable_const

/-- Page 5 display 16: the piecewise model S1star is essentially bounded. -/
theorem S1star_memLp_top (X Y H P : ℝ) : MemLp (S1star X Y H P) ⊤ volume := by
  unfold S1star
  exact memLp_finsetSum _ (fun v _ =>
    ((T1_memLp_top X Y (v.2 / v.1)).const_mul _).indicator
      (measurableSet_arc (H / P) v).nullMeasurableSet)

/-- Page 5 display 17: the piecewise model S2star is essentially bounded. -/
theorem S2star_memLp_top (Y H P : ℝ) : MemLp (S2star Y H P) ⊤ volume := by
  unfold S2star
  exact memLp_finsetSum _ (fun v _ =>
    ((T2_memLp_top Y P (v.2 / v.1)).const_mul _).indicator
      (measurableSet_arc (H / P) v).nullMeasurableSet)

/-- Page 4 display 13: the prime sum is essentially bounded. -/
theorem primeSum_memLp_top (X Y : ℝ) : MemLp (primeSum X Y) ⊤ volume := by
  unfold primeSum
  simpa only [sub_zero] using
    memLp_finsetSum ((primeWindow X Y).filter Nat.Prime)
      (fun m _ => fourier_shift_memLp_top (m : ℤ) 0)

/-- Page 4 display 13: the rough sum is essentially bounded. -/
theorem roughSum_memLp_top (Y P : ℝ) : MemLp (roughSum Y P) ⊤ volume := by
  unfold roughSum
  simpa only [sub_zero] using memLp_finsetSum (squareWindow Y)
    (fun m _ => (fourier_shift_memLp_top ((m ^ 2 : ℕ) : ℤ) 0).const_mul
      (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m))

/-- Page 4 display 15: increasing H narrows the major arcs. -/
theorem majorArcs_antitone {H K P : ℝ} (hH : 0 < H) (hP : 0 < P) (hHK : H ≤ K) :
    majorArcs K P ⊆ majorArcs H P := by
  rintro α ⟨q, hq, hqP, a, hcop, hα⟩
  exact ⟨q, hq, hqP, a, hcop, hα.trans
    (inv_anti₀ (div_pos hH hP) (div_le_div_of_nonneg_right hHK hP.le))⟩

/-- LEAF: P0088 page 7 display 28, the four term identity. In the block range M0 lies in
M since Q0 = Y P^(-3) is at least Q = H/P, and every integrand is bounded and
measurable on the period, so the integral splits over M0 and M minus M0. -/
theorem major_decomp :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) → ∀ n : ℕ,
        majorIntegral X (windowY X ε) H (Real.log X ^ B) n =
          termA X (windowY X ε) H (Real.log X ^ B) n +
          termB X (windowY X ε) H (Real.log X ^ B) n +
          termC X (windowY X ε) H (Real.log X ^ B) n +
          termD X (windowY X ε) H (Real.log X ^ B) n := by
  intro B hB ε hε hε'
  refine ⟨3, ?_⟩
  intro X H hX hlo hhi n
  let Y := windowY X ε
  let P := Real.log X ^ B
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP : 0 < P := by linarith
  have hY : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hH : 0 < H := lt_of_lt_of_le (mul_pos
    (Real.rpow_pos_of_pos hX0 _) (zpow_pos hP _)) hlo
  have hHK : H ≤ Y * P ^ (-2 : ℤ) := hhi.trans
    (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hP1 (by norm_num)) hY.le)
  have hsub : majorArcs (Y * P ^ (-2 : ℤ)) P ⊆ majorArcs H P :=
    majorArcs_antitone hH hP hHK
  let e : ℝ → ℂ := fun α => fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))
  let p : ℝ → ℂ := primeSum X Y
  let r : ℝ → ℂ := roughSum Y P
  let s : ℝ → ℂ := S1star X Y H P
  let t : ℝ → ℂ := S2star Y H P
  let M := Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P
  let M0 := Set.Ioc (0 : ℝ) 1 ∩ majorArcs (Y * P ^ (-2 : ℤ)) P
  have he : MemLp e ⊤ volume := by
    simpa only [sub_zero] using fourier_shift_memLp_top (-(n : ℤ)) 0
  have hp : MemLp p ⊤ volume := primeSum_memLp_top X Y
  have hr : MemLp r ⊤ volume := roughSum_memLp_top Y P
  have hs : MemLp s ⊤ volume := S1star_memLp_top X Y H P
  have ht : MemLp t ⊤ volume := S2star_memLp_top Y H P
  have hint (f : ℝ → ℂ) (hf : MemLp f ⊤ volume) (U : Set ℝ)
      (hU : U ⊆ Set.Ioc (0 : ℝ) 1) : IntegrableOn f U := by
    have hper : IntegrableOn f (Set.Ioc (0 : ℝ) 1) :=
      MemLp.integrable (by simp) (hf.mono_measure Measure.restrict_le_self)
    exact hper.mono_set hU
  have hB : IntegrableOn (fun α => e α * (p α * (r α - t α))) M :=
    hint _ (he.mul (r := ⊤) (hp.mul (r := ⊤) (hr.sub ht))) _ Set.inter_subset_left
  have hpt : IntegrableOn (fun α => e α * (p α * t α)) M :=
    hint _ (he.mul (r := ⊤) (hp.mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hst : IntegrableOn (fun α => e α * (s α * t α)) M0 :=
    hint _ (he.mul (r := ⊤) (hs.mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hD : IntegrableOn (fun α => e α * ((p α - s α) * t α)) M0 :=
    hint _ (he.mul (r := ⊤) ((hp.sub hs).mul (r := ⊤) ht)) _ Set.inter_subset_left
  have hsplit := integral_inter_add_sdiff
    (measurableSet_majorArcs (Y * P ^ (-2 : ℤ)) P) hpt
  have hset0 : M ∩ majorArcs (Y * P ^ (-2 : ℤ)) P = M0 := by
    ext α
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩
  have hsetC : M \ majorArcs (Y * P ^ (-2 : ℤ)) P =
      Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P) := by
    ext α
    simp only [M, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hset0, hsetC] at hsplit
  change (∫ α in M, e α * (p α * r α)) =
    (∫ α in M0, e α * (s α * t α)) +
    (∫ α in M, e α * (p α * (r α - t α))) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P), e α * (p α * t α)) +
    (∫ α in M0, e α * ((p α - s α) * t α))
  have hfirst : (∫ α in M, e α * (p α * r α)) =
      (∫ α in M, e α * (p α * (r α - t α))) +
      (∫ α in M, e α * (p α * t α)) := by
    rw [← integral_add hB hpt]
    congr 1
    ext α
    ring
  have hsecond : (∫ α in M0, e α * (p α * t α)) =
      (∫ α in M0, e α * (s α * t α)) +
      (∫ α in M0, e α * ((p α - s α) * t α)) := by
    rw [← integral_add hst hD]
    congr 1
    ext α
    ring
  rw [hfirst, ← hsplit, hsecond]
  ring

/-- Page 6 display 22 for j equal to one: partial summation gives the
geometric bound on any prime window whose lower endpoint is at least three. -/
theorem T1_geometric_bound {X Y : ℝ} (hlo : 3 ≤ X - Y) (β : ℝ) :
    ‖T1 X Y β‖ ≤ LeanLab.PNTPort.Vinogradov.G ((primeWindow X Y).card : ℝ) β := by
  let L : ℕ := ⌈X - Y⌉₊
  let N : ℕ := ⌈X⌉₊ - L
  let w : ℕ → ℝ := fun j => 1 / Real.log ((L + j : ℕ) : ℝ)
  have hL3 : (3 : ℝ) ≤ L := hlo.trans (Nat.le_ceil _)
  have hLj (j : ℕ) : (3 : ℝ) ≤ (L + j : ℕ) := by
    push_cast
    exact hL3.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hlog (j : ℕ) : 1 ≤ Real.log ((L + j : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith [hLj j])]
    exact Real.exp_one_lt_three.le.trans (hLj j)
  have hw0 (j : ℕ) : 0 ≤ w j := by dsimp [w]; positivity
  have hw : Antitone w := by
    intro i j hij
    apply one_div_le_one_div_of_le
    · linarith [hlog i]
    · apply Real.log_le_log
      · linarith [hLj i]
      · exact_mod_cast Nat.add_le_add_left hij L
  have hgeom := Task674.norm_weighted_linear_phase_le w N (L - 1) β hw hw0
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith)
  have hphase (j : ℕ) :
      LeanLab.PNTPort.LargeSieve.e ((((L - 1 + 1 : ℕ) : ℝ) * β + (j : ℝ) * β)) =
      fourier ((L + j : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [Task556d.fourier_nat_eq_e, Nat.sub_add_cancel hL1]
    congr 1
    push_cast
    ring
  simp_rw [hphase] at hgeom
  have heq : T1 X Y β = ∑ j ∈ Finset.range N, w j •
      fourier ((L + j : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    unfold T1
    rw [Task556d.primeWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
    rfl
  rw [heq]
  have hw1 : w 0 ≤ 1 := by
    dsimp [w]
    exact (one_div_le_one_div_of_le (by norm_num) (hlog 0)).trans (by norm_num)
  have hcard : ((primeWindow X Y).card : ℝ) = (N : ℝ) := by
    rw [Task556d.primeWindow_eq_Ico, Nat.card_Ico]
  rw [hcard]
  exact hgeom.trans (by
    simpa using mul_le_mul_of_nonneg_right hw1
      (LeanLab.PNTPort.Vinogradov.G_nonneg (Nat.cast_nonneg N) β))

/-- Page 6 display 22: distance to the nearest integer is the absolute
value on the centered half period. -/
theorem dist0_eq_abs_of_abs_le_half {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    LeanLab.PNTPort.LargeSieve.dist0 β = |β| := by
  by_cases h : β = 1 / 2
  · subst β
    norm_num [LeanLab.PNTPort.LargeSieve.dist0, round_eq]
  · have hr : round β = 0 := round_eq_zero_iff.mpr
      ⟨(abs_le.mp hβ).1, lt_of_le_of_ne (abs_le.mp hβ).2 h⟩
    simp [LeanLab.PNTPort.LargeSieve.dist0, hr]

/-- Page 6 display 22 for j equal to one on a single prime window.
The geometric bound and the trivial cardinal bound give the stated decay. -/
theorem T1_decay_bound {X Y : ℝ} (hlo : 3 ≤ X - Y) (hY : 1 ≤ Y)
    {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    ‖T1 X Y β‖ ≤ 4 * Y / (1 + Y * |β|) := by
  have hgeom := T1_geometric_bound hlo β
  have hcard := Task556d.primeWindow_card_le (by linarith : 0 ≤ X - Y) hY
  have htriv : ‖T1 X Y β‖ ≤ 2 * Y := hgeom.trans
    ((LeanLab.PNTPort.Vinogradov.G_le _ _).trans hcard)
  have hweight : ‖T1 X Y β‖ * |β| ≤ 1 / 2 := by
    by_cases hz : |β| = 0
    · rw [hz, mul_zero]
      norm_num
    · have hpos : 0 < |β| := lt_of_le_of_ne (abs_nonneg β) (Ne.symm hz)
      have hdist : 0 < LeanLab.PNTPort.LargeSieve.dist0 β := by
        rwa [dist0_eq_abs_of_abs_le_half hβ]
      have h := hgeom.trans (LeanLab.PNTPort.Vinogradov.G_le_inv hdist)
      rw [dist0_eq_abs_of_abs_le_half hβ] at h
      have hmul := (le_div_iff₀ (by positivity : 0 < 2 * |β|)).mp h
      nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 1 + Y * |β|)).mpr
  calc
    ‖T1 X Y β‖ * (1 + Y * |β|) = ‖T1 X Y β‖ + Y * (‖T1 X Y β‖ * |β|) := by ring
    _ ≤ 2 * Y + Y * (1 / 2) := add_le_add htriv
      (mul_le_mul_of_nonneg_left hweight (by linarith))
    _ ≤ 4 * Y := by linarith

/-- LEAF: P0088 page 6 display 22 for j = 1, from display 21 for f1 = 1/log u by
partial summation against the geometric sum bound min(Y, 1/(2|beta|)). -/
theorem T1_bound : T1BoundProp := by
  intro ε hε hε'
  have hθ : 0 < (7 / 12 + ε / 2 : ℝ) := by linarith
  have hθ' : 0 < (1 - (7 / 12 + ε / 2) : ℝ) := by linarith
  have hlarge : ∀ᶠ X : ℝ in Filter.atTop,
      4 ≤ windowY X ε ∧ 2 ≤ X ^ (1 - (7 / 12 + ε / 2)) ∧ 3 ≤ X :=
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop hθ').eventually_ge_atTop 2).and
        (Filter.eventually_ge_atTop 3))
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨4, X0, by norm_num, ?_⟩
  intro X hX β hβ
  obtain ⟨hY4, hratio, hX3⟩ := hX0 X hX
  have hX0' : 0 < X := by linarith
  have hXY : X = windowY X ε * X ^ (1 - (7 / 12 + ε / 2)) := by
    rw [windowY, ← Real.rpow_add hX0']
    ring_nf
    rw [Real.rpow_one]
  have hlo : 3 ≤ X - windowY X ε := by nlinarith
  exact T1_decay_bound hlo (by linarith) hβ

/-- PROVED. For eps at most 7/18 the window Y = X^(7/12 + eps/2) is at least one
when X is at least one. -/
theorem windowY_ge_one {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) : 1 ≤ windowY X ε :=
  Real.one_le_rpow hX (by linarith)

/-- PROVED. The split at Y |beta| = 1 behind display 22: a bound a Y^s in the
range Y |beta| at most one and b Y^s / (Y |beta|) beyond it give
(2a + 2b) Y^s / (1 + Y |beta|). -/
theorem split_bound {N W Y β a b : ℝ} (hY : 0 < Y) (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (h1 : Y * |β| ≤ 1 → N ≤ a * W) (h2 : 1 < Y * |β| → N ≤ b * W / (Y * |β|)) :
    N ≤ (2 * a + 2 * b) * W / (1 + Y * |β|) := by
  have hYb : 0 ≤ Y * |β| := mul_nonneg hY.le (abs_nonneg β)
  have hden : 0 < 1 + Y * |β| := by linarith
  rw [le_div_iff₀ hden]
  by_cases hc : Y * |β| ≤ 1
  · have := h1 hc
    nlinarith [mul_nonneg hb hW, mul_nonneg ha hW, mul_nonneg (mul_nonneg hb hW) hYb]
  · have hc' : 1 < Y * |β| := lt_of_not_ge hc
    have hpos : 0 < Y * |β| := by linarith
    have := h2 hc'
    rw [le_div_iff₀ hpos] at this
    nlinarith [mul_nonneg ha hW, mul_nonneg hb hW, mul_nonneg (mul_nonneg ha hW) hYb]

/-- PROVED. A trigonometric polynomial with coefficients w is bounded by the sum of
the norms of its coefficients. -/
theorem trig_norm_le (S : Finset ℕ) (w : ℕ → ℂ) (k : ℕ → ℤ) (x : AddCircle (1 : ℝ)) :
    ‖∑ m ∈ S, w m * fourier (k m) x‖ ≤ ∑ m ∈ S, ‖w m‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have h1 : ‖fourier (k m) x‖ = 1 := Circle.norm_coe _
  rw [norm_mul, h1, mul_one]

/-- Helper for display 54, page 16, proved 2026-11-12 PROVE PASS: the integral
term of f2 on page 15 is nonnegative and at most log of sqrt u over z0 divided by
log z0 times log sqrt u, since log t is at least log z0 and log of u over t is at
least log sqrt u on the range of integration. AI wrote the Lean code. -/
private theorem f2_integral_bound {a u : ℝ} (ha : 1 < a) (hab : a ≤ Real.sqrt u) :
    0 ≤ ∫ t in a..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) ∧
    ∫ t in a..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) ≤
      (1 / (Real.log a * Real.log (Real.sqrt u))) * Real.log (Real.sqrt u / a) := by
  have hb1 : 1 < Real.sqrt u := lt_of_lt_of_le ha hab
  have hu0 : 0 < u := by
    by_contra h; push Not at h; rw [Real.sqrt_eq_zero'.mpr h] at hb1; linarith
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log (Real.sqrt u) := Real.log_pos hb1
  have key : ∀ t ∈ Set.Icc a (Real.sqrt u), 0 < t ∧ Real.log a ≤ Real.log t ∧
      Real.log (Real.sqrt u) ≤ Real.log (u / t) := by
    intro t ⟨h1, h2⟩
    have ht : 0 < t := by linarith
    refine ⟨ht, Real.log_le_log (by linarith) h1, Real.log_le_log (by linarith) ?_⟩
    rw [le_div_iff₀ ht]; nlinarith
  have hcont : ContinuousOn (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      (Set.uIcc a (Real.sqrt u)) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul (ContinuousOn.mul continuousOn_id ?_) ?_
      · exact Real.continuousOn_log.mono (fun t ht => by
          have := (key t ht).1; simp; linarith)
      · apply ContinuousOn.log (continuousOn_const.div continuousOn_id
          (fun t ht => ((key t ht).1).ne')) (fun t ht => ?_)
        exact div_ne_zero hu0.ne' (key t ht).1.ne'
    · intro t ht
      obtain ⟨h0, h1, h2⟩ := key t ht
      have : 0 < t * Real.log t * Real.log (u / t) := by
        have := lt_of_lt_of_le hla h1; have := lt_of_lt_of_le hlb h2; positivity
      exact this.ne'
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      MeasureTheory.volume a (Real.sqrt u) := hcont.intervalIntegrable
  refine ⟨intervalIntegral.integral_nonneg hab (fun t ht => ?_), ?_⟩
  · obtain ⟨h0, h1, h2⟩ := key t ht
    have := lt_of_lt_of_le hla h1; have := lt_of_lt_of_le hlb h2; positivity
  · rw [← integral_one_div_of_pos (by linarith) (by linarith), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hint
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro t ht; exact ((key t ht).1).ne'
    · intro t ht
      obtain ⟨h0, h1, h2⟩ := key t ht
      rw [one_div_mul_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have : Real.log a * Real.log (Real.sqrt u) ≤ Real.log t * Real.log (u / t) :=
        mul_le_mul h1 h2 hlb.le (by linarith)
      nlinarith

/-- `‖e x - e y‖ ≤ 2π|x - y|`. -/
private lemma norm_e_sub_le (x y : ℝ) :
    ‖LeanLab.PNTPort.LargeSieve.e x - LeanLab.PNTPort.LargeSieve.e y‖ ≤ 2 * π * |x - y| := by
  have h1 : LeanLab.PNTPort.LargeSieve.e x - LeanLab.PNTPort.LargeSieve.e y =
      LeanLab.PNTPort.LargeSieve.e y * (LeanLab.PNTPort.LargeSieve.e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    ring_nf
  rw [h1, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
  have h2 : LeanLab.PNTPort.LargeSieve.e (x - y) - 1 =
      Complex.exp (I * ((2 * π * (x - y) : ℝ) : ℂ)) - 1 := rfl
  rw [h2, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h3 : 2 * π * (x - y) / 2 = π * (x - y) := by ring
  rw [h3, Real.norm_eq_abs, abs_mul]
  have h4 : |(2 : ℝ)| = 2 := by norm_num
  rw [h4]
  have hs := Real.abs_sin_le_abs (x := π * (x - y))
  have hp : (0 : ℝ) ≤ π := pi_pos.le
  calc 2 * |Real.sin (π * (x - y))| ≤ 2 * |π * (x - y)| := by linarith
    _ = 2 * π * |x - y| := by rw [abs_mul, abs_of_nonneg hp]; ring

/-- On `(0, 2/3]` one has `2t ≤ ‖e t - 1‖`. -/
private lemma two_mul_le_norm_e_sub_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 2 / 3) :
    2 * t ≤ ‖LeanLab.PNTPort.LargeSieve.e t - 1‖ := by
  have hdist : t / 2 ≤ LeanLab.PNTPort.LargeSieve.dist0 t := by
    have hmin := LeanLab.PNTPort.Vinogradov.dist0_ge (x := t) (y := 0) (t := 0) h0.le
      (by linarith)
    simp only [abs_zero, sub_zero, add_zero, Int.cast_zero] at hmin
    rcases le_or_gt t (1 - t) with h | h
    · rw [min_eq_left h] at hmin; linarith
    · rw [min_eq_right h.le] at hmin; linarith
  have h4 := LeanLab.PNTPort.LargeSieve.four_dist0_le t
  linarith

private lemma inv_sub_inv_eq (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    y⁻¹ - x⁻¹ = (x - y) / (x * y) := by
  field_simp

/-- Kusmin-Landau: a sum `∑_{j<N} e(θ j)` whose first differences are increasing and
lie in `[δ, 4δ] ⊂ (0, 2/3]` is at most `6/δ`. -/
private theorem sum_e_le_of_mono_steps {θ : ℕ → ℝ} {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ j, j < N → 0 < θ (j + 1) - θ j)
    (hup : ∀ j, j < N → θ (j + 1) - θ j ≤ 2 / 3)
    (hlo : ∀ j, j < N → δ ≤ θ (j + 1) - θ j)
    (hhi : ∀ j, j < N → θ (j + 1) - θ j ≤ 4 * δ)
    (hmono : ∀ j, j + 1 < N → θ (j + 1) - θ j ≤ θ (j + 2) - θ (j + 1)) :
    ‖∑ j ∈ Finset.range N, LeanLab.PNTPort.LargeSieve.e (θ j)‖ ≤ 8 / δ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  set Δ : ℕ → ℝ := fun j => θ (j + 1) - θ j with hΔdef
  set z : ℕ → ℂ := fun j => LeanLab.PNTPort.LargeSieve.e (θ j) with hzdef
  set c : ℕ → ℂ := fun j => (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1)⁻¹ with hcdef
  have hΔpos : ∀ j, j < N → 0 < Δ j := fun j hj => hpos j hj
  have hΔup : ∀ j, j < N → Δ j ≤ 2 / 3 := fun j hj => hup j hj
  have hΔlo : ∀ j, j < N → δ ≤ Δ j := fun j hj => hlo j hj
  have hΔhi : ∀ j, j < N → Δ j ≤ 4 * δ := fun j hj => hhi j hj
  have hΔmono : ∀ j, j + 1 < N → Δ j ≤ Δ (j + 1) := fun j hj => hmono j hj
  have hzn : ∀ j, ‖z j‖ = 1 := fun j => LeanLab.PNTPort.LargeSieve.norm_e (θ j)
  have hxlow : ∀ j, j < N → 2 * δ ≤ ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖ := by
    intro j hj
    have h1 := two_mul_le_norm_e_sub_one (hΔpos j hj) (hΔup j hj)
    have h2 := hΔlo j hj
    linarith
  have hxne : ∀ j, j < N → LeanLab.PNTPort.LargeSieve.e (Δ j) - 1 ≠ 0 := by
    intro j hj h
    have h1 := hxlow j hj
    rw [h, norm_zero] at h1
    linarith
  have hkey : ∀ j, j < N → z j = c j * (z (j + 1) - z j) := by
    intro j hj
    have hstep : z (j + 1) = z j * LeanLab.PNTPort.LargeSieve.e (Δ j) := by
      show LeanLab.PNTPort.LargeSieve.e (θ (j + 1)) =
        LeanLab.PNTPort.LargeSieve.e (θ j) * LeanLab.PNTPort.LargeSieve.e (Δ j)
      rw [← LeanLab.PNTPort.LargeSieve.e_add]
      congr 1
      simp only [hΔdef]
      ring
    rw [hstep]
    show z j = (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1)⁻¹ *
      (z j * LeanLab.PNTPort.LargeSieve.e (Δ j) - z j)
    rw [show z j * LeanLab.PNTPort.LargeSieve.e (Δ j) - z j
      = (LeanLab.PNTPort.LargeSieve.e (Δ j) - 1) * z j by ring,
      ← mul_assoc, inv_mul_cancel₀ (hxne j hj), one_mul]
  have htele : ∀ n : ℕ,
      ∑ j ∈ Finset.range (n + 1), c j * (z (j + 1) - z j) =
        c n * z (n + 1) - c 0 * z 0 -
          ∑ j ∈ Finset.range n, (c (j + 1) - c j) * z (j + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  have hsum_eq : ∑ j ∈ Finset.range N, z j =
      c (N - 1) * z N - c 0 * z 0 -
        ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1) := by
    have h := htele (N - 1)
    rw [Nat.sub_add_cancel hN] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j hj => hkey j (Finset.mem_range.mp hj)
  have hcbd : ∀ j, j < N → ‖c j‖ ≤ 1 / (2 * δ) := by
    intro j hj
    have h1 := hxlow j hj
    have h2 : ‖c j‖ = (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖)⁻¹ := by
      simp only [hcdef, norm_inv]
    rw [h2]
    have := inv_anti₀ (by linarith : (0 : ℝ) < 2 * δ) h1
    calc (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖)⁻¹ ≤ (2 * δ)⁻¹ := this
      _ = 1 / (2 * δ) := by rw [one_div]
  have hcdiff : ∀ j, j + 1 < N →
      ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
        (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) := by
    intro j hj
    rw [norm_mul, hzn, mul_one]
    have hle : Δ j ≤ Δ (j + 1) := hΔmono j hj
    have halg : c (j + 1) - c j =
        (LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))) /
          ((LeanLab.PNTPort.LargeSieve.e (Δ j) - 1) *
            (LeanLab.PNTPort.LargeSieve.e (Δ (j + 1)) - 1)) := by
      simp only [hcdef]
      rw [inv_sub_inv_eq _ _ (hxne j (by omega)) (hxne (j + 1) hj)]
      ring_nf
    rw [halg, norm_div, norm_mul]
    have hn : ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))‖
        ≤ 2 * π * (Δ (j + 1) - Δ j) := by
      have h := norm_e_sub_le (Δ j) (Δ (j + 1))
      have habs : |Δ j - Δ (j + 1)| = Δ (j + 1) - Δ j := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs] at h
      exact h
    have hd1 := hxlow j (by omega)
    have hd2 := hxlow (j + 1) hj
    have hstep : ‖LeanLab.PNTPort.LargeSieve.e (Δ j) - LeanLab.PNTPort.LargeSieve.e (Δ (j + 1))‖ /
        (‖LeanLab.PNTPort.LargeSieve.e (Δ j) - 1‖ *
          ‖LeanLab.PNTPort.LargeSieve.e (Δ (j + 1)) - 1‖) ≤
        (2 * π * (Δ (j + 1) - Δ j)) / ((2 * δ) * (2 * δ)) := by
      apply div_le_div₀ (by positivity) hn (by positivity)
      exact mul_le_mul hd1 hd2 (by linarith) (by positivity)
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have htelesc : ∑ j ∈ Finset.range (N - 1), (Δ (j + 1) - Δ j) = Δ (N - 1) - Δ 0 :=
    Finset.sum_range_sub Δ (N - 1)
  have htail : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
      (3 * π / 2) / δ := by
    have h1 : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤
        ∑ j ∈ Finset.range (N - 1), (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) :=
      Finset.sum_le_sum fun i hi => hcdiff i (by have := Finset.mem_range.mp hi; omega)
    have h2 : ∑ j ∈ Finset.range (N - 1), (π / 2) / δ ^ 2 * (Δ (j + 1) - Δ j) =
        (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) := by
      rw [← Finset.mul_sum, htelesc]
    have h3 : Δ (N - 1) - Δ 0 ≤ 3 * δ := by
      have h1 := hΔhi (N - 1) (by omega)
      have h2 := hΔlo 0 hN
      linarith
    have h4 : (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) ≤ (3 * π / 2) / δ := by
      have h1 : (π / 2) / δ ^ 2 * (Δ (N - 1) - Δ 0) ≤ (π / 2) / δ ^ 2 * (3 * δ) := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
      have h2 : (π / 2) / δ ^ 2 * (3 * δ) = (3 * π / 2) / δ := by
        field_simp
      linarith
    linarith
  have hN1 : ‖c (N - 1)‖ ≤ 1 / (2 * δ) := hcbd (N - 1) (by omega)
  have h0b : ‖c 0‖ ≤ 1 / (2 * δ) := hcbd 0 hN
  have hzN : ‖z N‖ = 1 := hzn N
  have hz0 : ‖z 0‖ = 1 := hzn 0
  rw [hsum_eq]
  have htri : ‖c (N - 1) * z N - c 0 * z 0 -
      ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
      ‖c (N - 1)‖ + ‖c 0‖ + ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ := by
    have ha : ‖c (N - 1) * z N - c 0 * z 0 -
        ∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
        ‖c (N - 1) * z N - c 0 * z 0‖ +
          ‖∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ := norm_sub_le _ _
    have hb : ‖c (N - 1) * z N - c 0 * z 0‖ ≤ ‖c (N - 1)‖ + ‖c 0‖ := by
      have := norm_sub_le (c (N - 1) * z N) (c 0 * z 0)
      rwa [norm_mul, norm_mul, hzN, hz0, mul_one, mul_one] at this
    have hc : ‖∑ j ∈ Finset.range (N - 1), (c (j + 1) - c j) * z (j + 1)‖ ≤
        ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ := norm_sum_le _ _
    linarith
  have hfin : ‖c (N - 1)‖ + ‖c 0‖ +
      ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤ 8 / δ := by
    have h1 : 1 / (2 * δ) + 1 / (2 * δ) = 1 / δ := by field_simp; norm_num
    have h2 : 3 * π / 2 / δ ≤ 6 / δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      nlinarith [pi_lt_four]
    have hB : ∑ j ∈ Finset.range (N - 1), ‖(c (j + 1) - c j) * z (j + 1)‖ ≤ 6 / δ :=
      htail.trans h2
    have hC : 1 / δ + 6 / δ ≤ 8 / δ := by
      have h7 : (7 : ℝ) / δ ≤ 8 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
      have he : 1 / δ + 6 / δ = (7 : ℝ) / δ := by field_simp; norm_num
      rw [he]
      exact h7
    linarith
  linarith

/-- Abel: a monotone nonnegative weight against a sequence whose partial sums are
bounded by `B` costs twice the last weight times `B`. -/
private theorem norm_sum_mono_weight_le {f : ℕ → ℂ} {w : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (hw0 : ∀ j, 0 ≤ w j) (hmono : ∀ j, j < N → w j ≤ w (j + 1))
    (hB : ∀ k, k ≤ N → ‖∑ j ∈ Finset.range k, f j‖ ≤ B) :
    ‖∑ j ∈ Finset.range N, (w j : ℂ) * f j‖ ≤ 2 * w (N - 1) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    have h1 := hw0 0
    nlinarith
  set A : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, f j with hA
  have hid : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (w j : ℂ) * f j =
      (w n : ℂ) * A (n + 1) +
        ∑ j ∈ Finset.range n, ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, hA]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hf : f (m + 1) = A (m + 2) - A (m + 1) := by
        simp only [hA, Finset.sum_range_succ]
        ring
      rw [hf]
      ring
  have hid2 := hid (N - 1)
  rw [Nat.sub_add_cancel hN] at hid2
  rw [hid2]
  have h1 : ‖(w (N - 1) : ℂ) * A N‖ ≤ w (N - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 (N - 1))]
    exact mul_le_mul_of_nonneg_left (hB N le_rfl) (hw0 (N - 1))
  have h2 : ‖∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ ≤
      (w (N - 1) - w 0) * B := by
    have hterm : ∀ j ∈ Finset.range (N - 1),
        ‖((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ ≤ (w (j + 1) - w j) * B := by
      intro j hj
      have hjN : j < N := by
        have := Finset.mem_range.mp hj
        omega
      have hle := hmono j hjN
      have he : ((w j : ℂ) - (w (j + 1) : ℂ)) = ((w j - w (j + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : w j - w (j + 1) ≤ 0), neg_sub]
      exact mul_le_mul_of_nonneg_left (hB (j + 1) (by omega)) (by linarith)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
    rw [← Finset.sum_mul, Finset.sum_range_sub w (N - 1)]
  have h3 : (w (N - 1) - w 0) ≤ w (N - 1) := by
    have := hw0 0
    linarith
  have h4 : 0 ≤ w (N - 1) := hw0 _
  calc ‖(w (N - 1) : ℂ) * A N +
        ∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖
      ≤ ‖(w (N - 1) : ℂ) * A N‖ +
        ‖∑ j ∈ Finset.range (N - 1), ((w j : ℂ) - (w (j + 1) : ℂ)) * A (j + 1)‖ :=
        norm_add_le _ _
    _ ≤ w (N - 1) * B + (w (N - 1) - w 0) * B := add_le_add h1 h2
    _ ≤ 2 * w (N - 1) * B := by nlinarith

private lemma sqrt_lt_self' {u : ℝ} (h1 : 1 < u) : Real.sqrt u < u := by
  have hpos : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
  nlinarith

private lemma hasDerivAt_f2antideriv {z0 u t : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u)
    (ht : t ∈ Set.uIcc z0 (Real.sqrt u)) :
    HasDerivAt (fun s => Real.log (Real.log s / (Real.log u - Real.log s)) / Real.log u)
      (1 / (t * Real.log t * Real.log (u / t))) t := by
  have hz0pos : 0 < z0 := by linarith
  have htsqrt : z0 ≤ Real.sqrt u := by
    calc z0 = Real.sqrt (z0 ^ 2) := (Real.sqrt_sq hz0pos.le).symm
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hz0u
  have hu1 : 1 < u := by nlinarith
  have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
  obtain ⟨ht1, ht2⟩ := htI
  have htpos : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hloglt : Real.log t < Real.log u := by
    apply Real.log_lt_log htpos
    exact lt_of_le_of_lt ht2 (sqrt_lt_self' hu1)
  have hdiff : 0 < Real.log u - Real.log t := by linarith
  have hldiv : Real.log (u / t) = Real.log u - Real.log t :=
    Real.log_div (by linarith) (ne_of_gt htpos)
  have h1 : HasDerivAt (fun s => Real.log s) (1 / t) t := by
    simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt htpos)
  have h2 : HasDerivAt (fun s => Real.log u - Real.log s) (-(1 / t)) t := by
    have h := (hasDerivAt_const (x := t) (c := Real.log u)).sub h1
    convert h using 1
    ring
  have h3 : HasDerivAt (fun s => Real.log s / (Real.log u - Real.log s))
      ((1 / t * (Real.log u - Real.log t) - Real.log t * (-(1 / t))) /
        (Real.log u - Real.log t) ^ 2) t :=
    h1.div h2 (ne_of_gt hdiff)
  have h4 : HasDerivAt (fun s => Real.log (Real.log s / (Real.log u - Real.log s)))
      (((1 / t * (Real.log u - Real.log t) - Real.log t * (-(1 / t))) /
        (Real.log u - Real.log t) ^ 2) / (Real.log t / (Real.log u - Real.log t))) t :=
    h3.log (by positivity)
  have h5 := h4.const_mul ((Real.log u)⁻¹)
  have hfun : (fun s => Real.log (Real.log s / (Real.log u - Real.log s)) / Real.log u)
      = fun y => (Real.log u)⁻¹ * Real.log (Real.log y / (Real.log u - Real.log y)) := by
    funext s
    ring
  rw [hfun]
  convert h5 using 1
  rw [hldiv]
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  field_simp
  ring

private theorem f2_integral_closed {z0 u : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u) :
    ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
      = Real.log ((Real.log u - Real.log z0) / Real.log z0) / Real.log u := by
  have hz0pos : 0 < z0 := by linarith
  have hu1 : 1 < u := by nlinarith
  have htsqrt : z0 ≤ Real.sqrt u := by
    calc z0 = Real.sqrt (z0 ^ 2) := (Real.sqrt_sq hz0pos.le).symm
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt hz0u
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t * Real.log (u / t)))
      volume z0 (Real.sqrt u) := by
    have hlogc : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc z0 (Real.sqrt u)) :=
      Real.continuousOn_log.mono (by
        intro t ht
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ne_of_gt (by linarith [htsqrt, hz0pos])
        · exact ne_of_gt (by linarith [htsqrt, hz0pos]))
    have hcont : ContinuousOn (fun t => 1 / (t * Real.log t * (Real.log u - Real.log t)))
        (Set.uIcc z0 (Real.sqrt u)) := by
      apply ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_id.mul hlogc).mul (continuousOn_const.sub hlogc)
      · intro t ht
        have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
          rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, h2⟩
          · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
        have htpos : 0 < t := by linarith [htI.1]
        have hloglt : Real.log t < Real.log u :=
          Real.log_lt_log htpos (lt_of_le_of_lt htI.2 (sqrt_lt_self' hu1))
        have hlogt : 0 < Real.log t := Real.log_pos (by linarith [htI.1])
        have h3 : 0 < Real.log u - Real.log t := by linarith
        apply ne_of_gt
        have : 0 < t * Real.log t * (Real.log u - Real.log t) := by positivity
        exact this
    refine (hcont.congr ?_).intervalIntegrable
    intro t ht
    simp only
    rw [Real.log_div (ne_of_gt (by linarith [htsqrt, hz0pos])) (by
      have htI : z0 ≤ t ∧ t ≤ Real.sqrt u := by
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨htsqrt.trans h1, h2.trans htsqrt⟩
      have : 0 < t := by linarith [htI.1]
      linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_f2antideriv hz0 hz0u ht) hint]
  have hlogsqrt : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt (by linarith)
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  have ha : Real.log z0 ≠ 0 := ne_of_gt (Real.log_pos hz0)
  have htop : Real.log (Real.log (Real.sqrt u) / (Real.log u - Real.log (Real.sqrt u))) = 0 := by
    rw [hlogsqrt, show Real.log u - Real.log u / 2 = Real.log u / 2 by ring,
      div_self (by positivity)]
    simp
  have hA : Real.log (Real.log (Real.sqrt u) / (Real.log u - Real.log (Real.sqrt u))) /
      Real.log u = 0 := by rw [htop, zero_div]
  have hpos' : 0 < Real.log u - Real.log z0 := by
    have h3 : 0 < Real.log z0 := Real.log_pos hz0
    have hsq : Real.log (z0 ^ 2) ≤ Real.log u := Real.log_le_log (by positivity) hz0u
    rw [Real.log_pow] at hsq
    norm_num at hsq
    linarith
  have hG : Real.log (Real.log z0 / (Real.log u - Real.log z0)) / Real.log u =
      -(Real.log ((Real.log u - Real.log z0) / Real.log z0) / Real.log u) := by
    have hinv : Real.log z0 / (Real.log u - Real.log z0) =
        ((Real.log u - Real.log z0) / Real.log z0)⁻¹ := by
      field_simp
    rw [hinv, Real.log_inv]
    ring
  rw [hA, zero_sub, hG]
  ring

/-- The weight `f2` of P0088 page 15 in closed form. -/
private theorem f2Weight_eq {z0 u : ℝ} (hz0 : 1 < z0) (hz0u : z0 ^ 2 ≤ u) :
    f2Weight z0 u =
      (1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) / Real.log u := by
  have hu1 : 1 < u := by nlinarith
  have hLu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu1)
  unfold f2Weight
  rw [f2_integral_closed hz0 hz0u]
  field_simp

/-- `(1 + log r)/(1 + r)` is increasing on `[1, 3/2]`. -/
private lemma mono_ratio_log :
    MonotoneOn (fun r : ℝ => (1 + Real.log r) / (1 + r)) (Set.Icc 1 (3 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · -- continuity
    have hlogc : ContinuousOn (fun r : ℝ => Real.log r) (Set.Icc (1:ℝ) (3/2)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        exact ne_of_gt (by linarith [hx.1]))
    exact (continuousOn_const.add hlogc).div (by fun_prop) (by
      intro x hx
      linarith [hx.1])
  · -- differentiability on the interior
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hxpos : 0 < x := by linarith
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · exact (differentiableAt_const _).add (Real.differentiableAt_log (ne_of_gt hxpos))
    · exact differentiableAt_id.const_add 1
    · linarith
  · -- nonnegative derivative
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hxpos : 0 < x := by linarith
    have hdif2 : DifferentiableAt ℝ (fun r : ℝ => (1 + Real.log r)) x := by fun_prop
    have hdif3 : DifferentiableAt ℝ (fun r : ℝ => (1 + r)) x := by fun_prop
    have hden : (1 + x) ≠ 0 := by linarith
    have hderiv : deriv (fun r : ℝ => (1 + Real.log r) / (1 + r)) x
        = ((1 / x) * (1 + x) - (1 + Real.log x)) / (1 + x) ^ 2 := by
      change deriv ((fun r : ℝ => 1 + Real.log r) / (fun r : ℝ => 1 + r)) x = _
      rw [deriv_div hdif2 hdif3 hden]
      simp only [one_div]
      norm_num
    rw [hderiv]
    have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
    have hxle : x ≤ 3 / 2 := by linarith
    have hxge : 1 ≤ x := by linarith
    have hinv : 1 / x ≥ 2 / 3 := by
      rw [ge_iff_le, le_div_iff₀ hxpos]
      nlinarith
    have hkey : 0 ≤ (1 / x) * (1 + x) - (1 + Real.log x) := by nlinarith
    exact div_nonneg hkey (by positivity)

/-- The weight of `T2` is nondecreasing in the argument on the block window. -/
private theorem f2Weight_mono {z0 u v : ℝ} (hz0 : 1 < z0) (hu : z0 ^ 2 ≤ u) (huv : u ≤ v)
    (hv : Real.log v ≤ 5 / 2 * Real.log z0) : f2Weight z0 u ≤ f2Weight z0 v := by
  have hz0pos : 0 < z0 := by linarith
  have ha : 0 < Real.log z0 := Real.log_pos hz0
  have hu1 : 1 < u := by nlinarith
  have hv1 : 1 < v := by linarith
  have hz0v : z0 ^ 2 ≤ v := le_trans hu huv
  have hL1 : 2 * Real.log z0 ≤ Real.log u := by
    have hsq : Real.log (z0 ^ 2) ≤ Real.log u := Real.log_le_log (by positivity) hu
    rw [Real.log_pow] at hsq
    norm_num at hsq
    linarith
  have hL12 : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  rw [f2Weight_eq hz0 hu, f2Weight_eq hz0 hz0v]
  have e1 : (1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) / Real.log u =
      (1 / Real.log z0) * ((1 + Real.log ((Real.log u - Real.log z0) / Real.log z0)) /
        (1 + ((Real.log u - Real.log z0) / Real.log z0))) := by
    have h1 : 1 + (Real.log u - Real.log z0) / Real.log z0 = Real.log u / Real.log z0 := by
      field_simp
      ring
    rw [h1]
    field_simp
  have e2 : (1 + Real.log ((Real.log v - Real.log z0) / Real.log z0)) / Real.log v =
      (1 / Real.log z0) * ((1 + Real.log ((Real.log v - Real.log z0) / Real.log z0)) /
        (1 + ((Real.log v - Real.log z0) / Real.log z0))) := by
    have h1 : 1 + (Real.log v - Real.log z0) / Real.log z0 = Real.log v / Real.log z0 := by
      field_simp
      ring
    rw [h1]
    field_simp
  rw [e1, e2]
  have hr1 : (1:ℝ) ≤ (Real.log u - Real.log z0) / Real.log z0 := by
    rw [le_div_iff₀ ha]
    linarith
  have hr2 : (Real.log v - Real.log z0) / Real.log z0 ≤ 3 / 2 := by
    rw [div_le_iff₀ ha]
    linarith
  have hrr : (Real.log u - Real.log z0) / Real.log z0 ≤ (Real.log v - Real.log z0) / Real.log z0 := by
    rw [div_le_div_iff_of_pos_right ha]
    linarith
  have hmem1 : (Real.log u - Real.log z0) / Real.log z0 ∈ Set.Icc (1:ℝ) (3/2) := ⟨hr1, hrr.trans hr2⟩
  have hmem2 : (Real.log v - Real.log z0) / Real.log z0 ∈ Set.Icc (1:ℝ) (3/2) :=
    ⟨hr1.trans hrr, hr2⟩
  have hmain := mono_ratio_log hmem1 hmem2 hrr
  have hpos : (0:ℝ) < 1 / Real.log z0 := by positivity
  exact mul_le_mul_of_nonneg_left hmain hpos.le

/-! ## T2_bound -/

/-- PROVED helper. P0088 page 6 display 22 for j = 2, the trivial bound. The weight f2 of
page 15 is bounded on the window of m between Y^(1/2)/2 and Y^(1/2), since its
integral term is at most log(log u^(1/2) / log z0) / log u, and the window holds at
most Y^(1/2) + 1 integers. -/
theorem T2_trivial :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ,
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤ C * Real.sqrt (windowY X ε) := by
  intro B hB ε hε hε'
  set M := max (Real.exp (1 / B)) (max ((55 * B) ^ 2) 100) with hMdef
  have hM100 : 100 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM4 : 4 ≤ M := by linarith
  refine ⟨4, Real.exp M, by norm_num, ?_⟩
  intro X hX β
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set L := Real.log X with hL
  have hLM : M ≤ L := by rw [← Real.log_exp M]; exact Real.log_le_log (Real.exp_pos _) hX
  have hL4 : 4 ≤ L := le_trans hM4 hLM
  have hLB : (55 * B) ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLM
  have hLe : Real.exp (1 / B) ≤ L := le_trans (le_max_left _ _) hLM
  have hLpos : 0 < L := by linarith
  set ℓ := Real.log L with hℓ
  have hℓB : 1 / B ≤ ℓ := by
    rw [← Real.log_exp (1 / B)]; exact Real.log_le_log (Real.exp_pos _) hLe
  have hBℓ : 1 ≤ B * ℓ := by
    rw [div_le_iff₀ hB] at hℓB; linarith
  have hℓpos : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  have hsqL : 55 * B ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hLB
    rwa [Real.sqrt_sq (by positivity)] at this
  have hℓsq : ℓ ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
    rw [Real.log_sqrt hLpos.le] at h1; linarith
  have hsqsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hkey : 2 * B * ℓ ≤ 7 * L / 96 := by
    have h1 := mul_le_mul_of_nonneg_left hℓsq (by positivity : (0:ℝ) ≤ 2 * B)
    have h2 := mul_le_mul_of_nonneg_right hsqL (Real.sqrt_nonneg L)
    nlinarith
  set e := 7 / 12 + ε / 2 with he
  have he7 : 7 / 12 ≤ e := by linarith
  have hYdef : windowY X ε = X ^ e := rfl
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hXpos _
  have hlogY : Real.log Y = e * L := by rw [hYdef]; exact Real.log_rpow hXpos e
  set P := L ^ B with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hLpos _
  have hlogP : Real.log P = B * ℓ := Real.log_rpow hLpos B
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) with hz0
  have hz0pos : 0 < z0 := by positivity
  have hlz : Real.log z0 = e * L / 4 - 2 * (B * ℓ) := by
    rw [hz0, Real.log_mul (by positivity) (by positivity), Real.log_rpow hYpos,
      Real.log_zpow, hlogY, hlogP]
    push_cast; ring
  have hlz8 : e * L / 8 ≤ Real.log z0 := by
    rw [hlz]; nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
  have hlz96 : 7 * L / 96 ≤ Real.log z0 := by
    nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
  have hlzpos : 0 < Real.log z0 := by linarith
  have hz1 : 1 < z0 := (Real.log_pos_iff hz0pos.le).mp hlzpos
  have hu : L ^ (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L
  have hsY : Real.log (Real.sqrt Y) = e * L / 2 := by
    rw [Real.log_sqrt hYpos.le, hlogY]
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hL100 : 100 ≤ L := hM100.trans hLM
  have per : ∀ m ∈ squareWindow Y, |f2Weight z0 (m : ℝ)| ≤ 2 := by
    intro v hv
    obtain ⟨_, hm2lo, hm2hi⟩ := Finset.mem_filter.mp hv
    set m : ℝ := (v : ℝ) with hm
    have hsYpos : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
    have hmpos : 0 < m := by linarith
    have hlmlo : e * L / 2 - Real.log 2 ≤ Real.log m := by
      have := Real.log_le_log (by positivity) hm2lo
      rwa [Real.log_div hsYpos.ne' (by norm_num), hsY] at this
    have hlmhi : Real.log m < e * L / 2 := by
      have := Real.log_lt_log hmpos hm2hi
      rwa [hsY] at this
    have hlm8 : 7 * L / 24 - 1 ≤ Real.log m := by
      nlinarith [mul_le_mul_of_nonneg_right he7 hLpos.le]
    have hlm1 : 1 ≤ Real.log m := by linarith
    have hlmpos : 0 < Real.log m := by linarith
    have hsm : Real.log (Real.sqrt m) = Real.log m / 2 := Real.log_sqrt hmpos.le
    have hsmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
    have hzle : z0 ≤ Real.sqrt m := by
      rw [← Real.log_le_log_iff hz0pos hsmpos, hsm, hlz]; linarith
    obtain ⟨hJ0, hJ1⟩ := f2_integral_bound (u := m) hz1 hzle
    have hlz1 : 1 ≤ Real.log z0 := by linarith
    have hsmLog : 0 < Real.log (Real.sqrt m) := by rw [hsm]; positivity
    have hratio : Real.log (Real.sqrt m / z0) ≤ Real.log (Real.sqrt m) := by
      rw [Real.log_div hsmpos.ne' hz0pos.ne']
      linarith
    have hJ2 : (∫ t in z0..Real.sqrt m, 1 / (t * Real.log t * Real.log (m / t))) ≤
        1 / Real.log z0 := by
      refine hJ1.trans ?_
      have hid : (1 / (Real.log z0 * Real.log (Real.sqrt m))) *
          Real.log (Real.sqrt m / z0) =
          Real.log (Real.sqrt m / z0) / (Real.log z0 * Real.log (Real.sqrt m)) := by ring
      rw [hid, div_le_div_iff₀ (mul_pos hlzpos hsmLog) hlzpos]
      nlinarith only [mul_le_mul_of_nonneg_right hratio hlzpos.le]
    have hmInv : 1 / Real.log m ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlm1
    have hzInv : 1 / Real.log z0 ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlz1
    change |1 / Real.log m + ∫ t in z0..Real.sqrt m,
      1 / (t * Real.log t * Real.log (m / t))| ≤ 2
    rw [abs_of_nonneg (add_nonneg (by positivity) hJ0)]
    linarith only [hmInv, hzInv, hJ2]
  have hcard : ((squareWindow Y).card : ℝ) ≤ Real.sqrt Y + 1 := by
    have h : (squareWindow Y).card ≤ ⌊Real.sqrt Y⌋₊ + 1 := by
      unfold squareWindow
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) ≤ Real.sqrt Y := Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ((squareWindow Y).card : ℝ) ≤ ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith [Real.add_one_le_exp M] : 1 ≤ X) (by linarith : 0 ≤ e)
  have hR1 : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.mpr hY1
  change ‖T2 Y P β‖ ≤ 4 * Real.sqrt Y
  refine (trig_norm_le (squareWindow Y) _ (fun m => ((m ^ 2 : ℕ) : ℤ)) _).trans ?_
  calc
    _ ≤ ∑ _m ∈ squareWindow Y, (2 : ℝ) := Finset.sum_le_sum fun m hm => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using per m hm
    _ = 2 * ((squareWindow Y).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * Real.sqrt Y := by linarith

set_option maxHeartbeats 4000000 in
/-- PROVED helper. P0088 page 6 display 22 for j = 2, the decay bound for 0 < |beta| at
most Y^(-1/2)/4: the Kuzmin Landau bound for the phase m^2 beta, whose
derivative 2 m beta is monotone with absolute value between Y^(1/2) |beta| and
1/2, and partial summation for the weight f2. -/
theorem T2_decay :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ β : ℝ, 0 < |β| →
        |β| ≤ 1 / (4 * Real.sqrt (windowY X ε)) →
        ‖T2 (windowY X ε) (Real.log X ^ B) β‖ ≤
          C / (Real.sqrt (windowY X ε) * |β|) := by
  intro B hB ε hε hε'
  refine ⟨32, Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B))),
    by norm_num, ?_⟩
  intro X hX β hβ hβd
  set L := Real.log X with hLdef
  have hX1 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hM1 : (400 * (B + 1)) ^ 2 ≤ L := by
    have h1 : Real.log (Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B)))) ≤
        Real.log X := Real.log_le_log (Real.exp_pos _) hX
    rw [Real.log_exp, ← hLdef] at h1
    exact le_trans (le_max_left _ _) h1
  have hM2 : Real.exp (Real.log 2 / B) ≤ L := by
    have h1 : Real.log (Real.exp (max ((400 * (B + 1)) ^ 2) (Real.exp (Real.log 2 / B)))) ≤
        Real.log X := Real.log_le_log (Real.exp_pos _) hX
    rw [Real.log_exp, ← hLdef] at h1
    exact le_trans (le_max_right _ _) h1
  have hB1 : (0:ℝ) < B + 1 := by linarith
  have hL1 : 1 ≤ L := by nlinarith
  have hL400 : 400 * (B + 1) ≤ Real.sqrt L := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 400 * (B + 1))]
    exact Real.sqrt_le_sqrt hM1
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  set ℓ := Real.log L with hℓdef
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]
    exact Real.log_nonneg hL1
  have hℓ2 : ℓ ≤ 2 * Real.sqrt L := by
    have h1 := Real.log_le_sub_one_of_pos hsqL
    rw [Real.log_sqrt (by linarith)] at h1
    rw [hℓdef]
    linarith
  have hBℓ : Real.log 2 ≤ B * ℓ := by
    have h := Real.log_le_log (Real.exp_pos _) hM2
    rw [Real.log_exp, div_le_iff₀ hB, ← hℓdef] at h
    simpa only [mul_comm] using h
  set ex := 7 / 12 + ε / 2 with hexdef
  have hex7 : 7 / 12 ≤ ex := by rw [hexdef]; linarith
  have hexpos : 0 < ex := by rw [hexdef]; linarith
  set Y := X ^ ex with hYdef
  have hYdef' : windowY X ε = Y := rfl
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hX1 ex
  have hlogY : Real.log Y = ex * L := by
    rw [hYdef, Real.log_rpow hX1, ← hLdef]
  have hsqY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hYpos
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hY2 : 2 ≤ Real.sqrt Y := by
    rw [← Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) hsqY, Real.log_sqrt hYpos.le, hlogY]
    nlinarith [hM1, hex7, hlog2le]
  set P := L ^ B with hPdef
  have hPpos : 0 < P := Real.rpow_pos_of_pos (by linarith) B
  have hlogP : Real.log P = B * ℓ := by
    rw [hPdef, Real.log_rpow (by linarith), ← hℓdef]
  have hP2 : 2 ≤ P := by
    rw [← Real.log_le_log_iff (by norm_num : (0:ℝ) < 2) hPpos, hlogP]
    linarith
  set z0 := Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) with hz0def
  have hz0pos : 0 < z0 := by
    rw [hz0def]
    exact mul_pos (Real.rpow_pos_of_pos hYpos _) (zpow_pos hPpos _)
  have hlogz0 : Real.log z0 = ex * L / 4 - 2 * (B * ℓ) := by
    rw [hz0def, Real.log_mul (Real.rpow_pos_of_pos hYpos _).ne' (zpow_pos hPpos _).ne',
      Real.log_rpow hYpos, Real.log_zpow, hlogY, hlogP]
    push_cast
    ring
  have hz0diff : 2 * (B * ℓ) ≤ ex * L / 40 := by
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
    have h4 : 160 * B ≤ ex * Real.sqrt L := by nlinarith [hL400, hex7, hB.le]
    have h5 : (160 * B) * Real.sqrt L ≤ ex * L := by
      have h6 : (160 * B) * Real.sqrt L ≤ ex * (Real.sqrt L * Real.sqrt L) := by
        calc (160 * B) * Real.sqrt L ≤ (ex * Real.sqrt L) * Real.sqrt L :=
              mul_le_mul_of_nonneg_right h4 hsqL.le
          _ = ex * (Real.sqrt L * Real.sqrt L) := by ring
      nlinarith [h6, hsq]
    have h6 : 2 * (B * ℓ) ≤ 4 * B * Real.sqrt L := by nlinarith [hℓ2, hB.le]
    have h7 : 4 * B * Real.sqrt L ≤ ex * L / 40 := by nlinarith [h5]
    linarith
  have hlogz0_ge : 1 ≤ Real.log z0 := by
    rw [hlogz0]
    nlinarith [hz0diff, hM1, hex7]
  have hz0gt1 : 1 < z0 := (Real.log_pos_iff hz0pos.le).mp (by linarith)
  have hlogz0pos : 0 < Real.log z0 := Real.log_pos hz0gt1
  -- the window of integers
  set L0 := ⌈Real.sqrt Y / 2⌉₊ with hL0def
  set U0 := ⌈Real.sqrt Y⌉₊ with hU0def
  set N := U0 - L0 with hNdef
  have hL0le : Real.sqrt Y / 2 ≤ (L0 : ℝ) := Nat.le_ceil _
  have hU0le : Real.sqrt Y ≤ (U0 : ℝ) := Nat.le_ceil _
  have hU0ub : (U0 : ℝ) < Real.sqrt Y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL0U0 : L0 ≤ U0 := Nat.ceil_mono (by linarith)
  have hNL0 : L0 + N = U0 := by
    rw [hNdef]
    exact Nat.add_sub_cancel' hL0U0
  have hNpos : 1 ≤ N := by
    have hlt : L0 < U0 := by
      by_contra hcon
      have hle : U0 ≤ L0 := Nat.le_of_not_lt hcon
      have heq : L0 = U0 := le_antisymm hL0U0 hle
      have h1 : (L0 : ℝ) < Real.sqrt Y / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : Real.sqrt Y ≤ (L0 : ℝ) := by rw [heq]; exact hU0le
      linarith
    omega
  have hL0ge1 : (1:ℝ) ≤ (L0 : ℝ) := by linarith
  have hmU : ∀ j < N, ((L0 + j : ℕ) : ℝ) ≤ (U0 : ℝ) - 1 := by
    intro j hj
    have h1 : L0 + j ≤ U0 - 1 := by omega
    have h2 : ((L0 + j : ℕ) : ℝ) ≤ ((U0 - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((U0 - 1 : ℕ) : ℝ) = (U0 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ U0)]
      norm_num
    linarith
  have hm_ge : ∀ j < N, Real.sqrt Y / 2 ≤ ((L0 + j : ℕ) : ℝ) := by
    intro j hj
    have h2 : (L0 : ℝ) ≤ ((L0 + j : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hm_cast_pos : ∀ m : ℕ, L0 ≤ m → (0:ℝ) < (m : ℝ) := by
    intro m hm
    have h3 : (L0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  set w : ℕ → ℝ := fun j => f2Weight z0 ((L0 + j : ℕ) : ℝ) with hwdef
  have hmpos : ∀ m : ℕ, L0 ≤ m → 2 * Real.log z0 ≤ Real.log (m : ℝ) := by
    intro m hm
    have h2 : Real.log (Real.sqrt Y / 2) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log (by positivity)
      have h3 : (L0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h4 : Real.log (Real.sqrt Y / 2) = ex * L / 2 - Real.log 2 := by
      rw [Real.log_div hsqY.ne' (by norm_num), Real.log_sqrt hYpos.le, hlogY]
    have h5 : 2 * Real.log z0 = ex * L / 2 - 4 * (B * ℓ) := by
      rw [hlogz0]; ring
    have h6 : Real.log 2 ≤ 4 * (B * ℓ) := by
      have h7 : 0 ≤ B * ℓ := mul_nonneg hB.le hℓ0
      linarith
    linarith
  have hz0le : ∀ m : ℕ, L0 ≤ m → z0 ^ 2 ≤ (m : ℝ) := by
    intro m hm
    have h1 : Real.log (z0 ^ 2) = 2 * Real.log z0 := by
      rw [Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by positivity : (0:ℝ) < z0 ^ 2) (hm_cast_pos m hm), h1]
    exact hmpos m hm
  have hlogup : ∀ m : ℕ, L0 ≤ m → (m : ℝ) ≤ (U0 : ℝ) →
      Real.log (m : ℝ) ≤ 5 / 2 * Real.log z0 := by
    intro m hm hle
    have h1 : Real.log (m : ℝ) ≤ Real.log (U0 : ℝ) := Real.log_le_log (hm_cast_pos m hm) hle
    have h2 : Real.log (U0 : ℝ) ≤ Real.log (2 * Real.sqrt Y) := by
      apply Real.log_le_log (by positivity)
      have h4 : (U0 : ℝ) < Real.sqrt Y + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have h3 : Real.log (2 * Real.sqrt Y) = Real.log 2 + ex * L / 2 := by
      rw [Real.log_mul (by norm_num) hsqY.ne', Real.log_sqrt hYpos.le, hlogY]
    have h5 : 5 * (B * ℓ) ≤ ex * L / 16 := by nlinarith [hz0diff]
    have h6 : 1 ≤ ex * L / 16 := by nlinarith [hM1, hex7]
    nlinarith [h1, h2, h3, hlog2le, h5, h6]
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    simp only [hwdef]
    have hm1 : L0 ≤ L0 + j := Nat.le_add_right L0 j
    rw [f2Weight_eq hz0gt1 (hz0le _ hm1)]
    have hlogm : 0 < Real.log ((L0 + j : ℕ) : ℝ) := by
      have h := hmpos _ hm1
      linarith
    have hnum : 0 < 1 + Real.log ((Real.log ((L0 + j : ℕ) : ℝ) - Real.log z0) / Real.log z0) := by
      have hr : 1 ≤ (Real.log ((L0 + j : ℕ) : ℝ) - Real.log z0) / Real.log z0 := by
        rw [le_div_iff₀ hlogz0pos]
        linarith [hmpos _ hm1]
      have h2 := Real.log_nonneg hr
      linarith
    exact div_nonneg hnum.le hlogm.le
  have hw_mono : ∀ j, j < N → w j ≤ w (j + 1) := by
    intro j hj
    simp only [hwdef]
    have hz0m := hz0le (L0 + j) (Nat.le_add_right L0 j)
    have hle1 : ((L0 + j : ℕ) : ℝ) ≤ ((L0 + (j + 1) : ℕ) : ℝ) := by
      have h2 : L0 + j ≤ L0 + (j + 1) := by omega
      exact_mod_cast h2
    have hle2 : ((L0 + (j + 1) : ℕ) : ℝ) ≤ (U0 : ℝ) := by
      have h2 : L0 + (j + 1) ≤ U0 := by omega
      exact_mod_cast h2
    exact f2Weight_mono hz0gt1 hz0m hle1 (hlogup _ (by omega) hle2)
  have hw_two : w (N - 1) ≤ 2 := by
    simp only [hwdef]
    have hz0m := hz0le (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))
    have hle2 : ((L0 + (N - 1) : ℕ) : ℝ) ≤ (U0 : ℝ) := by
      have h2 : L0 + (N - 1) ≤ U0 := by omega
      exact_mod_cast h2
    rw [f2Weight_eq hz0gt1 hz0m]
    have hmup := hlogup (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1)) hle2
    have hlogm : 2 ≤ Real.log ((L0 + (N - 1) : ℕ) : ℝ) := by
      have h := hmpos (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))
      linarith
    have hlogm0 : 0 < Real.log ((L0 + (N - 1) : ℕ) : ℝ) := by linarith
    have hr : Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0 ≤ Real.log z0 * (3 / 2) := by
      nlinarith [hmup]
    have hlogr : Real.log ((Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0) ≤ 1 := by
      have hpos : 0 < (Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0 := by
        apply div_pos _ hlogz0pos
        linarith [hmpos (L0 + (N - 1)) (Nat.le_add_right L0 (N - 1))]
      have hr2 : (Real.log ((L0 + (N - 1) : ℕ) : ℝ) - Real.log z0) / Real.log z0 ≤ 3 / 2 := by
        rw [div_le_iff₀ hlogz0pos]
        linarith
      have h1 := Real.log_le_sub_one_of_pos hpos
      linarith
    rw [div_le_iff₀ hlogm0]
    linarith
  -- reindex the sum
  have hT2 : T2 Y P β = ∑ j ∈ Finset.range N,
      (w j : ℂ) * fourier (((L0 + j) ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
    rw [show T2 Y P β = ∑ m ∈ squareWindow Y, ((f2Weight z0 (m : ℝ) : ℝ) : ℂ) *
        fourier (((m ^ 2 : ℕ)) : ℤ) (β : AddCircle (1 : ℝ)) from by
      unfold T2
      rw [← hz0def]]
    rw [Task674.squareWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
  have hβY : |β| ≤ 1 / (4 * Real.sqrt Y) := by
    rw [hYdef'] at hβd
    exact hβd
  -- the exponential sum bound (Kusmin-Landau)
  have hθdiff : ∀ j : ℕ, (((L0 + (j + 1) : ℕ) : ℝ))^2 * |β| -
      (((L0 + j : ℕ) : ℝ))^2 * |β| = (2 * (((L0 + j : ℕ) : ℝ)) + 1) * |β| := by
    intro j
    have h2 : L0 + (j + 1) = L0 + j + 1 := by omega
    rw [h2]
    push_cast
    ring
  have hKL : ∀ k ≤ N, ‖∑ j ∈ Finset.range k,
      LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ ≤
      8 / (Real.sqrt Y * |β|) := by
    intro k hk
    refine sum_e_le_of_mono_steps (θ := fun j => (((L0 + j : ℕ) : ℝ))^2 * |β|)
      (δ := Real.sqrt Y * |β|) (by positivity) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [hθdiff j]
      have h1 : (0:ℝ) < 2 * (((L0 + j : ℕ) : ℝ)) + 1 := by positivity
      exact mul_pos h1 hβ
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have hmU := hmU j hjN
      have h2 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 2 * Real.sqrt Y + 1 := by
        nlinarith [hmU, hU0ub]
      have h3 : (2 * Real.sqrt Y + 1) * |β| ≤ 2 / 3 := by
        have h4 : (2 * Real.sqrt Y + 1) * |β| ≤
            (2 * Real.sqrt Y + 1) * (1 / (4 * Real.sqrt Y)) :=
          mul_le_mul_of_nonneg_left hβY (by positivity)
        have h5 : (2 * Real.sqrt Y + 1) * (1 / (4 * Real.sqrt Y)) ≤ 2 / 3 := by
          rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt Y)]
          nlinarith [hY2]
        linarith
      exact (mul_le_mul_of_nonneg_right h2 hβ.le).trans h3
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have h1 : Real.sqrt Y ≤ 2 * (((L0 + j : ℕ) : ℝ)) + 1 := by
        have h2 := hm_ge j hjN
        linarith
      exact mul_le_mul_of_nonneg_right h1 hβ.le
    · intro j hj
      rw [hθdiff j]
      have hjN : j < N := lt_of_lt_of_le hj hk
      have hmU := hmU j hjN
      have h2 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 4 * Real.sqrt Y := by
        nlinarith [hmU, hU0ub, hY2]
      calc (2 * (((L0 + j : ℕ) : ℝ)) + 1) * |β| ≤ (4 * Real.sqrt Y) * |β| :=
            mul_le_mul_of_nonneg_right h2 hβ.le
        _ = 4 * (Real.sqrt Y * |β|) := by ring
    · intro j hj
      rw [hθdiff j, hθdiff (j + 1)]
      have h1 : 2 * (((L0 + j : ℕ) : ℝ)) + 1 ≤ 2 * (((L0 + (j + 1) : ℕ) : ℝ)) + 1 := by
        have hidx : ((L0 + (j + 1) : ℕ) : ℝ) = ((L0 + j : ℕ) : ℝ) + 1 := by
          have h2 : L0 + (j + 1) = L0 + j + 1 := by omega
          rw [h2]
          push_cast
          ring
        rw [hidx]
        linarith
      exact mul_le_mul_of_nonneg_right h1 hβ.le
  -- the weights times the phases
  have hterm : ∀ j, (w j : ℂ) * fourier (((L0 + j) ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) =
      (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β) := by
    intro j
    rw [Task556d.fourier_nat_eq_e]
    congr 1
    push_cast
    ring
  have hnorm_eq : ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β)‖
      = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ := by
    have hβne : β ≠ 0 := by
      intro h0
      rw [h0] at hβ
      simp at hβ
    rcases lt_or_gt_of_ne hβne with hneg | hpos
    · have hconj : (∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β))
          = (starRingEnd ℂ) (∑ j ∈ Finset.range N,
            (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have harg : ((((L0 + j : ℕ) : ℝ))^2 * β) = -((((L0 + j : ℕ) : ℝ))^2 * |β|) := by
          rw [abs_of_neg hneg]
          ring
        rw [harg, LeanLab.PNTPort.LargeSieve.e_neg, map_mul, Complex.conj_ofReal]
      rw [hconj, RCLike.norm_conj]
    · rw [abs_of_pos hpos]
  have hAbel := norm_sum_mono_weight_le
    (f := fun j => LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|))
    (w := w) (B := 8 / (Real.sqrt Y * |β|)) (N := N) hw_nonneg hw_mono hKL
  rw [hYdef']
  change ‖T2 Y P β‖ ≤ 32 / (Real.sqrt Y * |β|)
  calc ‖T2 Y P β‖
      = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * β)‖ := by
        rw [hT2, Finset.sum_congr rfl fun j hj => hterm j]
    _ = ‖∑ j ∈ Finset.range N, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e ((((L0 + j : ℕ) : ℝ))^2 * |β|)‖ := hnorm_eq
    _ ≤ 2 * w (N - 1) * (8 / (Real.sqrt Y * |β|)) := hAbel
    _ ≤ 2 * 2 * (8 / (Real.sqrt Y * |β|)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hw_two]
    _ = 32 / (Real.sqrt Y * |β|) := by ring

/-- The exact statement of T2_bound, from T2_trivial and
T2_decay. No sorry of its own. -/
theorem T2_bound_of_pieces : T2BoundProp := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := T2_trivial B hB ε hε hε'
  obtain ⟨C2, X2, hC2, k2⟩ := T2_decay B hB ε hε hε'
  refine ⟨2 * C1 + 2 * C2, max (max X1 X2) 1, by positivity, fun X hX β hβ => ?_⟩
  have hXa : X1 ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hY1 := windowY_ge_one hX1 hε
  have hY : 0 < windowY X ε := by linarith
  have hs : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY
  refine split_bound hY hs.le hC1.le hC2.le (fun _ => k1 X hXa β) (fun hc => ?_)
  have hb : 0 < |β| := by
    by_contra h0
    have : |β| = 0 := le_antisymm (not_lt.mp h0) (abs_nonneg β)
    rw [this, mul_zero] at hc
    linarith
  refine (k2 X hXb β hb hβ).trans (le_of_eq ?_)
  have hsq : Real.sqrt (windowY X ε) * Real.sqrt (windowY X ε) = windowY X ε :=
    Real.mul_self_sqrt hY.le
  have hb' : 0 < windowY X ε * |β| := by linarith
  rw [div_eq_div_iff (by positivity) hb'.ne']
  linear_combination (-(C2 * |β|)) * hsq

/-- LEAF: P0088 page 6 display 22 for j = 2, from display 21 for f2 by partial
summation and the Kuzmin Landau bound, phase derivative 2 beta m at most 1/2. -/
theorem T2_bound : T2BoundProp :=
  T2_bound_of_pieces

/-- LEAF: P0088 page 7 display 27, with the tail of the completed integral after
display 26. Uses display 22 through the two named bounds; the tail over
|beta| above Y^(-1/2)/4 needs a mean value bound for T2 beyond display 22. -/
theorem bound27 (h1 : T1BoundProp) (h2 : T2BoundProp) :
    BlockErrorBound (fun X Y H P n => termA X Y H P n - series2 n P * (singInt X Y P n : ℂ)) := by
  sorry

/-- LEAF: P0088 page 6 display 20 from displays 16 to 19, Gallagher's lemma with the
Saffari Vaughan device and hypothesis (A2.2), here A22Corr; H at most Y P^(-4)
keeps the delta edge term at most P^(-4). -/
theorem bound20 (h : A22Corr) : BlockErrorBound termB := by
  sorry

/-- LEAF: P0088 page 6 display 24, Cauchy with display 17, the Gauss sum bound
|S(q, a)| at most q^(1/2 + eta) and display 22 for T2 on |beta| between 1/(q Q0)
and 1/(q Q). -/
theorem bound24 (h2 : T2BoundProp) : BlockErrorBound termC := by
  sorry

/-- LEAF: P0088 page 6 display 26 from display 25, partial summation with hypothesis
(A1.2), here A12Corr, and display 22 for T2. -/
theorem bound26 (hA : A12Corr) (h2 : T2BoundProp) : BlockErrorBound termD := by
  sorry

/-- P0088 page 16: for eps above 7/18 the block range of Task628.major_arc_block is empty. -/
theorem block_range_empty {X H B ε : ℝ} (hX : 3 ≤ X) (hε : 7 / 18 < ε)
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ)) : False := by
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hP : 0 < (Real.log X ^ B) ^ (-4 : ℤ) := zpow_pos (Real.rpow_pos_of_pos hL _) _
  have h := (mul_le_mul_iff_left₀ hP).mp (hlo.trans hhi)
  rw [windowY] at h
  have h2 := (Real.rpow_le_rpow_left_iff hX1).mp h
  linarith

/-- P0088 page 7 display 28 squared: the exact statement of Task628.major_arc_block,
from the seven leaves above and the proved Fourier split. CONDITIONAL ON the cited A12Corr and A22Corr. -/
theorem major_arc_block_of_char_inputs (hA12 : A12Corr) (hA22 : A22Corr)
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  refine ⟨2 * A + 1, by linarith, ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := by linarith
  by_cases hεhi : 7 / 18 < ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX hlo hhi n
    exact (block_range_empty hX hεhi hlo hhi).elim
  have hε' : ε ≤ 7 / 18 := le_of_not_gt hεhi
  obtain ⟨X0, hdec⟩ := major_decomp B hBpos ε hε hε'
  obtain ⟨C1, X1, hC1, h27⟩ := bound27 T1_bound T2_bound B hBpos ε hε hε'
  obtain ⟨C2, X2, hC2, h20⟩ := bound20 hA22 B hBpos ε hε hε'
  obtain ⟨C3, X3, hC3, h24⟩ := bound24 T2_bound B hBpos ε hε hε'
  obtain ⟨C4, X4, hC4, h26⟩ := bound26 hA12 T2_bound B hBpos ε hε hε'
  set K := C1 + C2 + C3 + C4 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K ^ 2, max (max (max X0 X1) (max X2 X3)) (max X4 3), by positivity,
    le_trans (by norm_num) (le_max_right _ _ |>.trans (le_max_right _ _)), ?_⟩
  intro X H hX hlo hhi n
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX1 : X1 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _ |>.trans
    (le_max_left _ _))) hX
  have hX2 : X2 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX3 : X3 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans
    (le_max_left _ _))) hX
  have hX4 : X4 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hX
  have hX5 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_right _ _)) hX
  set Y := windowY X ε with hY
  set L := Real.log X with hLdef
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX5
  have hLpos : 0 < L := by linarith
  have hYnn : 0 ≤ Y := Real.rpow_nonneg hXpos.le _
  set E := ‖majorError X Y H (L ^ B) n‖ with hE
  set R := (L ^ B) ^ (-(1 / 4 : ℝ)) with hR
  have hRnn : 0 ≤ R := Real.rpow_nonneg (Real.rpow_nonneg hLpos.le _) _
  have hsplit : majorError X Y H (L ^ B) n =
      (termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)) +
        termB X Y H (L ^ B) n + termC X Y H (L ^ B) n + termD X Y H (L ^ B) n := by
    rw [majorError, roughCount_eq_major_add_minor X Y H (L ^ B) n,
      hdec X H hX0 hlo hhi n]
    ring
  have hbound : E ≤ K * Real.sqrt Y * R := by
    rw [hE, hsplit]
    have a1 := h27 X H hX1 hlo hhi n
    have a2 := h20 X H hX2 hlo hhi n
    have a3 := h24 X H hX3 hlo hhi n
    have a4 := h26 X H hX4 hlo hhi n
    calc _ ≤ ‖termA X Y H (L ^ B) n - series2 n (L ^ B) * (singInt X Y (L ^ B) n : ℂ)‖ +
          ‖termB X Y H (L ^ B) n‖ + ‖termC X Y H (L ^ B) n‖ + ‖termD X Y H (L ^ B) n‖ :=
            norm_add₄_le
      _ ≤ C1 * Real.sqrt Y * R + C2 * Real.sqrt Y * R + C3 * Real.sqrt Y * R +
          C4 * Real.sqrt Y * R := by gcongr
      _ = K * Real.sqrt Y * R := by rw [hK]; ring
  have hRsq : R ^ 2 ≤ L ^ (-A) := by
    have h1 : R = L ^ (B * (-(1 / 4 : ℝ))) := by rw [hR, ← Real.rpow_mul hLpos.le]
    have h2 : R ^ 2 = L ^ (-(B / 2)) := by
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      congr 1
      push_cast
      ring
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hEnn : 0 ≤ E := norm_nonneg _
  calc E ^ 2 ≤ (K * Real.sqrt Y * R) ^ 2 := pow_le_pow_left₀ hEnn hbound 2
    _ = K ^ 2 * Y * R ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hYnn]
    _ ≤ K ^ 2 * Y * L ^ (-A) := by gcongr
    _ = K ^ 2 * Y / L ^ A := by rw [Real.rpow_neg hLpos.le, div_eq_mul_inv]

/-- The theorem above has the exact type of the sealed leaf Task628.major_arc_block. -/
example (hA12 : A12Corr) (hA22 : A22Corr) : type_of% @Task628.major_arc_block :=
  major_arc_block_of_char_inputs hA12 hA22

end LeanLab.KumchevLiu2007.Prep1121KLMajor

#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.major_arc_block_of_char_inputs
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.block_range_empty
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.roughCount_eq_major_add_minor

#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.fourier_shift_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T2_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.measurableSet_arc
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.S1star_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.S2star_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.primeSum_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.roughSum_memLp_top
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.majorArcs_antitone
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_geometric_bound
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.dist0_eq_abs_of_abs_le_half
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_decay_bound
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.major_decomp
#print axioms LeanLab.KumchevLiu2007.Prep1121KLMajor.T1_bound
