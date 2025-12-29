import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
## Centered squares
-/

open MeasureTheory (ae volume)
open Metric (ball)
open Set

variable {c : ℂ} {s r : ℝ}

/-- Closed square centered at `c` with side length `s` -/
def csquare (c : ℂ) (s : ℝ) : Set ℂ :=
  {z | |z.re - c.re| ≤ s ∧ |z.im - c.im| ≤ s}

/-- Open square centered at `c` with side length `s` -/
def osquare (c : ℂ) (s : ℝ) : Set ℂ :=
  {z | |z.re - c.re| < s ∧ |z.im - c.im| < s}

/-- The closed square is closed -/
lemma isClosed_csquare : IsClosed (csquare c s) := by
  simp only [csquare, ← max_le_iff]
  simp only [← mem_Iic, ← preimage_setOf_eq, setOf_mem_eq]
  exact isClosed_Iic.preimage (by fun_prop)

/-- The open square is closed -/
lemma isOpen_osquare : IsOpen (osquare c s) := by
  simp only [osquare, ← max_lt_iff]
  simp only [← mem_Iio, ← preimage_setOf_eq, setOf_mem_eq]
  exact isOpen_Iio.preimage (by fun_prop)

/-- The open square is inside the closed square -/
lemma osquare_subset_csquare : osquare c s ⊆ csquare c s := by
  simp only [osquare, csquare]
  grind

lemma csquare_eq_prod :
    csquare c s = Complex.measurableEquivRealProd ⁻¹'
      (Icc (c.re - s) (c.re + s) ×ˢ Icc (c.im - s) (c.im + s)) := by
  ext ⟨u,v⟩
  simp [csquare, abs_le]
  grind

lemma osquare_eq_prod :
    osquare c s = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (c.re - s) (c.re + s) ×ˢ Ioo (c.im - s) (c.im + s)) := by
  ext ⟨u,v⟩
  simp [osquare, abs_lt]
  grind

@[simp] lemma volume_csquare : volume (csquare c s) = 4 * .ofReal s ^ 2 := by
  rw [csquare_eq_prod,
    Complex.volume_preserving_equiv_real_prod.measure_preimage (by measurability),
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp only [Real.volume_Icc, add_sub_sub_cancel, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
    ENNReal.ofReal_ofNat, ← pow_two, ← two_mul]
  ring

@[simp] lemma volume_osquare : volume (osquare c s) = 4 * .ofReal s ^ 2 := by
  rw [osquare_eq_prod,
    Complex.volume_preserving_equiv_real_prod.measure_preimage (by measurability),
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp only [Real.volume_Ioo, add_sub_sub_cancel, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
    ENNReal.ofReal_ofNat, ← pow_two, ← two_mul]
  ring

@[aesop (rule_sets := [finiteness]) safe apply]
lemma volume_csquare_finite : volume (csquare c s) ≠ ⊤ := by
  rw [volume_csquare]
  finiteness

@[aesop (rule_sets := [finiteness]) safe apply]
lemma volume_osquare_finite : volume (osquare c s) ≠ ⊤ := by
  rw [volume_osquare]
  finiteness

@[simp] lemma volumeReal_csquare (s0 : 0 ≤ s) : volume.real (csquare c s) = 4 * s ^ 2 := by
  simp [volume.real_def, volume_csquare, s0]

/-- The open and closed squares are a.e. equal -/
lemma osquare_ae_eq_csquare : (osquare c s : Set ℂ) =ᶠ[ae volume] (csquare c s : Set ℂ) := by
  simp only [MeasureTheory.ae_eq_set, diff_eq_empty.mpr osquare_subset_csquare,
    MeasureTheory.measure_empty, true_and]
  rw [MeasureTheory.measure_diff osquare_subset_csquare isOpen_osquare.nullMeasurableSet
    (by finiteness), volume_csquare, volume_osquare, tsub_self]

@[simp] private lemma dyadic_4_to_rat : Dyadic.toRat 4 = 4 := rfl

/-- Sufficient condition for a ball to cover a square (also necessary, but we don't need that) -/
lemma osquare_subset_ball (sr : √2 * s ≤ r) : osquare c s ⊆ ball c r := by
  intro z ⟨zr,zi⟩
  by_cases s0 : s < 0
  · linarith [abs_nonneg (z.re - c.re), zr.trans s0]
  · simp only [not_lt] at s0
    have r0 : 0 ≤ r := le_trans (by bound) sr
    rw [← sq_le_sq₀ (by bound) r0, mul_pow, Real.sq_sqrt (by norm_num)] at sr
    simp only [Metric.mem_ball, dist_eq_norm, ← sq_lt_sq₀ (abs_nonneg _) s0, Complex.normSq_apply,
      ← sq_lt_sq₀ (norm_nonneg _) r0, Complex.sq_norm, ← pow_two, Complex.sub_re, sq_abs,
      Complex.sub_im] at zr zi ⊢
    linarith

@[simp] lemma csquare_eq_empty (s0 : s < 0) : csquare c s = ∅ := by
  have lt : ∀ x, ¬|x| ≤ s := by
    intro x
    simp only [not_le]
    linarith [s0, abs_nonneg x]
  simp only [csquare, lt, and_self, setOf_false]

/-- Partition a square into four smaller squares -/
lemma csquare_partition : csquare c s =
    csquare ⟨c.re + s / 2, c.im + s / 2⟩ (s / 2) ∪
    csquare ⟨c.re - s / 2, c.im + s / 2⟩ (s / 2) ∪
    csquare ⟨c.re + s / 2, c.im - s / 2⟩ (s / 2) ∪
    csquare ⟨c.re - s / 2, c.im - s / 2⟩ (s / 2) := by
  ext ⟨x,y⟩
  have e : ∀ x c : ℝ, |x - c| ≤ s ↔ |x - (c - s / 2)| ≤ s / 2 ∨ |x - (c + s / 2)| ≤ s / 2 := by
    intro x c
    simp only [← sub_add, ← sub_sub]
    generalize x - c = y
    simp only [abs_le]
    constructor
    · intro ⟨h1, h2⟩; by_cases y ≤ 0 <;> [left; right] <;> constructor <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  simp only [csquare, e, mem_setOf_eq, mem_union]
  cutsat
