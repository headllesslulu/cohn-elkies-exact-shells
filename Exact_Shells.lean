import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact shell zeros for a small Fourier perturbation

The analytic interpolation and interval estimates are proved in the manuscript.
This file checks the passage from those pointwise estimates to an exact zero
set, the constants used in the argument, and the integer obstruction at 15.
Tested with Lean 4.19.0 and the accompanying mathlib release.
-/

namespace ExactShells

/-- Subtracting the transform of an even function gives eigenvalue minus one. -/
theorem anti_direction {E : Type*} [AddCommGroup E] (T : E →+ E) (p : E)
    (hinv : T (T p) = p) : T (p - T p) = -(p - T p) := by
  rw [map_sub, hinv, neg_sub]

/-- The two rows of the inverse equation prescribe the value and zero slope. -/
theorem interpolation_rows (Q D c d K K' w : ℝ) (hc : Q*c - K = w)
    (hd : Q*d + D*K - K' = -(D*w)) :
    Q*c - K = w ∧ Q*(d + D*c) - K' = 0 := by
  refine ⟨hc, ?_⟩
  calc
    Q*(d + D*c) - K' = (Q*d + D*K - K') + D*(Q*c - K) := by ring
    _ = 0 := by rw [hd, hc, neg_add_cancel]

/-- The same inequality works on either side of the nearest node. -/
theorem gap_bound (H U e w c K d : ℝ) (he : 0 ≤ e)
    (hH : c * d ^ 2 ≤ H) (hU : w - K * d ^ 2 ≤ U) :
    e * w + (c - e * K) * d ^ 2 ≤ H + e * U := by
  calc
    e * w + (c - e * K) * d ^ 2 =
        c * d ^ 2 + e * (w - K * d ^ 2) := by ring
    _ ≤ H + e * U := add_le_add hH (mul_le_mul_of_nonneg_left hU he)

/-- On each half-gap a zero is equivalent to being at a node of weight zero. -/
theorem zero_iff (H U e w c K d : ℝ)
    (he : 0 < e) (hw : 0 ≤ w) (hc : 0 < c - e * K)
    (hH : c * d ^ 2 ≤ H) (hU : w - K * d ^ 2 ≤ U)
    (hnode : d = 0 → H = 0 ∧ U = w) :
    H + e * U = 0 ↔ d = 0 ∧ w = 0 := by
  constructor
  · intro hz
    have hb := gap_bound H U e w c K d he.le hH hU
    rw [hz] at hb
    have hn : 0 ≤ e * w := mul_nonneg he.le hw
    have hd : d = 0 := by
      by_contra h
      have hp := mul_pos hc (sq_pos_of_ne_zero h)
      linarith
    obtain ⟨hH0, hUw⟩ := hnode hd
    rw [hH0, hUw, zero_add] at hz
    exact ⟨hd, (mul_eq_zero.mp hz).resolve_left he.ne'⟩
  · rintro ⟨hd, hw0⟩
    obtain ⟨hH0, hUw⟩ := hnode hd
    simp [hH0, hUw, hw0]

/-- A quadratic perturbation preserves the positive side of a simple root. -/
theorem interior_positive (H U e a K d : ℝ)
    (he : 0 ≤ e) (hK : 0 ≤ K) (hd : 0 < d) (hd1 : d ≤ 1)
    (hmargin : 0 < a - e * K) (hH : a * d ≤ H)
    (hU : U ≤ K * d ^ 2) : 0 < H - e * U := by
  have hd2 : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  have hUK : U ≤ K * d := hU.trans (mul_le_mul_of_nonneg_left hd2 hK)
  have hEU := mul_le_mul_of_nonneg_left hUK he
  have hpos := mul_pos hmargin hd
  nlinarith

theorem certificate_constants :
    (0 : ℝ) < 1/250 - (1/10^12) * (51240000/2) ∧
    (1/10^12 : ℝ) * 732000 < 1/1000000 ∧
    (51240000/2 : ℝ) * (1/10^12) < 1/10000 := by
  norm_num

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem residue_obstruction :
    ∀ j k : ZMod 25, j^2 + j*k + k^2 ≠ 15 := by decide

theorem fifteen_is_not_a_shell (j k : ℤ) : j^2 + j*k + k^2 ≠ 15 := by
  intro h
  have hr := congrArg (fun a : ℤ => (a : ZMod 25)) h
  exact residue_obstruction (j : ZMod 25) (k : ZMod 25) (by simpa using hr)

end ExactShells

#print axioms ExactShells.anti_direction
#print axioms ExactShells.interpolation_rows
#print axioms ExactShells.zero_iff
#print axioms ExactShells.interior_positive
#print axioms ExactShells.certificate_constants
#print axioms ExactShells.fifteen_is_not_a_shell
