/-
  Plimpton 322 in Lean 4 — core Lean only, no Mathlib required.

  Convention (matches the tablet):
    s = short side  (Column II of the tablet)
    l = long side   (NOT on the tablet; reconstructed as √(d² − s²))
    d = diagonal    (Column III of the tablet)

  Row 1: s = 119, d = 169  ⟹  l = 120.
-/

def IsPythagoreanTriple (s l d : Nat) : Prop :=
  s * s + l * l = d * d

-- Row 1: kernel reduction — 119² + 120² and 169² both compute to 28561.
theorem plimpton_row_1 : IsPythagoreanTriple 119 120 169 := by
  rfl

/- Scaling lemma, Mathlib-free.
   (With Mathlib you could replace the calc body with `ring`-based steps,
   after `import Mathlib.Tactic.Ring`.) -/
theorem scale_triple (s l d k : Nat) (h : IsPythagoreanTriple s l d) :
    IsPythagoreanTriple (s * k) (l * k) (d * k) := by
  unfold IsPythagoreanTriple at h ⊢
  calc (s * k) * (s * k) + (l * k) * (l * k)
      = (s * s) * (k * k) + (l * l) * (k * k) := by
        rw [Nat.mul_mul_mul_comm, Nat.mul_mul_mul_comm]
    _ = (s * s + l * l) * (k * k) := (Nat.add_mul ..).symm
    _ = (d * d) * (k * k) := by rw [h]
    _ = (d * k) * (d * k) := by rw [Nat.mul_mul_mul_comm]

/- All fifteen rows (reconstructed values), batch-verified by the kernel.
   `decide` is preferred over `rfl` here: it stays fast and readable
   even for Row 4, where d² = 343 768 681. -/

theorem row_01 : IsPythagoreanTriple   119   120   169 := by decide
theorem row_02 : IsPythagoreanTriple  3367  3456  4825 := by decide
theorem row_03 : IsPythagoreanTriple  4601  4800  6649 := by decide
theorem row_04 : IsPythagoreanTriple 12709 13500 18541 := by decide
theorem row_05 : IsPythagoreanTriple    65    72    97 := by decide
theorem row_06 : IsPythagoreanTriple   319   360   481 := by decide
theorem row_07 : IsPythagoreanTriple  2291  2700  3541 := by decide
theorem row_08 : IsPythagoreanTriple   799   960  1249 := by decide
theorem row_09 : IsPythagoreanTriple   481   600   769 := by decide
theorem row_10 : IsPythagoreanTriple  4961  6480  8161 := by decide
theorem row_11 : IsPythagoreanTriple    45    60    75 := by decide
theorem row_12 : IsPythagoreanTriple  1679  2400  2929 := by decide
theorem row_13 : IsPythagoreanTriple   161   240   289 := by decide
theorem row_14 : IsPythagoreanTriple  1771  2700  3229 := by decide
theorem row_15 : IsPythagoreanTriple    56    90   106 := by decide

/- The scribe's errors, refuted by the kernel.
   The tablet AS WRITTEN contains mistakes in several rows; Lean rejects
   them. Formal verification catching a ~1800 BCE copying error. -/

-- Row 9 as written: 541 (9,01) where 481 (8,01) belongs.
example : ¬ IsPythagoreanTriple 541 600 769 := by decide

-- Row 13 as written: 25921 = 161² recorded instead of 161 itself.
example : ¬ IsPythagoreanTriple 25921 240 289 := by decide

-- Row 15 as written: diagonal 53, half of the true value 106.
example : ¬ IsPythagoreanTriple 56 90 53 := by decide

-- Sanity check tying Row 11 to the scaling lemma: (45,60,75) = 15 · (3,4,5).
theorem row_11_is_scaled_345 : IsPythagoreanTriple (3 * 15) (4 * 15) (5 * 15) :=
  scale_triple 3 4 5 15 (by decide)
