import Mathlib

/-!
# Euclid's lemma — statement B (Gauss)

Source (Wikipedia, "Euclid's lemma", lead; Euclid, *Elements* VII.30):
> If a prime p divides the product ab of two integers a and b, then p must divide
> at least one of those integers a or b.

Phrased as elementarily as possible: primality and divisibility are spelled out by hand
rather than using `Nat.Prime` and `∣`.

Mapping, source → Lean:
* "a prime p"                  → `p : ℕ` with `2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p` (`IsPrimeB p`)
* "two integers a and b"       → `a b : ℤ` (any sign, zero allowed)
* "the product ab"             → `a * b : ℤ`
* "p divides …" (in ℤ)         → `DividesB p x := ∃ k : ℤ, x = (p : ℤ) * k`
* "if … then …"                → `→`
* "at least one of a or b"     → inclusive `∨`: `DividesB p a ∨ DividesB p b`
-/

namespace TuriMath.EuclidLemma.B

/-- `p` is prime: at least 2, and its only natural-number divisors are 1 and itself. -/
def IsPrimeB (p : ℕ) : Prop := 2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

/-- The natural number `p` divides the integer `x`: `x = p * k` for some integer `k`. -/
def DividesB (p : ℕ) (x : ℤ) : Prop := ∃ k : ℤ, x = (p : ℤ) * k

/-- Euclid's lemma (statement B). -/
def Statement : Prop :=
  ∀ (p : ℕ) (a b : ℤ), IsPrimeB p → DividesB p (a * b) → DividesB p a ∨ DividesB p b

/-! ## Sanity section -/

/-- `IsPrimeB` is exactly Mathlib's `Nat.Prime` (so our hand-made primality is not off). -/
example (p : ℕ) : IsPrimeB p ↔ Nat.Prime p := Nat.prime_def.symm

/-- `DividesB` is exactly divisibility in `ℤ`. -/
example (p : ℕ) (x : ℤ) : DividesB p x ↔ (p : ℤ) ∣ x := Iff.rfl

/-- The hypotheses can all hold at once: p = 5, a = 10, b = 3, 30 = 5 * 6. -/
example : ∃ (p : ℕ) (a b : ℤ), IsPrimeB p ∧ DividesB p (a * b) :=
  ⟨5, 10, 3, Nat.prime_def.mp (by norm_num), 6, by norm_num⟩

/-! ## Concrete cases -/

/-- p = 5, a = 10, b = 3: 5 ∣ 30, and indeed 10 = 5 * 2. -/
example : IsPrimeB 5 ∧ DividesB 5 (10 * 3) ∧ DividesB 5 10 :=
  ⟨Nat.prime_def.mp (by norm_num), ⟨6, by norm_num⟩, ⟨2, by norm_num⟩⟩

/-- Negative integers: p = 3, a = 7, b = -6: 3 ∣ -42, and b = 3 * (-2). -/
example : IsPrimeB 3 ∧ DividesB 3 (7 * (-6)) ∧ DividesB 3 (-6) :=
  ⟨Nat.prime_def.mp (by norm_num), ⟨-14, by norm_num⟩, ⟨-2, by norm_num⟩⟩

/-- Zero: p = 2, a = 0, b = 7: 2 ∣ 0, and a = 0 = 2 * 0. -/
example : DividesB 2 (0 * 7) ∧ DividesB 2 0 := ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

/-- Primality matters: p = 6 divides 2 * 3 = 6 but divides neither 2 nor 3,
and 6 is not `IsPrimeB` (2 ∣ 6). So the hypothesis is doing real work. -/
example : DividesB 6 (2 * 3) ∧ ¬ DividesB 6 2 ∧ ¬ DividesB 6 3 ∧ ¬ IsPrimeB 6 := by
  refine ⟨⟨1, by norm_num⟩, ?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩; omega
  · rintro ⟨k, hk⟩; omega
  · rintro ⟨-, h⟩; have := h 2 (by norm_num); omega

end TuriMath.EuclidLemma.B
