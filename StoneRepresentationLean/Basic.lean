import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

open PrimeSpectrum

universe u
variable {R : Type u} [BooleanRing R]

attribute [local instance] BooleanAlgebra.toBooleanRing

namespace BooleanRing

lemma mem_ideal_or_mem_ideal (x : R) (p : PrimeSpectrum R) :
    x ∈ p.asIdeal ∨ (1 + x) ∈ p.asIdeal := by
  apply Ideal.IsPrime.mem_or_mem'
  rw [BooleanRing.mul_one_add_self]
  exact Submodule.zero_mem p.asIdeal

lemma mem_ideal_iff (x : R) (p : PrimeSpectrum R) : x ∈ p.asIdeal ↔ 1 + x ∉ p.asIdeal := by
  constructor
  case mp =>
    intro h h'
    apply Ideal.one_notMem p.asIdeal
    have key : (1 + x) + x = 1 := by
      calc (1 + x) + x = 1 + (x + x) := by ring
                     _ = 1 + 0 := by rw [BooleanRing.add_self]
                     _ = 1 := by ring
    rw [← key]
    exact (Submodule.add_mem_iff_right p.asIdeal h').mpr h
  case mpr =>
    intro h
    have key := BooleanRing.mem_ideal_or_mem_ideal x p
    tauto

lemma one_add_self_mem_ideal {x y : R} {p : PrimeSpectrum R}
    (h : 1 + x * y ∈ p.asIdeal) : 1 + x ∈ p.asIdeal := by
  cases BooleanRing.mem_ideal_or_mem_ideal x p
  case inl h' =>
    exfalso
    apply Ideal.one_notMem p.asIdeal
    have key : (1 + x*y) + y*x = 1 := by
      calc (1 + x*y) + y*x = 1 + (x*y + x*y) := by ring
                         _ = 1 + 0 := by rw [BooleanRing.add_self]
                         _ = 1 := by ring
    rw [← key]
    apply Submodule.add_mem p.asIdeal h (Ideal.mul_mem_left p.asIdeal y h')
  case inr h' => exact h'

lemma one_add_self_mem_ideal' {x y : R} {p : PrimeSpectrum R}
    (h : 1 + y * x ∈ p.asIdeal) : 1 + x ∈ p.asIdeal := by
  rw [mul_comm] at h
  exact one_add_self_mem_ideal h

lemma IsUnit_iff (x : R) : IsUnit x ↔ x = 1 := by
  constructor
  · intro hx
    rcases hx with ⟨⟨x, y, hx1, hx2⟩, _, _⟩
    simp_all only
    rw [← BooleanRing.add_eq_zero']
    calc x + 1 = 1*(x + 1) := by ring
             _ = (x*y)*(x + 1) := by rw [hx1]
             _ = (x*x)*y + x*y := by ring
             _ = x*y + x*y := by rw [BooleanRing.mul_self]
             _ = 0 := by rw [BooleanRing.add_self]
  · intro hx
    exact Associates.mk_eq_one.mp (congrArg Associates.mk hx)

lemma nonunit_iff (x : R) : x ∈ nonunits R ↔ x ≠ 1 := by
  rw [mem_nonunits_iff, BooleanRing.IsUnit_iff]

end BooleanRing

namespace BooleanAlgebra

variable (A B : Type u) [BooleanAlgebra A] [BooleanAlgebra B]
variable {C D : Type u} [BooleanAlgebra C] [BooleanAlgebra D]

theorem toBooleanRing_add (a b : A) : a + b = symmDiff a b := rfl

theorem toBooleanRing_mul (a b : A) : a * b = a ⊓ b := rfl

theorem toBooleanRing_sup (a b : A) : a ⊔ b = a + b + (a * b) := by
  rw [toBooleanRing_add, toBooleanRing_add, toBooleanRing_mul, symmDiff_symmDiff_inf]

def BoundedLatticeHomfromRingHom (f : C →+* D) : BoundedLatticeHom C D where
  toFun := f
  map_sup' := by
    intro a b
    simp only [toBooleanRing_sup, f.map_add, f.map_mul]
  map_inf' := f.map_mul
  map_top' := f.map_one
  map_bot' := f.map_zero

end BooleanAlgebra
