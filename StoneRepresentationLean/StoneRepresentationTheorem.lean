import StoneRepresentationLean.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Hom.Lattice

open Set
open PrimeSpectrum
open RingHom

attribute [local instance] BooleanAlgebra.toBooleanRing
-- attribute [local instance] BooleanRing.toBooleanAlgebra

universe u
variable {R : Type u} [BooleanRing R] (S : Type u) [BooleanRing S]
variable (A : Type u) [BooleanAlgebra A]

namespace StoneRepresentation

def stone_map : S → Set (PrimeSpectrum S) := fun x ↦ {p | x ∉ p.asIdeal}

lemma mem_stone_map_iff (x : R) (p : PrimeSpectrum R) : p ∈ stone_map R x ↔ 1 + x ∈ p.asIdeal := by
  have := BooleanRing.mem_ideal_iff x p
  tauto

lemma mem_stone_map_iff' (x : R) (p : PrimeSpectrum R) : p ∉ stone_map R x ↔ x ∈ p.asIdeal := by
  simp_all only [stone_map, mem_setOf_eq, not_not]

lemma stone_map_add (x y : R) : stone_map R (x + y) = stone_map R x + stone_map R y := by
  ext p
  constructor <;> intro hp
  · by_cases h : p ∈ stone_map R x
    case pos =>
      left
      refine ⟨h, ?_⟩
      rw [mem_stone_map_iff']
      rw [mem_stone_map_iff] at *
      have key : (1 + (x + y)) + (1 + x) = y := by
        calc (1 + (x + y)) + (1 + x) = y + (1 + 1) + (x + x) := by ring
                                   _ = y + 0 + 0 := by repeat rw [BooleanRing.add_self]
                                   _ = y := by ring
      rw [← key]
      exact (Submodule.add_mem_iff_right p.asIdeal hp).mpr h
    case neg =>
      right
      refine ⟨?_, h⟩
      rw [mem_stone_map_iff] at ⊢ hp
      rw [mem_stone_map_iff'] at h
      have key : (1 + (x + y)) + x = 1 + y := by
        calc (1 + (x + y)) + x = 1 + y + (x + x) := by ring
                             _ = 1 + y + 0 := by rw [BooleanRing.add_self]
                             _ = 1 + y := by ring
      rw [← key]
      exact (Submodule.add_mem_iff_right p.asIdeal hp).mpr h
  · cases hp
    case h.mpr.inl hp =>
      rcases hp with ⟨hp1, hp2⟩
      rw [mem_stone_map_iff] at hp1
      rw [mem_stone_map_iff'] at hp2
      rw [mem_stone_map_iff]
      have key : (1 + x) + y ∈ p.asIdeal := by exact
        (Submodule.add_mem_iff_right p.asIdeal hp1).mpr hp2
      have : (1 + x) + y = 1 + (x + y) := by abel
      rw [← this]
      exact key
    case h.mpr.inr hp =>
      rcases hp with ⟨hp1, hp2⟩
      rw [mem_stone_map_iff] at hp1
      rw [mem_stone_map_iff'] at hp2
      rw [mem_stone_map_iff]
      have key : (1 + y) + x ∈ p.asIdeal := by exact
        (Submodule.add_mem_iff_right p.asIdeal hp1).mpr hp2
      have : (1 + y) + x = 1 + (x + y) := by abel
      rw [← this]
      exact key

lemma stone_map_mul (x y : R) : stone_map R (x * y) = stone_map R x * stone_map  R y := by
  ext p
  constructor
  case h.mp =>
    intro hp
    refine ⟨?_, ?_⟩ <;> rw [mem_stone_map_iff] at *
    · exact BooleanRing.one_add_self_mem_ideal hp
    · exact BooleanRing.one_add_self_mem_ideal' hp
  case h.mpr =>
    intro ⟨hp1, hp2⟩
    rw [mem_stone_map_iff] at *
    have key : (1 + x) + x*(1 + y) = 1 + x*y := by
      calc (1 + x) + x*(1 + y) = 1 + (x + x) + x*y := by ring
                             _ = 1 + 0 + x*y := by rw [BooleanRing.add_self]
                             _ = 1 + x*y := by ring
    rw [← key]
    apply Submodule.add_mem p.asIdeal hp1 (Ideal.mul_mem_left p.asIdeal x hp2)

lemma stone_map_one : stone_map R 1 = univ := by
  ext p
  constructor
  · tauto
  · intro _
    rw [mem_stone_map_iff, BooleanRing.add_self]
    exact Submodule.zero_mem p.asIdeal

lemma stone_map_zero : stone_map R 0 = ∅ := by
  ext p
  constructor
  · rw [mem_stone_map_iff, add_zero]
    intro hp
    exfalso
    exact Ideal.one_notMem p.asIdeal hp
  · intro hp
    exfalso
    exact hp

lemma stone_map_injective : Function.Injective (stone_map R) := by
  intro x y
  contrapose!
  intro hxy
  rw [← Set.symmDiff_nonempty]
  have key : 1 + (x + y) ∈ nonunits R := by
    apply (BooleanRing.nonunit_iff (1 + (x + y))).mpr
    intro h
    apply hxy
    apply (BooleanRing.add_eq_zero' x y).mp
    exact left_eq_add.mp (Eq.symm h)
  rcases exists_max_ideal_of_mem_nonunits key with ⟨I, hI1, hI2⟩
  let p : PrimeSpectrum R := ⟨I, Ideal.IsMaximal.isPrime hI1⟩
  use p
  cases BooleanRing.mem_ideal_or_mem_ideal x p
  case h.inl hx =>
    right
    refine ⟨?_, by tauto⟩
    have key : (1 + (x + y)) + x = 1 + y := by
      calc (1 + (x + y)) + x = 1 + y + (x + x) := by abel
                           _ = 1 + y + 0 := by rw [BooleanRing.add_self]
                           _ = 1 + y := by abel
    rw [mem_stone_map_iff, ← key]
    exact (Submodule.add_mem_iff_right p.asIdeal hI2).mpr hx
  case h.inr hx =>
    left
    refine ⟨(mem_stone_map_iff x p).mpr hx, ?_⟩
    have key : (1 + (x + y)) + (1 + x) = y := by
      calc (1 + (x + y)) + (1 + x) = y + ((1 + x) + (1 + x)) := by abel
                                 _ = y + 0 := by rw [BooleanRing.add_self]
                                 _ = y := by abel
    rw [mem_stone_map_iff', ← key]
    exact (Submodule.add_mem_iff_right p.asIdeal hI2).mpr hx

def stone_hom : S →+* Set (PrimeSpectrum S) where
  toFun := stone_map S
  map_zero' := stone_map_zero
  map_one' := stone_map_one
  map_add' := stone_map_add
  map_mul' := stone_map_mul

/--
Stone's Representation Theorem for Boolean Rings:
For any Boolean ring R, there exists a set X and an injective ring homomorphism
(embedding) from R into the power set of X.
-/
theorem stone_representation_theorem : ∃ (X : Type u) (φ : S →+* Set X), Function.Injective φ := by
  use PrimeSpectrum S
  use stone_hom S
  exact stone_map_injective

def stone_hom' : BoundedLatticeHom A (Set (PrimeSpectrum A)) :=
  BooleanAlgebra.BoundedLatticeHomfromRingHom (stone_hom A)

/--
Stone's Representation Theorem for Boolean Algebras
-/
theorem BooleanAlgebra.stone_representation_theorem :
    ∃ (X : Type u) (φ : BoundedLatticeHom A (Set X)), Function.Injective φ := by
  use PrimeSpectrum A
  use stone_hom' A
  exact stone_map_injective

end StoneRepresentation
