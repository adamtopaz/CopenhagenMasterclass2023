import Mathlib.CategoryTheory.Equivalence
set_option autoImplicit false

open CategoryTheory

universe u v

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]

lemma equiv_reflects_mono {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : Mono (e.functor.map f)) : Mono f := by
  constructor
  intros W φ ψ h
  apply e.functor.map_injective
  apply hef.1
  rw [← Functor.map_comp, ← Functor.map_comp, h]

lemma equiv_preserves_mono {X Y : C} (f : X ⟶ Y) [Mono f] (e : C ≌ D) :
  Mono (e.functor.map f) := by
-- Hint: if `w : f = g`, to obtain `F.map f = F.map G`,
--   you can use `have w' := congr_arg (λ k, F.map k) w`.
  constructor
  intros W φ ψ h
  apply Functor.map_injective e.inverse
  apply Mono.right_cancellation (f := (Equivalence.unitInv e).app X)
  apply Mono.right_cancellation (f := f)
  apply e.functor.map_injective
  simp only [Functor.map_comp]
  simpa
/-!
There are some further hints in
`hints/category_theory/exercise3/`
-/

